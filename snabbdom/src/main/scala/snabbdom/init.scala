/*
 * Copyright 2022 buntec
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Copyright (c) 2015 Simon Friis Vindum
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

package snabbdom

import org.scalajs.dom
import snabbdom.modules._

import scala.collection.mutable

object init {

  def apply: Patch = {
    apply(
      Seq(
        Attributes.module,
        Classes.module,
        Props.module,
        Styles.module,
        EventListeners.module,
        Dataset.module
      )
    )
  }

  def apply(
      modules: Seq[Module],
      domApi: Option[DomApi] = None
  ): Patch = {

    type VNodeQueue = mutable.ArrayBuffer[PatchedVNode]

    val api = domApi.getOrElse(DomApi.apply)

    val cbs: ModuleHooks = modules.foldLeft(ModuleHooks.empty) {
      case (hooks, module) =>
        hooks.copy(
          create = module.create.fold(hooks.create)(_ :: hooks.create),
          update = module.update.fold(hooks.update)(_ :: hooks.update),
          postPatch =
            module.postPatch.fold(hooks.postPatch)(_ :: hooks.postPatch),
          remove = module.remove.fold(hooks.remove)(_ :: hooks.remove),
          destroy = module.destroy.fold(hooks.destroy)(_ :: hooks.destroy),
          pre = module.pre.fold(hooks.pre)(_ :: hooks.pre),
          post = module.post.fold(hooks.post)(_ :: hooks.post)
        )
    }

    def emptyNodeAt(elm: dom.Element): PatchedVNode = {
      val id = Option(elm.id).filter(_.nonEmpty).fold("")("#" + _)
      val classes = Option(elm.getAttribute("class"))
      val c = classes.map("." + _.split(" ").mkString(".")).getOrElse("")

      PatchedVNode.Element(
        api.tagName(elm).toLowerCase + id + c,
        VNodeData.empty,
        Nil,
        elm
      )

    }

    def createRmCb(childElm: dom.Node, listeners: Int): () => Unit = {
      var listeners0 = listeners
      () => {
        listeners0 -= 1
        if (listeners0 == 0) {
          val parent = api.parentNode(childElm)
          parent.foreach(parent => api.removeChild(parent, childElm))
        }
      }
    }

    def createElm(
        vnode00: VNode,
        insertedVNodeQueue: VNodeQueue
    ): PatchedVNode = {

      val vnode0 = VNode.applyInitHook(vnode00)

      val pvnode = vnode0 match {
        case VNode.Comment(content) =>
          val node = api.createComment(content)
          PatchedVNode.comment(content, node)

        case VNode.Text(text) =>
          PatchedVNode.Text(
            text,
            api.createTextNode(text)
          )

        case VNode.Element(sel, data, children) =>
          val hashIdx = sel.indexOf("#")
          val dotIdx = sel.indexOf(".", hashIdx)
          val hash = if (hashIdx > 0) hashIdx else sel.length
          val dot = if (dotIdx > 0) dotIdx else sel.length
          val tag = if (hashIdx != -1 || dotIdx != -1) {
            sel.substring(0, math.min(hash, dot))
          } else {
            sel
          }
          val elm = data.ns match {
            case Some(ns) =>
              api.createElementNS(ns, tag) // TODO what about data?
            case None =>
              api.createElement(tag) // TODO what about data argument?
          }
          val pvnode0 = PatchedVNode.Element(
            sel,
            data,
            children = children.map(createElm(_, insertedVNodeQueue)),
            node = elm
          )
          if (hash < dot) elm.setAttribute("id", sel.substring(hash + 1, dot))
          if (dotIdx > 0) {
            val classes = sel.substring(dot + 1)
            elm.setAttribute(
              "class",
              if (classes.indexOf('.') < 0) classes
              else classes.replace('.', ' ')
            )
          }

          var createHooks = cbs.create
          while (createHooks.nonEmpty) {
            createHooks.head(pvnode0)
            createHooks = createHooks.tail
          }

          // insert children into dom
          var patchedChildren = pvnode0.children
          while (patchedChildren.nonEmpty) {
            api.appendChild(elm, patchedChildren.head.node)
            patchedChildren = patchedChildren.tail
          }

          data.hook match {
            case Some(hooks) =>
              hooks.create.foreach(hook => hook(pvnode0))
              if (hooks.insert.isDefined) insertedVNodeQueue.append(pvnode0)
            case None => ()
          }

          pvnode0

      }
      pvnode.source = vnode00
      pvnode

    }

    def invokeDestroyHook(vnode: PatchedVNode): Unit = {
      vnode match {
        case PatchedVNode.Element(_, data, children, _) =>
          data.hook match {
            case Some(hooks) => hooks.destroy.foreach(_(vnode))
            case None        => ()
          }
          var destroyHooks = cbs.destroy
          while (destroyHooks.nonEmpty) {
            destroyHooks.head(vnode)
            destroyHooks = destroyHooks.tail
          }
          var rest = children
          while (rest.nonEmpty) {
            invokeDestroyHook(rest.head)
            rest = rest.tail
          }
        case _ => ()
      }
    }

    def hasRemoveHook(vnode: PatchedVNode): Boolean = vnode match {
      case PatchedVNode.Element(_, data, _, _) =>
        data.hook.exists(_.remove.isDefined)
      case _ => false
    }

    def removeAllVnodes(
        parentElm: dom.Node,
        vnodes: List[PatchedVNode]
    ): Unit = {
      var rest = vnodes
      while (rest.nonEmpty) {
        rest.head match {
          case child @ PatchedVNode.Element(_, data, _, elm) =>
            invokeDestroyHook(child)
            if (cbs.remove.isEmpty && !hasRemoveHook(child)) {
              api.parentNode(elm).foreach(api.removeChild(_, elm))
            } else {
              val listeners = cbs.remove.length + 1
              val rm = createRmCb(elm, listeners)
              cbs.remove.foreach(_(child, rm))
              data.hook.flatMap(_.remove).fold(rm()) { hook =>
                hook(child, rm); ()
              }
            }
          case other =>
            api.removeChild(parentElm, other.node)
        }
        rest = rest.tail
      }
    }

    // Removes every child of `parentElm` at once when nothing can delay a
    // removal and the element holds exactly `vnodes`. Returns false, having
    // done nothing, when that does not hold.
    def removeAllChildrenAtOnce(
        parentElm: dom.Node,
        vnodes: List[PatchedVNode],
        count: Int
    ): Boolean = {
      val possible =
        cbs.remove.isEmpty &&
          parentElm.childNodes.length == count &&
          !vnodes.exists(hasRemoveHook)
      if (possible) {
        var rest = vnodes
        while (rest.nonEmpty) {
          invokeDestroyHook(rest.head)
          rest = rest.tail
        }
        api.setTextContent(parentElm, Some(""))
      }
      possible
    }

    def updateChildren(
        parentElm: dom.Node,
        oldCh: List[PatchedVNode],
        newCh: List[VNode],
        insertedVnodeQueue: VNodeQueue
    ): List[PatchedVNode] = {

      // Scratch space local to this call. An unkeyed child matches the old
      // child at its position and stays where it is (anchored). A keyed child
      // matches the first unclaimed old child with its key and may move.
      val oldLen = oldCh.length
      val newLen = newCh.length
      val olds = new Array[PatchedVNode](oldLen)
      val news = new Array[VNode](newLen)
      var fillOld = oldCh
      var i = 0
      while (i < oldLen) {
        olds(i) = fillOld.head
        fillOld = fillOld.tail
        i += 1
      }
      var fillNew = newCh
      i = 0
      while (i < newLen) {
        news(i) = fillNew.head
        fillNew = fillNew.tail
        i += 1
      }
      val claimed = new Array[Boolean](oldLen)
      val children = new Array[PatchedVNode](newLen)
      val movable = new Array[Boolean](newLen)

      // Common prefix: every child before `start` matched the old child at
      // its own position, which is what both rules choose there.
      val common = math.min(oldLen, newLen)
      var start = 0
      while (start < common && sameVnode(olds(start), news(start))) {
        children(start) =
          patchVnode(olds(start), news(start), insertedVnodeQueue)
        claimed(start) = true
        movable(start) = isKeyed(news(start))
        start += 1
      }

      if (start == oldLen) {
        // Every old child matched in place, so no key or position can match
        // the remaining new children: they are created and appended.
        var j = start
        while (j < newLen) {
          children(j) = createElm(news(j), insertedVnodeQueue)
          j += 1
        }
        j = start
        while (j < newLen) {
          api.appendChild(parentElm, children(j).node)
          j += 1
        }
        return toList(children)
      }

      if (start == newLen) {
        // Every new child matched in place: the remaining old ones go.
        var removed = List.empty[PatchedVNode]
        var k = oldLen - 1
        while (k >= start) {
          removed = olds(k) :: removed
          k -= 1
        }
        removeAllVnodes(parentElm, removed)
        return toList(children)
      }

      // Unclaimed old children by key, in order: `firstWithKey` holds the
      // first index for each key and `nextWithKey` chains the rest.
      var firstWithKey: JSMap[String, Int] = null
      var nextWithKey: Array[Int] = null
      def indexKeys(): Unit = {
        firstWithKey = new JSMap[String, Int]()
        nextWithKey = new Array[Int](oldLen)
        var k = oldLen - 1
        while (k >= start) {
          olds(k) match {
            case PatchedVNode.Element(_, data, _, _) if data.key.isDefined =>
              val key = data.key.get
              nextWithKey(k) = firstWithKey.get(key).getOrElse(-1)
              firstWithKey.set(key, k)
            case _ => ()
          }
          k -= 1
        }
      }

      // Old index of each new child, -1 when it was created.
      val oldIndex = new Array[Int](newLen)
      var k = 0
      while (k < start) {
        oldIndex(k) = k
        k += 1
      }
      var anchoredAfterStart = false
      var claimedCount = start

      var j = start
      while (j < newLen) {
        val vnode = news(j)
        var matched = -1
        vnode match {
          case VNode.Element(_, data, _) if data.key.isDefined =>
            if (firstWithKey == null) indexKeys()
            var candidate = firstWithKey.get(data.key.get).getOrElse(-1)
            while (candidate >= 0 && matched < 0) {
              if (!claimed(candidate) && sameVnode(olds(candidate), vnode)) {
                matched = candidate
              } else candidate = nextWithKey(candidate)
            }
            movable(j) = true
          case _ =>
            if (j < oldLen && !claimed(j) && sameVnode(olds(j), vnode)) {
              matched = j
            }
        }
        oldIndex(j) = matched
        if (matched >= 0) {
          claimed(matched) = true
          claimedCount += 1
          children(j) = patchVnode(olds(matched), vnode, insertedVnodeQueue)
          if (!movable(j)) anchoredAfterStart = true
        } else {
          children(j) = createElm(vnode, insertedVnodeQueue)
          movable(j) = true
        }
        j += 1
      }

      // Every old child goes: clear them in one step before placing the new
      // ones, when nothing can delay their removal.
      val oldRemoved =
        claimedCount == 0 && removeAllChildrenAtOnce(parentElm, oldCh, oldLen)

      if (anchoredAfterStart)
        placeAroundAnchors(parentElm, olds, children, movable)
      else placeWithFewestMoves(parentElm, children, oldIndex)

      if (!oldRemoved && claimedCount < oldLen) {
        var removed = List.empty[PatchedVNode]
        k = oldLen - 1
        while (k >= 0) {
          if (!claimed(k)) removed = olds(k) :: removed
          k -= 1
        }
        removeAllVnodes(parentElm, removed)
      }

      toList(children)

    }

    // Orders a child list in which every matched child may move (keyed) and
    // every other child was just created. Children whose old positions form
    // the longest increasing run stay put; the rest are inserted before their
    // next sibling, from last to first.
    def placeWithFewestMoves(
        parentElm: dom.Node,
        children: Array[PatchedVNode],
        oldIndex: Array[Int]
    ): Unit = {
      val stays = longestIncreasingRun(oldIndex)
      // Walks back over runs of children that must be inserted, and inserts
      // each run in document order before the child that follows it.
      var next: Option[dom.Node] = None
      var end = children.length - 1
      while (end >= 0) {
        if (stays(end)) {
          next = Some(children(end).node)
          end -= 1
        } else {
          var first = end
          while (first > 0 && !stays(first - 1)) first -= 1
          var k = first
          while (k <= end) {
            api.insertBefore(parentElm, children(k).node, next)
            k += 1
          }
          next = Some(children(first).node)
          end = first - 1
        }
      }
    }

    // Orders a child list that holds anchored (unkeyed) children, which never
    // move. Walks forward and inserts each movable child before the next new
    // child in the DOM, skipping old children that are being removed.
    def placeAroundAnchors(
        parentElm: dom.Node,
        olds: Array[PatchedVNode],
        children: Array[PatchedVNode],
        movable: Array[Boolean]
    ): Unit = {
      val reconciled = new JSSet[dom.Node]()
      var k = 0
      while (k < children.length) {
        reconciled.add(children(k).node)
        k += 1
      }
      def nextReconciled(from: dom.Node): dom.Node = {
        var node = from
        while (node != null && !reconciled.has(node)) {
          node = api.nextSibling(node).orNull
        }
        node
      }
      var cursor: dom.Node = if (olds.nonEmpty) olds(0).node else null
      k = 0
      while (k < children.length) {
        val node = children(k).node
        if (movable(k)) {
          val reference = nextReconciled(cursor)
          if (reference eq node) {
            cursor = api.nextSibling(node).orNull
          } else {
            api.insertBefore(parentElm, node, Option(reference))
            cursor = reference
          }
        } else {
          cursor = api.nextSibling(node).orNull
        }
        k += 1
      }
    }

    def patchVnode(
        oldVnode: PatchedVNode,
        vnode00: VNode,
        insertedVNodeQueue: VNodeQueue
    ): PatchedVNode = {

      // apply prepatch hooks
      val vnode = vnode00 match {
        case VNode.Element(_, data, _) =>
          data.hook
            .flatMap(_.prepatch)
            .fold(vnode00)(hook => hook(oldVnode, vnode00))
        case _ => vnode00
      }

      // Nothing to do when the caller passed the very VNode instance this node
      // came from, or a prepatch hook (a thunk) answered with the old node's
      // own VNode.
      val unchanged = (vnode eq oldVnode.source) || (
        (vnode ne vnode00) && (oldVnode match {
          case old: PatchedVNode.Element => vnode eq old.toVNodeIfComputed
          case _                         => false
        })
      )
      if (unchanged) {

        oldVnode

      } else {

        // apply update hooks
        cbs.update.foreach { hook => hook(oldVnode, vnode) }
        vnode match {
          case VNode.Element(_, data, _) =>
            data.hook.flatMap(_.update).foreach(hook => hook(oldVnode, vnode))
          case _ => ()
        }

        val patchedVNode = (oldVnode, vnode) match {

          case (
                PatchedVNode.Comment(oldContent, node),
                VNode.Comment(content)
              ) =>
            if (oldContent != content) {
              api.setTextContent(node, Some(content))
            }
            PatchedVNode.Comment(content, node)

          case (PatchedVNode.Text(oldContent, node), VNode.Text(content)) =>
            if (oldContent != content) {
              api.setTextContent(node, Some(content))
            }
            PatchedVNode.Text(
              content,
              node
            )

          case (
                PatchedVNode.Element(_, _, oldCh, elm),
                VNode.Element(sel, data, ch)
              ) =>
            (oldCh, ch) match {
              case (oldCh @ _ :: _, ch @ _ :: _) =>
                PatchedVNode.element(
                  sel,
                  data,
                  updateChildren(elm, oldCh, ch, insertedVNodeQueue),
                  elm
                )

              case (Nil, ch @ _ :: _) =>
                val patchedChildren = ch.map { vnode =>
                  val pvnode = createElm(vnode, insertedVNodeQueue)
                  api.insertBefore(
                    elm,
                    pvnode.node,
                    None
                  )
                  pvnode
                }
                PatchedVNode.Element(
                  sel,
                  data,
                  patchedChildren,
                  elm
                )

              case (oldCh @ _ :: _, Nil) =>
                if (!removeAllChildrenAtOnce(elm, oldCh, oldCh.length)) {
                  removeAllVnodes(elm, oldCh)
                }
                PatchedVNode.Element(
                  sel,
                  data,
                  Nil,
                  elm
                )
              case (Nil, Nil) =>
                PatchedVNode.Element(
                  sel,
                  data,
                  Nil,
                  elm
                )

            }

          case _ =>
            throw new AssertionError("trying to patch incompatible nodes")

        }

        // apply post patch hooks
        cbs.postPatch.foreach(hook => hook(oldVnode, patchedVNode))
        patchedVNode match {
          case PatchedVNode.Element(_, data, _, _) =>
            data.hook
              .flatMap(_.postpatch)
              .foreach(hook => hook(oldVnode, patchedVNode))
          case _ => ()
        }

        patchedVNode.source = vnode00
        patchedVNode

      }

    }

    def patch(oldVnode: PatchedVNode, vnode: VNode): PatchedVNode = {

      val insertedVNodeQueue: VNodeQueue =
        mutable.ArrayBuffer.empty[PatchedVNode]

      cbs.pre.foreach(_())

      val vnode0 = if (sameVnode(oldVnode, vnode)) {
        patchVnode(oldVnode, vnode, insertedVNodeQueue)
      } else {
        val elm = oldVnode.node
        val parent = api.parentNode(elm)
        val vnode1 = createElm(vnode, insertedVNodeQueue)
        parent match {
          case Some(parent) =>
            api.insertBefore(parent, vnode1.node, api.nextSibling(elm))
            removeAllVnodes(parent, List(oldVnode))
          case None => ()
        }
        vnode1
      }

      insertedVNodeQueue.foreach {
        case vnode @ PatchedVNode.Element(_, data, _, _) =>
          data.hook.flatMap(_.insert).foreach(_(vnode))
        case _ => ()
      }

      cbs.post.foreach(_())

      vnode0

    }

    new Patch {

      override def apply(oldVnode: PatchedVNode, vnode: VNode): PatchedVNode =
        patch(oldVnode, vnode)

      override def apply(elm: dom.Element, vnode: VNode): PatchedVNode =
        patch(emptyNodeAt(elm), vnode)

    }

  }

  private def sameVnode(vnode1: PatchedVNode, vnode2: VNode): Boolean = {
    (vnode1, vnode2) match {
      case (_: PatchedVNode.Text, _: VNode.Text) => true
      case (
            PatchedVNode.Element(sel1, data1, _, _),
            VNode.Element(sel2, data2, _)
          ) =>
        sel1 == sel2 && data1.key == data2.key && data1.is == data2.is
      case _ => false
    }
  }

  // Marks one longest strictly increasing subsequence of the non-negative
  // entries of `seq` (negative entries never belong to it). O(n log n).
  private def longestIncreasingRun(seq: Array[Int]): Array[Boolean] = {
    val n = seq.length
    val inRun = new Array[Boolean](n)
    // tails(l): index of the smallest last element of a run of length l + 1
    val tails = new Array[Int](n)
    val previous = new Array[Int](n)
    var length = 0
    var i = 0
    while (i < n) {
      val value = seq(i)
      if (value >= 0) {
        var lo = 0
        var hi = length
        while (lo < hi) {
          val mid = (lo + hi) >>> 1
          if (seq(tails(mid)) < value) lo = mid + 1 else hi = mid
        }
        previous(i) = if (lo > 0) tails(lo - 1) else -1
        tails(lo) = i
        if (lo == length) length += 1
      }
      i += 1
    }
    var k = if (length > 0) tails(length - 1) else -1
    while (k >= 0) {
      inRun(k) = true
      k = previous(k)
    }
    inRun
  }

  private def toList(children: Array[PatchedVNode]): List[PatchedVNode] = {
    var list = List.empty[PatchedVNode]
    var k = children.length - 1
    while (k >= 0) {
      list = children(k) :: list
      k -= 1
    }
    list
  }

  private def isKeyed(vnode: VNode): Boolean = vnode match {
    case VNode.Element(_, data, _) => data.key.isDefined
    case _                         => false
  }

}
