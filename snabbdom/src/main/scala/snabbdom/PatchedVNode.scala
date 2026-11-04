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

package snabbdom

import org.scalajs.dom
import scalajs.js

/** A `VNode` that has been patched into the DOM. */
sealed trait PatchedVNode {
  def node: dom.Node // the corresponding node in the DOM
  def toVNode: VNode
}

object PatchedVNode {

  def key(vnode: PatchedVNode): Option[String] = vnode match {
    case Element(_, data, _, _) => data.key
    case _                      => None
  }

  final case class Element(
      sel: String,
      data: VNodeData,
      children: List[PatchedVNode],
      node: dom.Element
  ) extends PatchedVNode {

    private[snabbdom] def handleEvent(event: dom.Event): Unit = {
      val name = event.`type`
      data.on.get(name).foreach { handler =>
        handler.cbs.foreach(_(event, this.toVNode))
      }
    }

    // Handed from each patched version of an element to the next while `on`
    // stays non-empty, so a patch adds or removes only the event names that
    // changed.
    private[snabbdom] var listener: Listener = null

    // When non-null, equal to the conversion `toVNode` would build.
    private[PatchedVNode] var vnodeCache: VNode = null

    override def toVNode: VNode = {
      if (vnodeCache == null) {
        vnodeCache = VNode.Element(sel, data, children.map(_.toVNode))
      }
      vnodeCache
    }

    // Lets `toVNode` answer with `vnode`, the value this node was built from,
    // when the children prove it equal to the conversion.
    private[snabbdom] def builtFrom(vnode: VNode.Element): this.type = {
      if (childrenMatch(children, vnode.children)) vnodeCache = vnode
      this
    }

  }

  /** `vnode == patched.toVNode`, decided without building the conversion. */
  private[snabbdom] def matches(patched: PatchedVNode, vnode: VNode): Boolean =
    (patched, vnode) match {
      case (e: Element, v: VNode.Element) =>
        val cached = e.vnodeCache
        if (cached != null) v == cached
        else
          e.sel == v.sel && e.data == v.data &&
          childrenMatch(e.children, v.children)
      case (Text(content, _), VNode.Text(other))       => content == other
      case (Comment(content, _), VNode.Comment(other)) => content == other
      case _                                           => false
    }

  private[snabbdom] def childrenMatch(
      patched: List[PatchedVNode],
      vnodes: List[VNode]
  ): Boolean = {
    var ps = patched
    var vs = vnodes
    while (ps.nonEmpty && vs.nonEmpty && matches(ps.head, vs.head)) {
      ps = ps.tail
      vs = vs.tail
    }
    ps.isEmpty && vs.isEmpty
  }

  private[snabbdom] final class Listener(var vnode: Element) {
    val fn: js.Function1[dom.Event, Unit] =
      (event: dom.Event) => vnode.handleEvent(event)
  }

  def element(
      sel: String,
      data: VNodeData,
      children: List[PatchedVNode],
      node: dom.Element
  ): PatchedVNode =
    Element(
      sel,
      data,
      children,
      node
    )

  final case class Text(
      content: String,
      node: dom.Text
  ) extends PatchedVNode {

    override def toVNode: VNode = VNode.Text(content)

  }

  def text(content: String, node: dom.Text): PatchedVNode = Text(content, node)

  final case class Comment(content: String, node: dom.Comment)
      extends PatchedVNode {

    override def toVNode: VNode = VNode.comment(content)

  }

  def comment(content: String, node: dom.Comment): PatchedVNode =
    PatchedVNode.Comment(content, node)

}
