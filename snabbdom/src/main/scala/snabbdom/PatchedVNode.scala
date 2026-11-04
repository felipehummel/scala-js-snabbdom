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

  // The VNode this node was last created or patched from, as the caller
  // passed it (before init and prepatch hooks). Patching with the very same
  // VNode instance again has nothing to do. Set once by `init`, right after
  // construction, and never visible outside the library.
  private[snabbdom] var source: VNode = null
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

    // The DOM listener for this element's `on` handlers. The EventListeners
    // module hands it from the old node to the new one on every patch, so the
    // element keeps one browser listener per event name.
    private[snabbdom] var listener: Listener = null

    // Immutable, so the conversion is computed at most once.
    private var vnodeCache: VNode = null

    override def toVNode: VNode = {
      if (vnodeCache == null) {
        vnodeCache = VNode.Element(sel, data, children.map(_.toVNode))
      }
      vnodeCache
    }

    // `toVNode` if something already asked for it, otherwise null.
    private[snabbdom] def toVNodeIfComputed: VNode = vnodeCache

  }

  // Dispatches DOM events to the handlers of the element's current vnode.
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
