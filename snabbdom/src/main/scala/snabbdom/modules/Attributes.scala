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

package snabbdom.modules

import org.scalajs.dom
import snabbdom._

object Attributes {

  val module: Module = Module().copy(
    create = Some(new CreateHook {
      override def apply(vNode: PatchedVNode): Unit = {
        vNode match {
          case elm: PatchedVNode.Element =>
            if (elm.data.attrs.nonEmpty) {
              setAttrs(elm)
            }
          case _ => ()
        }
      }
    }),
    update = Some(new UpdateHook {
      override def apply(
          oldVNode: PatchedVNode,
          vNode: VNode
      ): Unit = {
        (oldVNode, vNode) match {
          case (a: PatchedVNode.Element, b: VNode.Element) =>
            if (a.data.attrs != b.data.attrs) {
              updateAttrs(a, b)
            }
          case _ => ()
        }
      }
    })
  )

  private val htmlNS = "http://www.w3.org/1999/xhtml"
  private val xlinkNS = "http://www.w3.org/1999/xlink"
  private val xmlNS = "http://www.w3.org/XML/1998/namespace"
  private val xmlnsNS = "http://www.w3.org/2000/xmlns/"

  // The namespace a key's prefix names. Every write and removal of the key
  // goes through it, so the key never becomes two attributes.
  private def namespaceOf(key: String): Option[String] =
    if (key.isEmpty || key.charAt(0) != 'x') None
    else if (key.startsWith("xml:")) Some(xmlNS)
    else if (key.startsWith("xmlns:")) Some(xmlnsNS)
    else if (key.startsWith("xlink:")) Some(xlinkNS)
    else None

  // An attribute parsed from HTML markup, such as `xml:lang` on an element
  // hydrated by `toVNode`, has no namespace even with a prefix: its local name
  // is the whole key. `set` and `remove` both remove it with
  // `removeAttributeNS(null, key)`, so the key never ends up as two
  // attributes. `removeAttribute(key)` would find it too, but on an HTML
  // element it lowercases the key, so dropping `xlink:HREF` would also remove
  // `xlink:href`.
  private def set(elm: dom.Element, key: String, value: String): Unit =
    namespaceOf(key) match {
      case None => elm.setAttribute(key, value)
      case Some(ns) =>
        elm.setAttributeNS(ns, key, value)
        elm.removeAttributeNS(null, key)
    }

  private def remove(elm: dom.Element, key: String): Unit =
    namespaceOf(key) match {
      case None => elm.removeAttribute(key)
      case Some(ns) =>
        elm.removeAttributeNS(ns, key.substring(key.indexOf(':') + 1))
        elm.removeAttributeNS(null, key)
    }

  private def write(elm: dom.Element, key: String, attr: AttrValue): Unit =
    attr match {
      case AttrValue.BooleanAttrValue(true)  => set(elm, key, "")
      case AttrValue.BooleanAttrValue(false) => remove(elm, key)
      case AttrValue.StringAttrValue(value)  => set(elm, key, value)
    }

  // On an HTML element the DOM lowercases the names `setAttribute` and
  // `removeAttribute` take, in ASCII only.
  private def asciiLower(s: String): String =
    s.map(c => if (c >= 'A' && c <= 'Z') (c + 32).toChar else c)

  // A key the new vnode drops goes back to what `createElm` leaves: the
  // selector's `id` or classes, if it sets them.
  private def drop(elm: dom.Element, sel: String, key: String): Unit = {
    val name = if (elm.namespaceURI == htmlNS) asciiLower(key) else key
    Selector.attr(sel, name) match {
      case Some(value) => elm.setAttribute(key, value)
      case None        => remove(elm, key)
    }
  }

  private def setAttrs(vnode: PatchedVNode.Element): Unit = {
    val elm = vnode.node
    vnode.data.attrs.foreachEntry((key, attr) => write(elm, key, attr))
  }

  private def updateAttrs(
      oldVnode: PatchedVNode.Element,
      vnode: VNode.Element
  ): Unit = {

    val elm = oldVnode.node
    val oldAttrs = oldVnode.data.attrs
    val attrs = vnode.data.attrs

    // Removals first: an old key respelled in another case names the same
    // DOM attribute as the new spelling, which must be the one left set.
    oldAttrs.foreachEntry { (key, _) =>
      if (!attrs.contains(key)) {
        drop(elm, vnode.sel, key)
      }
    }

    attrs.foreachEntry { (key, cur) =>
      if (oldAttrs.get(key).forall(_ != cur)) {
        write(elm, key, cur)
      }
    }
  }

}
