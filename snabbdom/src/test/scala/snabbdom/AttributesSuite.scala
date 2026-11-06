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

class AttributesSuite extends BaseSuite {

  val vnode0 = FunFixture[dom.Element](
    setup = { _ =>
      dom.document.createElement("div")
    },
    teardown = { _ => () }
  )

  val patch = init(Seq(modules.Attributes.module))

  group("attributes") {

    vnode0.test("have their provided values") { vnode0 =>
      val vnode1 = h(
        "div",
        VNodeData(attrs =
          Map(
            "href" -> "/foo",
            "minlength" -> "1",
            "selected" -> true,
            "disabled" -> false
          )
        )
      )
      val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.Element]
      assertEquals(elm.getAttribute("href"), "/foo")
      assertEquals(elm.getAttribute("minlength"), "1")
      assertEquals(elm.hasAttribute("selected"), true)
      assertEquals(elm.getAttribute("selected"), "")
      assertEquals(elm.hasAttribute("disabled"), false)
    }

    vnode0.test("can be memoized") { vnode0 =>
      val cachedAttrs = VNodeData(
        attrs = Map("href" -> "/foo", "minlength" -> "1", "selected" -> true)
      )
      val vnode1 = h("div", cachedAttrs)
      val vnode2 = h("div", cachedAttrs)
      val vnode1p = patch(vnode0, vnode1)
      val elm1 = vnode1p.node.asInstanceOf[dom.Element]
      assertEquals(elm1.getAttribute("href"), "/foo")
      assertEquals(elm1.getAttribute("minlength"), "1")
      assertEquals(elm1.hasAttribute("selected"), true)

      val elm2 = patch(vnode1p, vnode2).node.asInstanceOf[dom.Element]
      assertEquals(elm2.getAttribute("href"), "/foo")
      assertEquals(elm2.getAttribute("minlength"), "1")
      assertEquals(elm2.hasAttribute("selected"), true)
    }

    vnode0.test("are not omitted when falsy (in JS) values are provided") {
      vnode0 =>
        val vnode1 = h(
          "div",
          VNodeData(attrs =
            Map(
              "href" -> "None",
              "minlength" -> "0",
              "value" -> "",
              "title" -> "undefined"
            )
          )
        )
        val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.Element]
        assertEquals(elm.hasAttribute("href"), true)
        assertEquals(elm.hasAttribute("minlength"), true)
        assertEquals(elm.hasAttribute("value"), true)
        assertEquals(elm.hasAttribute("title"), true)
    }

    vnode0.test("are set correctly when namespaced") { vnode0 =>
      val vnode1 =
        h("div", VNodeData(attrs = Map("xlink:href" -> "#foo")))
      val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.Element]
      assertEquals(
        elm.getAttributeNS("http://www.w3.org/1999/xlink", "href"),
        "#foo"
      )
    }

    test("should not touch class nor id fields") {
      val elm = dom.document.createElement("div").asInstanceOf[dom.HTMLElement]
      elm.id = "myId"
      elm.className = "myClass"
      val vnode0 = elm
      val vnode1 = h(
        "div#myId.myClass",
        VNodeData(),
        List[VNode]("Hello")
      )
      val elm1 = patch(vnode0, vnode1).node.asInstanceOf[dom.HTMLElement]
      assertEquals(elm1.tagName, "DIV")
      assertEquals(elm1.id, "myId")
      assertEquals(elm1.className, "myClass")
      assertEquals(elm1.textContent, "Hello")
    }

  }

  group("patched attributes") {

    // In each test, patching must leave what rendering the new vnode from
    // scratch leaves.

    vnode0.test("fall back to the selector's id when removed") { vnode0 =>
      val vnode1 = h("div#a", VNodeData(attrs = Map("id" -> "z")))
      val vnode1p = patch(vnode0, vnode1)
      val elm = patch(vnode1p, h("div#a")).node.asInstanceOf[dom.Element]
      assertEquals(elm.getAttribute("id"), "a")
    }

    vnode0.test("fall back to the selector's classes when removed") { vnode0 =>
      val vnode1 = h("div.x.y", VNodeData(attrs = Map("CLASS" -> "z")))
      val vnode1p = patch(vnode0, vnode1)
      val elm = patch(vnode1p, h("div.x.y")).node.asInstanceOf[dom.Element]
      assertEquals(elm.getAttribute("class"), "x y")
    }

    vnode0.test("leave a key in another case alone on SVG elements") { vnode0 =>
      val vnode1 = h("svg#a", VNodeData(attrs = Map("ID" -> "z")))
      val vnode1p = patch(vnode0, vnode1)
      val elm = patch(vnode1p, h("svg#a")).node.asInstanceOf[dom.Element]
      assertEquals(elm.getAttribute("id"), "a")
      assertEquals(elm.getAttribute("ID"), null)
      assertEquals(elm.attributes.length, 1)
    }

    vnode0.test("keep a name respelled in another case") { vnode0 =>
      val vnode1 = h("div", VNodeData(attrs = Map("TITLE" -> "x")))
      val vnode1p = patch(vnode0, vnode1)
      val vnode2 = h("div", VNodeData(attrs = Map("title" -> "y")))
      val elm = patch(vnode1p, vnode2).node.asInstanceOf[dom.Element]
      assertEquals(elm.getAttribute("title"), "y")
    }

    vnode0.test("set xmlns-prefixed keys in the XMLNS namespace") { vnode0 =>
      val xlinkNS = "http://www.w3.org/1999/xlink"
      val vnode1 = h("div", VNodeData(attrs = Map("xmlns:xlink" -> xlinkNS)))
      val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.Element]
      assertEquals(
        elm.getAttributeNS("http://www.w3.org/2000/xmlns/", "xlink"),
        xlinkNS
      )
    }

    vnode0.test("stay one attribute when a namespaced key changes type") {
      vnode0 =>
        val vnode1 = h("div", VNodeData(attrs = Map("xlink:href" -> true)))
        val vnode1p = patch(vnode0, vnode1)
        val vnode2 = h("div", VNodeData(attrs = Map("xlink:href" -> "#a")))
        val elm = patch(vnode1p, vnode2).node.asInstanceOf[dom.Element]
        assertEquals(elm.attributes.length, 1)
        assertEquals(
          elm.getAttributeNS("http://www.w3.org/1999/xlink", "href"),
          "#a"
        )
    }

    vnode0.test("remove a namespaced key when dropped or set to false") {
      vnode0 =>
        val vnode1 = h("div", VNodeData(attrs = Map("xlink:href" -> "#a")))
        val vnode1p = patch(vnode0, vnode1)
        assertEquals(
          vnode1p.node.asInstanceOf[dom.Element].attributes.length,
          1
        )
        val dropped = patch(vnode1p, h("div")).node.asInstanceOf[dom.Element]
        assertEquals(dropped.attributes.length, 0)

        val vnode2p = patch(dom.document.createElement("div"), vnode1)
        val vnode3 = h("div", VNodeData(attrs = Map("xlink:href" -> false)))
        val falsed = patch(vnode2p, vnode3).node.asInstanceOf[dom.Element]
        assertEquals(falsed.attributes.length, 0)
    }

    test("remove a hydrated prefixed attribute, which has no namespace") {
      val host = dom.document.createElement("div")
      host.innerHTML = """<div xml:lang="fr" xlink:href="#a"></div>"""
      val elm = host.firstChild.asInstanceOf[dom.Element]
      assertEquals(elm.getAttributeNode("xml:lang").namespaceURI, null)
      val hydrated = toVNode(elm)
      val dropped = patch(hydrated, h("div")).node.asInstanceOf[dom.Element]
      assertEquals(dropped.attributes.length, 0)
    }

    test("replace a hydrated prefixed attribute, which has no namespace") {
      val xmlNS = "http://www.w3.org/XML/1998/namespace"
      val host = dom.document.createElement("div")
      host.innerHTML = """<div xml:lang="fr"></div>"""
      val elm = host.firstChild.asInstanceOf[dom.Element]
      val hydrated = toVNode(elm)
      val vnode = h("div", VNodeData(attrs = Map("xml:lang" -> "en")))
      val changed = patch(hydrated, vnode).node.asInstanceOf[dom.Element]
      assertEquals(changed.attributes.length, 1)
      assertEquals(changed.getAttributeNS(xmlNS, "lang"), "en")
    }

    vnode0.test("drop a namespaced key without its other-case sibling") {
      vnode0 =>
        val both = h(
          "div",
          VNodeData(attrs = Map("xlink:HREF" -> "#a", "xlink:href" -> "#b"))
        )
        val bothP = patch(vnode0, both)
        assertEquals(bothP.node.asInstanceOf[dom.Element].attributes.length, 2)
        val one = h("div", VNodeData(attrs = Map("xlink:href" -> "#b")))
        val elm = patch(bothP, one).node.asInstanceOf[dom.Element]
        assertEquals(elm.attributes.length, 1)
        assertEquals(
          elm.getAttributeNS("http://www.w3.org/1999/xlink", "href"),
          "#b"
        )
    }

  }

  group("boolean attribute") {

    vnode0.test("is present and empty string if the value is thruthy (in JS)") {
      vnode0 =>
        val vnode1 = h(
          "div",
          VNodeData(attrs =
            Map(
              "required" -> true,
              "readonly" -> "1",
              "noresize" -> "truthy"
            )
          )
        )
        val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.HTMLElement]
        assertEquals(elm.hasAttribute("required"), true)
        assertEquals(elm.getAttribute("required"), "")
        assertEquals(elm.hasAttribute("readonly"), true)
        assertEquals(elm.getAttribute("readonly"), "1")
        assertEquals(elm.hasAttribute("noresize"), true)
        assertEquals(elm.getAttribute("noresize"), "truthy")
    }

    vnode0.test("is omitted if the value is false") { vnode0 =>
      val vnode1 = h("div", VNodeData(attrs = Map("required" -> false)))
      val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.HTMLElement]
      assertEquals(elm.hasAttribute("required"), false)
      assertEquals(elm.getAttribute("required"), null)
    }

    vnode0.test("is not omitted if the value is falsy") { vnode0 =>
      val vnode1 =
        h(
          "div",
          VNodeData(attrs = Map("readonly" -> "0", "noresize" -> ""))
        )
      val elm = patch(vnode0, vnode1).node.asInstanceOf[dom.HTMLElement]
      assertEquals(elm.hasAttribute("readonly"), true)
      assertEquals(elm.hasAttribute("noresize"), true)
    }

  }

  group("Object.prototype property") {

    // not sure I understand this test
    vnode0.test(
      "is not considered as a boolean attribute and shouldn't be omitted"
    ) { vnode0 =>
      val vnode1 = h("div", VNodeData(attrs = Map("constructor" -> true)))
      val vnode1p = patch(vnode0, vnode1)
      val elm1 = vnode1p.node.asInstanceOf[dom.Element]
      assertEquals(elm1.hasAttribute("constructor"), true)
      assertEquals(elm1.getAttribute("constructor"), "")
      val vnode2 =
        h("div", VNodeData(attrs = Map("constructor" -> false)))
      val elm2 = patch(vnode1p, vnode2).node.asInstanceOf[dom.Element]
      assertEquals(elm2.hasAttribute("constructor"), false)

    }

  }

}
