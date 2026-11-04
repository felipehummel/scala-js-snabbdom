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

import snabbdom.modules._

import org.scalajs.dom
import scala.collection.mutable.ListBuffer

class EventListenersSuite extends BaseSuite {

  val vnode0 = FunFixture[dom.Element](
    setup = { _ =>
      dom.document.createElement("div")
    },
    teardown = { _ => () }
  )

  val patch = init(
    Seq(
      EventListeners.module
    )
  )

  vnode0.test("attaches click event handler to element") { vnode0 =>
    val result = List.newBuilder[dom.Event]
    val clicked = EventHandler((ev: dom.Event) => result += ev)
    val vnode = h(
      "div",
      VNodeData(on = Map("click" -> clicked)),
      List(h("a", "Click my parent"))
    )
    val elm = patch(vnode0, vnode).node
    elm.asInstanceOf[dom.HTMLElement].click()
    assertEquals(result.result().length, 1)
  }

  // wouldn't a better name be "detaches old listener when element is the same"
  vnode0.test("does not attach new listener") { vnode0 =>
    val result = List.newBuilder[Int]
    val vnode1 = h(
      "div",
      VNodeData(on =
        Map("click" -> EventHandler((_: dom.Event) => result += 1))
      ),
      List(h("a", "Click my parent"))
    )
    val vnode2 = h(
      "div",
      VNodeData(on = Map("click" -> EventHandler(_ => result += 2))),
      List(h("a", "Click my parent"))
    )
    val vnode1p = patch(vnode0, vnode1)
    val elm1 = vnode1p.node.asInstanceOf[dom.HTMLElement]
    elm1.click()
    val elm2 = patch(vnode1p, vnode2).node.asInstanceOf[dom.HTMLElement]
    elm2.click()
    val result0 = result.result()
    assertEquals(result0, List(1, 2))
  }

  vnode0.test("detach attached click event handler to element") { vnode0 =>
    val result = ListBuffer[dom.Event]()
    val clicked = (ev: dom.Event) => {
      result += ev
      ()
    }
    val vnode1 = h(
      "div",
      VNodeData(on = Map("click" -> clicked)),
      List(h("a", "Click my parent"))
    )
    val vnode1p = patch(vnode0, vnode1)
    val elm1 = vnode1p.node.asInstanceOf[dom.HTMLElement]
    elm1.click()
    assertEquals(result.length, 1)
    val vnode2 = h("div", VNodeData(), List(h("a", "Click my parent")))
    val elm2 = patch(vnode1p, vnode2).node.asInstanceOf[dom.HTMLElement]
    elm2.click()
    assertEquals(result.length, 1)
  }

  vnode0.test("multiple event handlers for same event on same element") {
    vnode0 =>
      var called = 0
      val clicked = (ev: dom.Event, vnode: VNode) => {
        called += 1
        assert(ev.target != null)
        val div = vnode.asInstanceOf[VNode.Element]
        assertEquals(div.sel, "div")
      }

      val vnode1 = h(
        "div",
        VNodeData(on =
          Map("click" -> EventHandler.usingVNode(clicked, clicked, clicked))
        ),
        List(h("a", "Click my parent"))
      )
      val vnode1p = patch(vnode0, vnode1)
      val elm1 = vnode1p.node.asInstanceOf[dom.HTMLElement]
      elm1.click()
      assertEquals(called, 3)
      val vnode2 = h(
        "div",
        VNodeData(on =
          Map("click" -> EventHandler.usingVNode(clicked, clicked))
        ),
        List(h("a", "Click my parent"))
      )
      val elm2 = patch(vnode1p, vnode2).node.asInstanceOf[dom.HTMLElement]
      elm2.click()
      assertEquals(called, 5)
  }

  vnode0.test("access to virtual node in event handler") { vnode0 =>
    val result = ListBuffer[VNode]()
    val clicked = (_: dom.Event, vnode: VNode) => {
      result += vnode
      ()
    }
    val vnode1 = h(
      "div",
      VNodeData(on = Map("click" -> clicked)),
      List(h("a", "Click my parent"))
    )
    val vnode1p = patch(vnode0, vnode1)
    val elm1 = vnode1p.node.asInstanceOf[dom.HTMLElement]
    elm1.click()
    assertEquals(result.length, 1)
    assertEquals(result(0), vnode1p.toVNode)
  }

  vnode0.test("shared handlers in parent and child nodes") { vnode0 =>
    val result = ListBuffer[dom.Event]()
    val clicked = (ev: dom.Event) => {
      result += ev
      ()
    }
    val vnode1 = h(
      "div",
      VNodeData(on = Map("click" -> clicked)),
      List(
        h(
          "a",
          VNodeData(on = Map("click" -> clicked)),
          "Click my parent"
        )
      )
    )
    val elm1 = patch(vnode0, vnode1).node.asInstanceOf[dom.HTMLDivElement]
    elm1.click()
    assertEquals(result.length, 1)
    elm1.firstChild.asInstanceOf[dom.HTMLElement].click()
    assertEquals(result.length, 3)
  }

  def record(result: ListBuffer[Int], value: Int): EventHandler =
    EventHandler((_: dom.Event) => { result += value; () })

  def listening(on: (String, EventHandler)*): VNode =
    h("div", VNodeData(on = on.toMap), "Hover or click me")

  def mouseover(elm: dom.Element): Unit =
    elm.dispatchEvent(new dom.Event("mouseover"))

  vnode0.test("listens again after every handler was removed") { vnode0 =>
    val result = ListBuffer[Int]()
    val vnode1p = patch(vnode0, listening("click" -> record(result, 1)))
    val elm = vnode1p.node.asInstanceOf[dom.HTMLElement]
    elm.click()
    val vnode2p = patch(vnode1p, listening())
    elm.click()
    patch(vnode2p, listening("click" -> record(result, 3)))
    elm.click()
    assertEquals(result.toList, List(1, 3))
  }

  vnode0.test("adds a listener for a new event name") { vnode0 =>
    val result = ListBuffer[Int]()
    val vnode1p = patch(vnode0, listening("click" -> record(result, 1)))
    val elm = vnode1p.node.asInstanceOf[dom.HTMLElement]
    patch(
      vnode1p,
      listening("click" -> record(result, 2), "mouseover" -> record(result, 3))
    )
    elm.click()
    mouseover(elm)
    assertEquals(result.toList, List(2, 3))
  }

  vnode0.test("removes the listener for a dropped event name") { vnode0 =>
    val result = ListBuffer[Int]()
    val vnode1p = patch(
      vnode0,
      listening("click" -> record(result, 1), "mouseover" -> record(result, 2))
    )
    val elm = vnode1p.node.asInstanceOf[dom.HTMLElement]
    patch(vnode1p, listening("mouseover" -> record(result, 3)))
    elm.click()
    mouseover(elm)
    assertEquals(result.toList, List(3))
  }

  vnode0.test("calls a handler once when the module is registered twice") {
    vnode0 =>
      val patchTwice = init(Seq(EventListeners.module, EventListeners.module))
      val result = ListBuffer[Int]()
      val vnode1p = patchTwice(vnode0, listening("click" -> record(result, 1)))
      val elm = vnode1p.node.asInstanceOf[dom.HTMLElement]
      elm.click()
      assertEquals(result.toList, List(1))
      patchTwice(vnode1p, listening())
      elm.click()
      assertEquals(result.toList, List(1))
  }

}
