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
import snabbdom.modules._

import scala.scalajs.js

class ConnectionCounter extends dom.HTMLElement {
  var connects: Int = 0
  var disconnects: Int = 0
  def connectedCallback(): Unit = connects += 1
  def disconnectedCallback(): Unit = disconnects += 1
}

class ChildReconciliationSuite extends BaseSuite {

  val counterTag = "connection-counter"
  dom.window.customElements.define(
    counterTag,
    js.constructorOf[ConnectionCounter]
  )

  val patch = init(
    Seq(
      Classes.module,
      Props.module,
      EventListeners.module,
      Styles.module
    )
  )

  // Custom elements only receive connection callbacks inside the document.
  val mounted = FunFixture[dom.Element](
    setup = { _ =>
      val elm = dom.document.createElement("div")
      dom.document.body.appendChild(elm)
      elm
    },
    teardown = { elm => elm.remove() }
  )

  def counterIn(elm: dom.Element): ConnectionCounter =
    elm.querySelector(counterTag).asInstanceOf[ConnectionCounter]

  def card(sel: String, title: String): VNode =
    h(sel, List(h("h3", title), h(counterTag)))

  def keyedCard(key: String): VNode =
    h("div", VNodeData(key = Some(key)), List(h("h3", key), h(counterTag)))

  def childElements(root: PatchedVNode): List[dom.Element] =
    root.node.asInstanceOf[dom.Element].children.toList

  def assertConnectedOnce(counter: ConnectionCounter): Unit = {
    assertEquals(counter.connects, 1)
    assertEquals(counter.disconnects, 0)
  }

  mounted.test(
    "keeps a custom element when an earlier sibling changes tag (FEL-434)"
  ) { elm =>
    val before = patch(
      elm,
      h(
        "div",
        List(
          h("div", List(h("button", "Team A"), h("button", "Team B"))),
          card("div", "Documents"),
          h("div", "history")
        )
      )
    )
    val cardBefore = childElements(before)(1)
    val counterBefore = counterIn(cardBefore)

    val after = patch(
      before,
      h(
        "div",
        List(
          h("p", "Team: A"),
          card("div", "Documents"),
          h("div", "history")
        )
      )
    )

    val children = childElements(after)
    assertEquals(children.map(_.tagName), List("P", "DIV", "DIV"))
    assertEquals(
      children.map(_.textContent),
      List("Team: A", "Documents", "history")
    )
    assert(children(1) eq cardBefore)
    assert(counterIn(children(1)) eq counterBefore)
    assertConnectedOnce(counterBefore)
  }

  List(0, 1, 2).foreach { swapped =>
    mounted.test(
      s"replaces only the unkeyed child whose tag changes at $swapped"
    ) { elm =>
      val titles = List("a", "b", "c")
      val before = patch(elm, h("div", titles.map(card("div", _))))
      val elementsBefore = childElements(before)
      val countersBefore = elementsBefore.map(counterIn)

      val after = patch(
        before,
        h(
          "div",
          titles.zipWithIndex.map { case (title, i) =>
            card(if (i == swapped) "section" else "div", title)
          }
        )
      )

      val children = childElements(after)
      assertEquals(children.map(_.textContent), titles)
      assertEquals(children(swapped).tagName, "SECTION")
      assertEquals(countersBefore(swapped).disconnects, 1)
      assertConnectedOnce(counterIn(children(swapped)))
      (0 until 3).filter(_ != swapped).foreach { i =>
        assert(children(i) eq elementsBefore(i))
        assertConnectedOnce(countersBefore(i))
      }
    }
  }

  mounted.test("appends and removes unkeyed children at the end in place") {
    elm =>
      val before = patch(elm, h("div", List("a", "b").map(card("div", _))))
      val elementsBefore = childElements(before)

      val grown =
        patch(before, h("div", List("a", "b", "c", "d").map(card("div", _))))
      val grownChildren = childElements(grown)
      assertEquals(grownChildren.map(_.textContent), List("a", "b", "c", "d"))
      assert(grownChildren(0) eq elementsBefore(0))
      assert(grownChildren(1) eq elementsBefore(1))

      val shrunk = patch(grown, h("div", List("a", "b").map(card("div", _))))
      val shrunkChildren = childElements(shrunk)
      assertEquals(shrunkChildren.map(_.textContent), List("a", "b"))
      assert(shrunkChildren(0) eq elementsBefore(0))
      assert(shrunkChildren(1) eq elementsBefore(1))
      elementsBefore.map(counterIn).foreach(assertConnectedOnce)
      assertEquals(counterIn(grownChildren(2)).disconnects, 1)
      assertEquals(counterIn(grownChildren(3)).disconnects, 1)
  }

  List(
    ("inserts at the front of", List("a", "b"), List("new", "a", "b")),
    ("inserts in the middle of", List("a", "b"), List("a", "new", "b")),
    ("removes at the front of", List("a", "b", "c"), List("b", "c")),
    ("removes in the middle of", List("a", "b", "c"), List("a", "c"))
  ).foreach { case (change, titles, newTitles) =>
    mounted.test(s"$change an unkeyed list by patching each position") { elm =>
      val before = patch(elm, h("div", titles.map(card("div", _))))
      val elementsBefore = childElements(before)
      val shared = math.min(titles.length, newTitles.length)

      val after = patch(before, h("div", newTitles.map(card("div", _))))

      val children = childElements(after)
      assertEquals(children.map(_.textContent), newTitles)
      children.zip(elementsBefore).foreach { case (child, before) =>
        assert(child eq before)
      }
      elementsBefore.take(shared).map(counterIn).foreach(assertConnectedOnce)
      elementsBefore.drop(shared).map(counterIn).foreach { counter =>
        assertEquals(counter.disconnects, 1)
      }
      children.drop(shared).map(counterIn).foreach(assertConnectedOnce)
    }
  }

  mounted.test(
    "fills and empties placeholder slots without touching siblings"
  ) { elm =>
    val before = patch(
      elm,
      h("div", List(VNode.empty, card("div", "kept"), VNode.empty))
    )
    val keptBefore = childElements(before).head

    val filled = patch(
      before,
      h("div", List(h("p", "first"), card("div", "kept"), h("span", "last")))
    )
    val filledNodes = filled.node.childNodes.toList
    assertEquals(
      filledNodes.map(_.nodeName),
      List("P", "DIV", "SPAN")
    )
    assert(filledNodes(1) eq keptBefore)

    val emptied = patch(
      filled,
      h("div", List(VNode.empty, card("div", "kept"), VNode.empty))
    )
    val emptiedNodes = emptied.node.childNodes.toList
    assertEquals(
      emptiedNodes.map(_.nodeName),
      List("#text", "DIV", "#text")
    )
    assertEquals(emptiedNodes.map(_.textContent), List("", "kept", ""))
    assert(emptiedNodes(1) eq keptBefore)
    assertConnectedOnce(counterIn(keptBefore))
  }

  mounted.test("replaces a comment child with an element") { elm =>
    val before = patch(elm, h("div", List(h.comment("slot"), h("span", "x"))))
    val spanBefore = childElements(before).head

    val after = patch(before, h("div", List(h("p", "filled"), h("span", "x"))))

    val nodes = after.node.childNodes.toList
    assertEquals(nodes.map(_.nodeName), List("P", "SPAN"))
    assert(nodes(1) eq spanBefore)
  }

  mounted.test("reorders keyed children and keeps each node by key") { elm =>
    val before = patch(elm, h("div", List("a", "b", "c", "d").map(keyedCard)))
    val byKeyBefore =
      childElements(before).map(child => child.textContent -> child).toMap

    val order = List("c", "a", "d", "b")
    val after = patch(before, h("div", order.map(keyedCard)))

    val children = childElements(after)
    assertEquals(children.map(_.textContent), order)
    order.zip(children).foreach { case (key, child) =>
      assert(child eq byKeyBefore(key))
    }
  }

  mounted.test("does not move keyed children that keep their order") { elm =>
    val keys = List("a", "b", "c")
    val before = patch(elm, h("div", keys.map(keyedCard)))
    val elementsBefore = childElements(before)

    val after = patch(
      before,
      h(
        "div",
        keys.map(key =>
          h(
            "div",
            VNodeData(key = Some(key)),
            List(h("h3", key + "!"), h(counterTag))
          )
        )
      )
    )

    val children = childElements(after)
    assertEquals(children.map(_.textContent), keys.map(_ + "!"))
    children.zip(elementsBefore).foreach { case (child, before) =>
      assert(child eq before)
    }
    elementsBefore.map(counterIn).foreach(assertConnectedOnce)
  }

  mounted.test("swaps two keyed children by moving only those two") { elm =>
    val keys = (0 until 10).map(_.toString).toList
    val before = patch(elm, h("div", keys.map(keyedCard)))
    val byKeyBefore =
      childElements(before).map(child => child.textContent -> child).toMap

    val swapped = keys.updated(1, keys(8)).updated(8, keys(1))
    val after = patch(before, h("div", swapped.map(keyedCard)))

    val children = childElements(after)
    assertEquals(children.map(_.textContent), swapped)
    swapped.zip(children).foreach { case (key, child) =>
      assert(child eq byKeyBefore(key))
    }
    assertEquals(children.map(counterIn(_).disconnects).sum, 2)
  }

  mounted.test("skips a child patched again with the same VNode instance") {
    elm =>
      var updates = 0
      val counting =
        Hooks(update = Some((_: PatchedVNode, _: VNode) => updates += 1))
      val shared = h("span", VNodeData(hook = Some(counting)), "same")

      val before = patch(elm, h("div", List(shared, h("span", "a"))))
      val after = patch(before, h("div", List(shared, h("span", "b"))))

      assertEquals(updates, 0)
      assertEquals(
        childElements(after).map(_.textContent),
        List("same", "b")
      )
  }

  mounted.test("moves keyed siblings around an unkeyed child") { elm =>
    val before = patch(
      elm,
      h("div", List(keyedCard("x"), card("div", "middle"), keyedCard("y")))
    )
    val elementsBefore = childElements(before)
    val xBefore = elementsBefore(0)
    val middleBefore = elementsBefore(1)
    val yBefore = elementsBefore(2)

    val after = patch(
      before,
      h("div", List(keyedCard("y"), card("div", "middle"), keyedCard("x")))
    )

    val children = childElements(after)
    assertEquals(children.map(_.textContent), List("y", "middle", "x"))
    assert(children(0) eq yBefore)
    assert(children(1) eq middleBefore)
    assert(children(2) eq xBefore)
    assertConnectedOnce(counterIn(middleBefore))
    List(xBefore, yBefore).map(counterIn).foreach { counter =>
      assertEquals(counter.connects, 2)
      assertEquals(counter.disconnects, 1)
    }
  }

  mounted.test("inserts an unkeyed child without moving keyed siblings") {
    elm =>
      val before = patch(elm, h("div", List(keyedCard("x"), keyedCard("y"))))
      val elementsBefore = childElements(before)

      val after = patch(
        before,
        h("div", List(keyedCard("x"), card("div", "middle"), keyedCard("y")))
      )

      val children = childElements(after)
      assertEquals(children.map(_.textContent), List("x", "middle", "y"))
      assert(children(0) eq elementsBefore(0))
      assert(children(2) eq elementsBefore(1))
      elementsBefore.map(counterIn).foreach(assertConnectedOnce)
  }

  List("div", "span").foreach { secondSel =>
    mounted.test(s"keeps both div and $secondSel siblings that share a key") {
      elm =>
        def sameKeyPair(version: String): VNode =
          h(
            "div",
            List("div", secondSel).zipWithIndex.map { case (sel, index) =>
              h(
                sel,
                VNodeData(key = Some("x")),
                List(h("h3", s"$index-$version"), h(counterTag))
              )
            }
          )
        val before = patch(elm, sameKeyPair("old"))
        val elementsBefore = childElements(before)

        val after = patch(before, sameKeyPair("new"))

        val children = childElements(after)
        assertEquals(children.map(_.textContent), List("0-new", "1-new"))
        children.zip(elementsBefore).foreach { case (child, before) =>
          assert(child eq before)
        }
        elementsBefore.map(counterIn).foreach(assertConnectedOnce)
    }
  }

  mounted.test(
    "leaves keyed children in place beside a node awaiting removal"
  ) { elm =>
    var finishRemoval: () => Unit = () => ()
    val delayedRemoval = h(
      "div",
      VNodeData(
        key = Some("b"),
        hook = Some(Hooks(remove = Some((_, rm) => finishRemoval = rm)))
      ),
      List(h("h3", "b"))
    )
    val before = patch(
      elm,
      h("div", List(keyedCard("a"), delayedRemoval, keyedCard("c")))
    )
    val elementsBefore = childElements(before)

    val removing =
      patch(before, h("div", List(keyedCard("a"), keyedCard("c"))))
    assertEquals(childElements(removing), elementsBefore)

    val after = patch(
      removing,
      h("div", List(keyedCard("a"), keyedCard("c"), keyedCard("d")))
    )
    finishRemoval()

    val children = childElements(after)
    assertEquals(children.map(_.textContent), List("a", "c", "d"))
    assert(children(0) eq elementsBefore(0))
    assert(children(1) eq elementsBefore(2))
    children.map(counterIn).foreach(assertConnectedOnce)
  }

}
