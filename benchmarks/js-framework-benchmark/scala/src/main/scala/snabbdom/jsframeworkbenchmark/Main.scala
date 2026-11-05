/*
 * Copyright 2022 felipehummel
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

package snabbdom.jsframeworkbenchmark

import org.scalajs.dom
import snabbdom.*
import snabbdom.modules.*

import scala.scalajs.js

/** Keep in step with `entries/snabbdom/src/main.js`: the comparison is fair
  * only while both apps do the same work.
  */
object Main {

  final case class Row(id: Int, label: String)
  final case class State(rows: Vector[Row], selected: Int)

  private val adjectives = Array(
    "pretty",
    "large",
    "big",
    "small",
    "tall",
    "short",
    "long",
    "handsome",
    "plain",
    "quaint",
    "clean",
    "elegant",
    "easy",
    "angry",
    "crazy",
    "helpful",
    "mushy",
    "odd",
    "unsightly",
    "adorable",
    "important",
    "inexpensive",
    "cheap",
    "expensive",
    "fancy"
  )
  private val colours = Array(
    "red",
    "yellow",
    "blue",
    "green",
    "pink",
    "brown",
    "purple",
    "brown",
    "white",
    "black",
    "orange"
  )
  private val nouns = Array(
    "table",
    "chair",
    "house",
    "bbq",
    "desk",
    "car",
    "pony",
    "cookie",
    "sandwich",
    "burger",
    "pizza",
    "mouse",
    "keyboard"
  )

  private var nextId = 1

  private def random(max: Int): Int =
    js.Math.round(js.Math.random() * 1000).toInt % max

  private def buildData(count: Int): Vector[Row] = {
    val builder = Vector.newBuilder[Row]
    builder.sizeHint(count)
    var i = 0
    while (i < count) {
      builder += Row(
        nextId,
        adjectives(random(adjectives.length)) + " " +
          colours(random(colours.length)) + " " +
          nouns(random(nouns.length))
      )
      nextId += 1
      i += 1
    }
    builder.result()
  }

  private val patch = init(
    Seq(Classes.module, Props.module, Attributes.module, EventListeners.module)
  )

  private var state = State(Vector.empty, 0)
  private var vnode: PatchedVNode = null

  private def update(f: State => State): Unit = {
    state = f(state)
    vnode = patch(vnode, view(state))
  }

  private def run(): Unit = update(_ => State(buildData(1000), 0))

  private def runLots(): Unit = update(_ => State(buildData(10000), 0))

  private def add(): Unit =
    update(s => s.copy(rows = s.rows ++ buildData(1000)))

  private def updateEvery10th(): Unit = update { s =>
    var rows = s.rows
    var i = 0
    while (i < rows.length) {
      val row = rows(i)
      rows = rows.updated(i, row.copy(label = row.label + " !!!"))
      i += 10
    }
    s.copy(rows = rows)
  }

  private def clear(): Unit = update(_ => State(Vector.empty, 0))

  private def swapRows(): Unit = update { s =>
    if (s.rows.length > 998)
      s.copy(rows = s.rows.updated(1, s.rows(998)).updated(998, s.rows(1)))
    else s
  }

  private def remove(id: Int): Unit = update { s =>
    val idx = s.rows.indexWhere(_.id == id)
    s.copy(rows = s.rows.patch(idx, Nil, 1))
  }

  private def select(id: Int): Unit = update(_.copy(selected = id))

  private val ariaHidden = VNodeData(attrs = Map("aria-hidden" -> "true"))

  private def onClick(cb: () => Unit): VNodeData =
    VNodeData(on = Map("click" -> EventHandler((_: dom.Event) => cb())))

  // A thunk is skipped when both its function and its arguments are equal to
  // the previous render's, so the function must be a single stable instance.
  private val renderRow: Any => VNode.Element = { args =>
    val (row, selected) = args.asInstanceOf[(Row, Boolean)]
    h(
      "tr",
      VNodeData(
        key = Some(row.id.toString),
        classes = Map("danger" -> selected)
      ),
      List(
        h("td.col-md-1", row.id.toString),
        h(
          "td.col-md-4",
          List(h("a", onClick(() => select(row.id)), row.label))
        ),
        h(
          "td.col-md-1",
          List(
            h(
              "a",
              onClick(() => remove(row.id)),
              List(h("span.glyphicon.glyphicon-remove", ariaHidden))
            )
          )
        ),
        h("td.col-md-6")
      )
    )
  }

  private def button(id: String, title: String, cb: () => Unit): VNode =
    h(
      "div.col-sm-6.smallpad",
      List(
        h(
          s"button#$id.btn.btn-primary.btn-block",
          onClick(cb).copy(attrs = Map("type" -> "button")),
          title
        )
      )
    )

  private val renderJumbotron: Any => VNode.Element = _ =>
    h(
      "div.jumbotron",
      List(
        h(
          "div.row",
          List(
            h("div.col-md-6", List(h("h1", "scala-js-snabbdom keyed"))),
            h(
              "div.col-md-6",
              List(
                h(
                  "div.row",
                  List(
                    button("run", "Create 1,000 rows", () => run()),
                    button("runlots", "Create 10,000 rows", () => runLots()),
                    button("add", "Append 1,000 rows", () => add()),
                    button(
                      "update",
                      "Update every 10th row",
                      () => updateEvery10th()
                    ),
                    button("clear", "Clear", () => clear()),
                    button("swaprows", "Swap Rows", () => swapRows())
                  )
                )
              )
            )
          )
        )
      )
    )

  private def view(s: State): VNode =
    h(
      "div#main",
      List(
        h(
          "div.container",
          List(
            thunk("div.jumbotron", renderJumbotron, ()),
            h(
              "table.table.table-hover.table-striped.test-data",
              List(
                h(
                  "tbody",
                  s.rows.iterator.map { row =>
                    thunk(
                      "tr",
                      row.id.toString,
                      renderRow,
                      (row, row.id == s.selected)
                    )
                  }.toList
                )
              )
            ),
            h("span.preloadicon.glyphicon.glyphicon-remove", ariaHidden)
          )
        )
      )
    )

  def main(args: Array[String]): Unit =
    vnode = patch(dom.document.getElementById("main"), view(state))

}
