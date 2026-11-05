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
import snabbdom.modules.Attributes

import scala.collection.mutable
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.scalajs.js

/** Emits the cases formal/Conform.lean replays; the output format is described
  * there. Run it through formal/conformance.sh, which sets
  * SNABBDOM_CONFORMANCE: the suite is too slow for the normal test run.
  */
class ConformanceSuite extends munit.FunSuite {

  val nCases = 10000

  final class RecordingDomApi(underlying: DomApi) extends DomApi {
    val ids = js.Map.empty[dom.Node, Int]
    var nextId = 0
    var recording = false
    val trace = mutable.ArrayBuffer.empty[String]

    def id(n: dom.Node): String = ids.get(n).fold("?")(_.toString)
    private def fresh[N <: dom.Node](n: N): N = {
      if (recording) { ids(n) = nextId; nextId += 1 }
      n
    }
    private def log(s: => String): Unit = if (recording) trace += s

    def createElement(tagName: String): dom.HTMLElement = {
      val e = fresh(underlying.createElement(tagName))
      log(s"ce ${id(e)} $tagName")
      e
    }
    def createElementNS(ns: String, name: String): dom.Element = {
      val e = fresh(underlying.createElementNS(ns, name))
      log(s"ce ${id(e)} $name")
      e
    }
    def createDocumentFragment: dom.DocumentFragment =
      underlying.createDocumentFragment
    def createTextNode(text: String): dom.Text = {
      val t = fresh(underlying.createTextNode(text))
      log(s"ct ${id(t)} $text")
      t
    }
    def createComment(text: String): dom.Comment = {
      val c = fresh(underlying.createComment(text))
      log(s"cc ${id(c)} $text")
      c
    }
    def insertBefore(
        parentNode: dom.Node,
        newNode: dom.Node,
        referenceNode: Option[dom.Node]
    ): Unit = {
      log(
        s"ib ${id(parentNode)} ${id(newNode)} ${referenceNode.fold("-")(id)}"
      )
      underlying.insertBefore(parentNode, newNode, referenceNode)
    }
    def removeChild(node: dom.Node, child: dom.Node): Unit = {
      log(s"rc ${id(node)} ${id(child)}")
      underlying.removeChild(node, child)
    }
    def appendChild(node: dom.Node, child: dom.Node): Unit = {
      log(s"ac ${id(node)} ${id(child)}")
      underlying.appendChild(node, child)
    }
    def parentNode(node: dom.Node): Option[dom.Node] =
      underlying.parentNode(node)
    def nextSibling(node: dom.Node): Option[dom.Node] =
      underlying.nextSibling(node)
    def tagName(elm: dom.Element): String = underlying.tagName(elm)
    def setTextContent(node: dom.Node, text: Option[String]): Unit = {
      log(s"st ${id(node)} ${text.getOrElse("")}")
      underlying.setTextContent(node, text)
    }
    def getTextContent(node: dom.Node): Option[String] =
      underlying.getTextContent(node)
    def isElement(node: dom.Node): Boolean = underlying.isElement(node)
    def isText(node: dom.Node): Boolean = underlying.isText(node)
    def isComment(node: dom.Node): Boolean = underlying.isComment(node)
    def isDocumentFragement(node: dom.Node): Boolean =
      underlying.isDocumentFragement(node)
  }

  /** Small alphabets, so that keys, tags and texts collide often: duplicate
    * keys among siblings, keyed and unkeyed siblings mixed, tag changes,
    * comments and text nodes. Attributes include the `id` and `class` a
    * selector also sets, and names in upper case, which the DOM lowercases:
    * both are outside the proved theorem but must still match the model.
    * Selectors in upper case check that the model lowercases tags too.
    *
    * A `wide` generator gives up to 12 siblings, mostly keyed elements over
    * more keys, so that `longestIncreasingRun` and `placeWithFewestMoves` also
    * run on long lists with several moved blocks.
    */
  final class CaseGen(seed: Long, wide: Boolean) {
    private val r = new scala.util.Random(seed)
    def coin(num: Int, den: Int): Boolean = r.nextInt(den) < num
    private def pick[A](xs: Vector[A]): A = xs(r.nextInt(xs.length))
    private val sels =
      Vector(
        "div",
        "span",
        "p",
        "div#a",
        "div.x",
        "p#b.x.y",
        "span.x",
        "DIV",
        "Span.x"
      )
    private val keys =
      if (wide) Vector("a", "b", "c", "d", "e", "f", "g", "h")
      else Vector("a", "b", "c")
    private val maxChildren = if (wide) 12 else 4
    private val lastTextDraw = if (wide) 1 else 4
    // One spelling per name within a map: a Scala Map holding both `title`
    // and `TITLE` would set the same DOM attribute twice, in an iteration
    // order the JSON (sorted by key) does not carry.
    private val attrKeys = Vector("title", "lang", "dir", "id", "class")

    private def attrs(): Map[String, AttrValue] =
      attrKeys
        .filter(_ => coin(1, 3))
        .map { k =>
          (if (coin(1, 6)) k.toUpperCase else k) ->
            (if (coin(1, 4)) AttrValue.BooleanAttrValue(r.nextBoolean())
             else AttrValue.StringAttrValue(pick(Vector("x", "y"))))
        }
        .toMap

    def elem(depth: Int): VNode.Element = VNode.Element(
      pick(sels),
      VNodeData(
        key =
          if (r.nextInt(if (wide) 10 else 3) == 0) None else Some(pick(keys)),
        attrs = attrs()
      ),
      if (depth <= 0) Nil
      else List.fill(r.nextInt(maxChildren + 1))(node(depth - 1))
    )

    def root(depth: Int): VNode = r.nextInt(10) match {
      case 0 => VNode.Text(pick(Vector("t", "u")))
      case 1 => VNode.Comment(pick(Vector("c", "d")))
      case _ => elem(depth)
    }

    def node(depth: Int): VNode = r.nextInt(12) match {
      case 0                      => VNode.Comment(pick(Vector("c", "d")))
      case n if n <= lastTextDraw => VNode.Text(pick(Vector("t", "u")))
      case _                      => elem(depth)
    }

    def mutate(v: VNode, depth: Int): VNode = v match {
      case VNode.Element(sel, data, ch) =>
        val sel1 = if (r.nextInt(10) == 0) pick(sels) else sel
        val key1 =
          if (r.nextInt(10) == 0)
            (if (r.nextBoolean()) None else Some(pick(keys)))
          else data.key
        val attrs1 = if (r.nextInt(3) == 0) attrs() else data.attrs
        VNode.Element(
          sel1,
          data.copy(key = key1, attrs = attrs1),
          mutateList(ch, depth - 1)
        )
      case other => if (r.nextInt(5) == 0) node(depth) else other
    }

    private def mutateList(ch: List[VNode], depth: Int): List[VNode] = {
      var xs = ch
      if (r.nextInt(2) == 0) xs = r.shuffle(xs)
      if (r.nextInt(4) == 0) xs = xs.filter(_ => r.nextInt(3) != 0)
      if (depth > 0 && r.nextInt(4) == 0) {
        val at = r.nextInt(xs.length + 1)
        xs = xs.take(at) ++ List(node(depth - 1)) ++ xs.drop(at)
      }
      xs.map(mutate(_, depth))
    }
  }

  private def str(s: String) = "\"" + s + "\""

  private def json(v: VNode): String = v match {
    case VNode.Text(s)    => s"""{"x":${str(s)}}"""
    case VNode.Comment(s) => s"""{"c":${str(s)}}"""
    case VNode.Element(sel, data, ch) =>
      val attrs = data.attrs.toList.sortBy(_._1).map {
        case (k, AttrValue.StringAttrValue(v))  => s"[${str(k)},${str(v)}]"
        case (k, AttrValue.BooleanAttrValue(b)) => s"[${str(k)},$b]"
      }
      s"""{"sel":${str(sel)},"key":${data.key.fold("null")(str)},""" +
        s""""attrs":[${attrs
            .mkString(",")}],"ch":[${ch.map(json).mkString(",")}]}"""
  }

  /** Same format as `serialize` in formal/Conform.lean. */
  private def serialize(n: dom.Node): String = n.nodeType match {
    case 3 => "\"" + n.textContent + "\""
    case 8 => "<!--" + n.textContent + "-->"
    case _ =>
      val e = n.asInstanceOf[dom.Element]
      val tag = e.tagName.toLowerCase
      val attrs = (0 until e.attributes.length)
        .map(i => e.attributes(i))
        .sortBy(_.name)
        .map(a => s""" ${a.name}="${a.value}"""")
        .mkString
      val children = (0 until e.childNodes.length)
        .map(i => serialize(e.childNodes(i)))
        .mkString
      s"<$tag$attrs>$children</$tag>"
  }

  private def div(sel: String, attrs: (String, String)*): VNode =
    VNode.Element(
      sel,
      VNodeData(attrs = attrs.map { case (k, v) =>
        k -> AttrValue.StringAttrValue(v)
      }.toMap),
      Nil
    )

  /** The library counterexamples in formal/Snabbdom/Counterexamples.lean, so
    * the model is checked against Scala on exactly those inputs, and keys that
    * take the Attributes module's `setAttributeNS` branch, which the model
    * treats as `setAttribute`.
    */
  private val fixedCases: List[(VNode, VNode)] = List(
    div("div#a", "id" -> "z") -> div("div#a"),
    div("div", "TITLE" -> "x") -> div("div", "title" -> "y"),
    div("div", "xml:lang" -> "en") ->
      div("div", "xml:lang" -> "fr", "xlink:href" -> "#a"),
    div("div", "xlink:href" -> "#a") -> div("span", "xml:lang" -> "en")
  )

  test("emit conformance cases") {
    val gen = new CaseGen(seed = 20261104L, wide = false)
    val wideGen = new CaseGen(seed = 20261105L, wide = true)
    val randomCases = (0 until nCases).iterator.map { _ =>
      // shallower when wide, to keep the case size close to the others
      val (g, depth) = if (gen.coin(1, 10)) (wideGen, 2) else (gen, 3)
      val old = g.root(depth)
      val neu = if (g.coin(2, 3)) g.mutate(old, depth) else g.root(depth)
      val detached = g.coin(1, 5)
      // a sibling after `old`, so that replacing it inserts before a node
      val sibling = !detached && g.coin(1, 2)
      (old, neu, detached, sibling)
    }
    val cases = fixedCases.iterator.map { case (o, n) =>
      (o, n, false, true)
    } ++ randomCases
    cases.foreach { case (old, neu, detached, sibling) =>
      val api = new RecordingDomApi(DomApi.apply)
      val patch = init(Seq(Attributes.module), Some(api))
      val host = dom.document.createElement("div")
      val placeholder = dom.document.createElement("x-placeholder")
      host.appendChild(placeholder)
      val pv1 = patch(placeholder, old)
      if (detached) host.removeChild(pv1.node)
      val sib =
        if (sibling)
          Some(host.appendChild(dom.document.createElement("x-sibling")))
        else None

      // ids in the order the model allocates them: host is 0, then the old
      // tree in pre-order (as createElm allocates), then the sibling
      api.ids(host) = 0
      var next = 1
      def number(p: PatchedVNode): Unit = {
        api.ids(p.node) = next
        next += 1
        p match {
          case PatchedVNode.Element(_, _, ch, _) => ch.foreach(number)
          case _                                 => ()
        }
      }
      number(pv1)
      sib.foreach { s =>
        api.ids(s) = next; next += 1
      }
      api.nextId = next
      api.recording = true
      val pv2 = patch(pv1, neu)
      api.recording = false

      val trace = api.trace.map(str).mkString(",")
      val domStr = (0 until host.childNodes.length)
        .map(i => serialize(host.childNodes(i)))
        .mkString + "|" + serialize(pv2.node)
      println(
        s"""CONFORMANCE {"old":${json(old)},"new":${json(
            neu
          )},"detached":$detached,"sibling":$sibling,"trace":[$trace],"dom":${str(
            domStr.replace("\"", "\\\"")
          )}}"""
      )
    }
    println(s"CONFORMANCE-END ${nCases + fixedCases.length}")
    // The Selenium env drops the tail of the browser console when the run
    // ends, so pad the output and give it time to drain.
    (0 until 200).foreach(_ => println("CONFORMANCE-PAD"))
    val drained = Promise[Unit]()
    js.timers.setTimeout(1000)(drained.success(()))
    drained.future
  }

}
