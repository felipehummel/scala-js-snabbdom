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
    */
  final class CaseGen(seed: Long) {
    private val r = new scala.util.Random(seed)
    def coin(num: Int, den: Int): Boolean = r.nextInt(den) < num
    private def pick[A](xs: Vector[A]): A = xs(r.nextInt(xs.length))
    private val sels =
      Vector("div", "span", "p", "div#a", "div.x", "p#b.x.y", "span.x")
    private val keys = Vector("a", "b", "c")
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
        key = if (r.nextInt(3) == 0) None else Some(pick(keys)),
        attrs = attrs()
      ),
      if (depth <= 0) Nil else List.fill(r.nextInt(5))(node(depth - 1))
    )

    def root(depth: Int): VNode = r.nextInt(10) match {
      case 0 => VNode.Text(pick(Vector("t", "u")))
      case 1 => VNode.Comment(pick(Vector("c", "d")))
      case _ => elem(depth)
    }

    def node(depth: Int): VNode = r.nextInt(12) match {
      case 0             => VNode.Comment(pick(Vector("c", "d")))
      case 1 | 2 | 3 | 4 => VNode.Text(pick(Vector("t", "u")))
      case _             => elem(depth)
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
    * the model is checked against Scala on exactly those inputs.
    */
  private val fixedCases: List[(VNode, VNode)] = List(
    div("div#a", "id" -> "z") -> div("div#a"),
    div("div", "TITLE" -> "x") -> div("div", "title" -> "y")
  )

  test("emit conformance cases") {
    val gen = new CaseGen(seed = 20261104L)
    val randomCases = (0 until nCases).iterator.map { _ =>
      val old = gen.root(3)
      val neu = if (gen.coin(2, 3)) gen.mutate(old, 3) else gen.root(3)
      (old, neu, gen.coin(1, 5))
    }
    val cases = fixedCases.iterator.map { case (o, n) =>
      (o, n, false)
    } ++ randomCases
    cases.foreach { case (old, neu, detached) =>
      val api = new RecordingDomApi(DomApi.apply)
      val patch = init(Seq(Attributes.module), Some(api))
      val host = dom.document.createElement("div")
      val placeholder = dom.document.createElement("x-placeholder")
      host.appendChild(placeholder)
      val pv1 = patch(placeholder, old)
      if (detached) host.removeChild(pv1.node)

      // ids: host is 0, the old tree is numbered in pre-order, as createElm
      // allocates them in the model
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
          )},"detached":$detached,"trace":[$trace],"dom":${str(
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
