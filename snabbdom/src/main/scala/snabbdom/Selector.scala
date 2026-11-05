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

/** A selector such as `div#app.a.b`, from which `createElm` makes a `div` with
  * `id="app"` and `class="a b"`.
  */
private[snabbdom] final case class Selector(
    tag: String,
    id: Option[String],
    classes: Option[String]
)

private[snabbdom] object Selector {

  def parse(sel: String): Selector = {
    val hashIdx = sel.indexOf("#")
    val dotIdx = sel.indexOf(".", hashIdx)
    val hash = if (hashIdx > 0) hashIdx else sel.length
    val dot = if (dotIdx > 0) dotIdx else sel.length
    val tag =
      if (hashIdx != -1 || dotIdx != -1) sel.substring(0, math.min(hash, dot))
      else sel
    val id = if (hash < dot) Some(sel.substring(hash + 1, dot)) else None
    val classes =
      if (dotIdx > 0) {
        val cs = sel.substring(dot + 1)
        Some(if (cs.indexOf('.') < 0) cs else cs.replace('.', ' '))
      } else None
    Selector(tag, id, classes)
  }

  /** The value `createElm` gives the attribute `name` from `sel`: only `id` and
    * `class`, spelled exactly so.
    */
  def attr(sel: String, name: String): Option[String] = name match {
    case "id"    => parse(sel).id
    case "class" => parse(sel).classes
    case _       => None
  }

}
