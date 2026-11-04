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

import scala.scalajs.js
import scala.scalajs.js.annotation.JSGlobal

// Minimal facades for the ES2015 collections, used as scratch space inside
// `init`. Nothing here is visible outside the library.

@js.native
@JSGlobal("Set")
private[snabbdom] class JSSet[A]() extends js.Object {
  def add(value: A): this.type = js.native
  def has(value: A): Boolean = js.native
}

@js.native
@JSGlobal("Map")
private[snabbdom] class JSMap[K, V]() extends js.Object {
  def get(key: K): js.UndefOr[V] = js.native
  def set(key: K, value: V): this.type = js.native
}
