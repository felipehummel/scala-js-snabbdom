import {
  init,
  classModule,
  propsModule,
  attributesModule,
  eventListenersModule,
  h,
  thunk,
} from "snabbdom";

// Mirrors the Scala.js entry (scala/src/main/scala/.../Main.scala) so the two
// Snabbdom entries differ only in the library. Each row is a thunk, the
// Snabbdom counterpart of the `memo` rows in the React entries.

const adjectives = ["pretty", "large", "big", "small", "tall", "short", "long",
  "handsome", "plain", "quaint", "clean", "elegant", "easy", "angry", "crazy",
  "helpful", "mushy", "odd", "unsightly", "adorable", "important",
  "inexpensive", "cheap", "expensive", "fancy"];
const colours = ["red", "yellow", "blue", "green", "pink", "brown", "purple",
  "brown", "white", "black", "orange"];
const nouns = ["table", "chair", "house", "bbq", "desk", "car", "pony",
  "cookie", "sandwich", "burger", "pizza", "mouse", "keyboard"];

let nextId = 1;

const random = (max) => Math.round(Math.random() * 1000) % max;

function buildData(count) {
  const data = new Array(count);
  for (let i = 0; i < count; i++) {
    data[i] = {
      id: nextId++,
      label: `${adjectives[random(adjectives.length)]} ${colours[random(colours.length)]} ${nouns[random(nouns.length)]}`,
    };
  }
  return data;
}

const patch = init([classModule, propsModule, attributesModule, eventListenersModule]);

let state = { rows: [], selected: 0 };
let vnode;

function update(f) {
  state = f(state);
  vnode = patch(vnode, view(state));
}

const run = () => update(() => ({ rows: buildData(1000), selected: 0 }));

const runLots = () => update(() => ({ rows: buildData(10000), selected: 0 }));

const add = () => update((s) => ({ ...s, rows: s.rows.concat(buildData(1000)) }));

const updateEvery10th = () =>
  update((s) => {
    const rows = s.rows.slice();
    for (let i = 0; i < rows.length; i += 10) {
      const row = rows[i];
      rows[i] = { id: row.id, label: row.label + " !!!" };
    }
    return { ...s, rows };
  });

const clear = () => update(() => ({ rows: [], selected: 0 }));

const swapRows = () =>
  update((s) => {
    if (s.rows.length <= 998) return s;
    const rows = s.rows.slice();
    rows[1] = s.rows[998];
    rows[998] = s.rows[1];
    return { ...s, rows };
  });

const remove = (id) =>
  update((s) => {
    const idx = s.rows.findIndex((row) => row.id === id);
    return { ...s, rows: [...s.rows.slice(0, idx), ...s.rows.slice(idx + 1)] };
  });

const select = (id) => update((s) => ({ ...s, selected: id }));

const ariaHidden = { attrs: { "aria-hidden": "true" } };

// A thunk is skipped when its arguments are identical (===) to the previous
// render's.
function renderRow(row, selected) {
  return h("tr", { key: row.id, class: { danger: selected } }, [
    h("td.col-md-1", String(row.id)),
    h("td.col-md-4", [h("a", { on: { click: () => select(row.id) } }, row.label)]),
    h("td.col-md-1", [
      h("a", { on: { click: () => remove(row.id) } }, [
        h("span.glyphicon.glyphicon-remove", ariaHidden),
      ]),
    ]),
    h("td.col-md-6"),
  ]);
}

const button = (id, title, cb) =>
  h("div.col-sm-6.smallpad", [
    h(`button#${id}.btn.btn-primary.btn-block`, { attrs: { type: "button" }, on: { click: cb } }, title),
  ]);

const renderJumbotron = () =>
  h("div.jumbotron", [
    h("div.row", [
      h("div.col-md-6", [h("h1", "snabbdom keyed")]),
      h("div.col-md-6", [
        h("div.row", [
          button("run", "Create 1,000 rows", run),
          button("runlots", "Create 10,000 rows", runLots),
          button("add", "Append 1,000 rows", add),
          button("update", "Update every 10th row", updateEvery10th),
          button("clear", "Clear", clear),
          button("swaprows", "Swap Rows", swapRows),
        ]),
      ]),
    ]),
  ]);

const view = (s) =>
  h("div#main", [
    h("div.container", [
      thunk("div.jumbotron", renderJumbotron, []),
      h("table.table.table-hover.table-striped.test-data", [
        h(
          "tbody",
          s.rows.map((row) => thunk("tr", row.id, renderRow, [row, row.id === s.selected])),
        ),
      ]),
      h("span.preloadicon.glyphicon.glyphicon-remove", ariaHidden),
    ]),
  ]);

vnode = patch(document.getElementById("main"), view(state));
