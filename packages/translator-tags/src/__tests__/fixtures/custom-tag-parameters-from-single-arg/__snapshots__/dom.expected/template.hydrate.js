// size: 473 (min) 283 (brotli)

import {
  dynamicTagAttrs as o,
  register as i,
  on as t,
  queueSource as n,
  value as c,
  data as d,
  queueEffect as r,
  intersection as m,
  createRenderer as v,
  init as s,
} from "@marko/runtime-tags/dom";
const u = o(2),
  a = m(2, (o) => {
    const { 5: i } = o;
    u(o, () => i);
  }),
  b = i("a0", (o) =>
    t(
      o[0],
      "click",
      ((o) => {
        const { 5: i } = o;
        return function () {
          n(o, e, i + 1);
        };
      })(o),
    ),
  ),
  e = c(
    5,
    (o, i) => {
      d(o[1], i), r(o, b);
    },
    a,
  ),
  f = c(2, (o, i) => d(o[0], i));
i(
  "b0",
  v(
    "<div>Count: <!></div>",
    "Db%",
    void 0,
    void 0,
    void 0,
    c(1, (o, i) => f(o, i[0])),
  ),
),
  s();