// size: 331 (min) 202 (brotli)

import {
  register as n,
  on as o,
  queueSource as t,
  value as r,
  data as c,
  intersection as m,
  queueEffect as i,
  init as s,
} from "@marko/runtime-tags/dom";
const u = n("d", (n) =>
    o(
      n[0],
      "click",
      ((n) => {
        const { 2: o, 3: r } = n;
        return function () {
          t(
            n,
            a,
            o.map(
              ((n) => {
                const { 3: o } = n;
                return (n) => o;
              })(n),
            ),
          );
        };
      })(n),
    ),
  ),
  a = r(
    2,
    (n, o) => c(n[1], o.join("")),
    m(2, (n) => {
      i(n, u);
    }),
  );
s();
