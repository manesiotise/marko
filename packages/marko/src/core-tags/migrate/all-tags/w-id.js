const findBoundParent = require("../util/findBoundParent");

module.exports = function migrate(el, context) {
  const attr = el.getAttribute("w-id");
  if (!attr) {
    return;
  }

  if (!findBoundParent(el)) {
    context.setMigrationFlag("legacyWidgetAttrsWithoutBind");
  }

  el.setAttributeValue("key", attr.value);
  const isHTML = el.tagDef && el.tagDef.html;
  const isDynamic = Boolean(el.rawTagNameExpression);
  const isRepeated =
    attr.value.type === "Literal" && /\[\]$/.test(attr.value.value);
  if (!el.hasAttribute("id") && !isRepeated && (isHTML || isDynamic))
    el.setAttributeValue("id:scoped", attr.value);
  el.removeAttribute(attr.name);
};
