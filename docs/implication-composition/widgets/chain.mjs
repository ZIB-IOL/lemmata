// Toggle P, P→Q, Q→R and watch what can be derived. Uses only model.get/set/on, which
// the static MyST theme supports; there is no kernel behind it.
function render({ model, el }) {
  const keys = [["p", "P"], ["pq", "P → Q"], ["qr", "Q → R"]];
  const box = document.createElement("div");
  box.className = "lemmata-chain";
  const out = document.createElement("p");
  const update = () => {
    const p = model.get("p"), pq = model.get("pq"), qr = model.get("qr");
    const q = p && pq, r = q && qr;
    out.textContent = r ? "R follows: P, then Q, then R."
      : q ? "Q follows, but without Q → R we cannot reach R."
      : p ? "Only P is known."
      : "Nothing follows without P.";
    out.dataset.r = String(r);
  };
  for (const [k, label] of keys) {
    const l = document.createElement("label");
    const c = document.createElement("input");
    c.type = "checkbox"; c.checked = !!model.get(k);
    c.addEventListener("change", () => model.set(k, c.checked));
    model.on(`change:${k}`, update);
    l.append(c, " ", label);
    box.append(l);
  }
  box.append(out);
  el.append(box);
  update();
}
export default { render };
