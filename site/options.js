"use strict";
const form = document.querySelector("#options");
function updateOptions() {
  const mode = new FormData(form).get("mode");
  const effort = document.querySelector("#effort").value;
  const opts = [];
  if (mode !== "search") opts.push("(mode := .committed)");
  if (effort !== "1000") opts.push(`(effort := ${effort})`);
  if (!document.querySelector("#lazy").checked) opts.push("(lazy := false)");
  if (document.querySelector("#defer").checked) opts.push("(deferChecks := true)");
  const tactic = document.querySelector("#report").checked ? "waterfall?" : "waterfall";
  document.querySelector("#snippet").textContent = tactic +
    (opts.length ? "\n  " + opts.join("\n  ") : "") + "\n  [myDefinition, helperLemma]";
  document.querySelector("#mode-note").textContent = mode === "search"
    ? "Search retains alternatives when a later obligation fails."
    : "Committed search accepts the first local progress and discards alternatives. It uses a different induction schedule and costs.";
}
form.addEventListener("input", updateOptions);
updateOptions();
