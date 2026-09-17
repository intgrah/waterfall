module
import waterfall

open Lean Elab Command

run_cmd do
  for name in [`waterfall.Mode, `waterfall.Mode.hooks, `waterfall.Options] do
    unless (← getEnv).contains name do
      throwError "missing facade declaration: {name}"
  for name in [`waterfall.Observe.capture, `waterfall.Observe.replay,
      `waterfall.elabOptions] do
    if (← getEnv).contains name then
      throwError "unexpected facade declaration: {name}"

example (P : Prop) (h : P) : P := by waterfall
