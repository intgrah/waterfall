import Waterfall

open Lean Elab Command
run_cmd do
  for name in [`Waterfall.Observe.capture, `Waterfall.Observe.replay,
      `WFCore.run, `LeanWaterfall.waterfallTac] do
    if (← getEnv).contains name then
      throwError "unexpected implementation in default import: {name}"

example (P : Prop) (h : P) : P := by waterfall
