import Tests.ForeignTrace
import Waterfall

-- Initialization of both packages must succeed, before any tactic can run.
example : True := by waterfall
example : True := by waterfall (mode := .committed)
