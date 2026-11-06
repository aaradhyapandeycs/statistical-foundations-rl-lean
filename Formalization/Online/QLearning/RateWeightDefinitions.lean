import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Definition-only source models for the learning rates and weights in
`lemma:property_lr`. This module contains no theorem declarations.
-/


namespace StatisticalRL.OnlineRL

/-- Source learning rate `η_n = (H+1)/(H+n)` (`eq:learning_rate_ucbq`). -/
noncomputable def onlineQRate (H n : ℕ) : ℝ :=
  ((H : ℝ) + 1) / ((H : ℝ) + n)

/-- Source weights `η_n^N` (`equ:learning_rate_notation`) for `n ≥ 1`, and
`η_0^N` (`equ:learning_rate_notation-eta_0n`) at `n = 0`. Empty products give the
source's `N = n` and `N = 0` branches. -/
noncomputable def onlineQRateWeight (H N n : ℕ) : ℝ :=
  if n = 0 then ∏ i ∈ Finset.Icc 1 N, (1 - onlineQRate H i)
  else if n ≤ N then onlineQRate H n * ∏ i ∈ Finset.Icc (n + 1) N, (1 - onlineQRate H i)
  else 0

end StatisticalRL.OnlineRL
