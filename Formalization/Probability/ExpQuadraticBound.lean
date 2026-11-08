import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
# A quadratic upper bound for the exponential

`exp_le_one_add_add_sq`: `e^x ≤ 1 + x + x²` for `|x| ≤ 1` (from Mathlib's
`Real.abs_exp_sub_one_sub_id_le`). Used by the exponential-moment tail bounds
(`Probability/SeqLawExpTail.lean`) and the second-order Hedge regret
(`Online/Hedge/SecondOrderRegret.lean`).
-/

namespace StatisticalRL

/-- `e^x ≤ 1 + x + x²` for `|x| ≤ 1`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.1 h).2
  linarith

end StatisticalRL
