import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
namespace StatisticalRL.OnlineRL
/-- Total source-compatible scalar Q update: no zero-count bonus is evaluated.
The empirical row can retain its source uniform initialization when N=0. -/
noncomputable def onlineZeroCountSafeQUpdate
    (reward mean variance H L c₁ c₂ : ℝ) (N : ℕ) : ℝ :=
  if N=0 then H else
    min (reward+mean+c₁*Real.sqrt (variance*L/N)+c₂*H*L/N) H


end StatisticalRL.OnlineRL
