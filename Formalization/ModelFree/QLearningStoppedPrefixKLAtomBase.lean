import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Zero-safe atomic KL summand for the countable stopped-prefix law. -/

namespace StatisticalRL.QLearning.CountablePinsker

/-- Zero-safe oriented KL atom, with numerator first and reference second. -/
noncomputable def qStoppedPrefixKLAtom (a b : ℝ) : ℝ :=
  if a = 0 then 0 else a * Real.log (a / b)

end StatisticalRL.QLearning.CountablePinsker
