import Mathlib.Data.Real.Basic

/-! Definition-only reciprocal count vocabulary for the source Lemma 5.3. -/
namespace StatisticalRL.OnlineRL

/-- The source summand `1 / max(n, 1)`, with the visit count cast to reals. -/
noncomputable def onlineReciprocalMaxOneCount (n : ℕ) : ℝ :=
  (((max n 1 : ℕ) : ℝ)⁻¹)

end StatisticalRL.OnlineRL
