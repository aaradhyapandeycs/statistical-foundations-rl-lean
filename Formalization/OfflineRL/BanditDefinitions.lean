import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Definitions for the offline bandit model and its sampling law.

Source: `chapters/offlineRL.tex:243–260, 322–334, 400–443`.
The zero-count fallback discussed in the chapter is commented out at lines 429–430;
see `docs/SOURCE-ISSUES.md#C18` for the distinction from the active pseudocode.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL

/-- Actual offline bandit data law (`offlineRL.tex:243–260`): an i.i.d. behaviour action
vector `a ~ ⊗_N d` and an independent standard Gaussian noise vector `z ~ ⊗_N N(0,1)`. -/
noncomputable def offlineBanditLaw {Arm : Type*} [MeasurableSpace Arm] (d : Measure Arm) (N : ℕ) :
    Measure ((Fin N → Arm) × (Fin N → ℝ)) :=
  (Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

/-- `n_b = #{i | a_i = b}`. -/
def armCount {N : ℕ} (a : Fin N → Arm) (b : Arm) : ℕ :=
  (Finset.univ.filter (fun i => a i = b)).card

/-- Empirical mean reward of arm `b` (Lean's `x/0 = 0` matches the source's
zero-count convention `μ̂_b = 0`). -/
noncomputable def empiricalArmMean {N : ℕ} (r : Arm → ℝ) (a : Fin N → Arm) (z : Fin N → ℝ)
    (b : Arm) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => a i = b), (r (a i) + z i)) / armCount a b

/-- Confidence radius `√(2 log(4A/δ)/n)`. -/
noncomputable def armRadius (A : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (4 * A / δ) / n)

/-- LCB under the commented fallback: `r̄ = 0, b = 1` at `N_b = 0`. -/
noncomputable def lcbFallback {N : ℕ} (r : Arm → ℝ) (a : Fin N → Arm) (z : Fin N → ℝ) (δ : ℝ)
    (b : Arm) : ℝ :=
  if armCount a b = 0 then 0 - 1
  else empiricalArmMean r a z b - armRadius (Fintype.card Arm) δ (armCount a b)

/-- Repaired mean: the empirical mean, or `0` at zero count. -/
noncomputable def safeMean {N : ℕ} (r : Arm → ℝ) (a : Fin N → Arm) (z : Fin N → ℝ) (b : Arm) : ℝ :=
  if armCount a b = 0 then 0 else empiricalArmMean r a z b

/-- Repaired radius: `√(2 log(4A/δ)/N_b)`, or `1` at zero count. -/
noncomputable def safeRadius {N : ℕ} (a : Fin N → Arm) (δ : ℝ) (b : Arm) : ℝ :=
  if armCount a b = 0 then 1 else armRadius (Fintype.card Arm) δ (armCount a b)

end StatisticalRL.OfflineRL
