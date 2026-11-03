import Formalization.ModelFree.QLearningStoppedPrefixKLAtomBase
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Nonnegativity of countable atomic KL under explicit support and summability. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

/-- Pointwise Gibbs inequality in `KL(p || q)` orientation. The zero
numerator case does not require reference support; for a positive numerator,
the stated support implication gives a strictly positive denominator. -/
theorem qStoppedKLAtom_ge_sub (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsupport : a ≠ 0 → b ≠ 0) :
    a - b ≤ qStoppedPrefixKLAtom a b := by
  by_cases ha0 : a = 0
  · simp [qStoppedPrefixKLAtom, ha0]
    exact hb
  · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb0 := hsupport ha0
    have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hbPos haPos)
    have hlogQ : Real.log (b / a) = Real.log b - Real.log a :=
      Real.log_div (ne_of_gt hbPos) (ne_of_gt haPos)
    have hlogP : Real.log (a / b) = Real.log a - Real.log b :=
      Real.log_div (ne_of_gt haPos) (ne_of_gt hbPos)
    have hmul := mul_le_mul_of_nonneg_left hlog haPos.le
    have hmul' : a * (Real.log b - Real.log a) ≤ b - a := by
      calc
        a * (Real.log b - Real.log a) = a * Real.log (b / a) := by rw [hlogQ]
        _ ≤ a * (b / a - 1) := hmul
        _ = b - a := by field_simp [ne_of_gt haPos]
    rw [qStoppedPrefixKLAtom, if_neg ha0, hlogP]
    nlinarith

/-- Countable Gibbs nonnegativity for probability masses, with the convergence
obligation explicit as absolute summability of the zero-safe KL atoms. -/
theorem qStoppedKLSeries_nonneg_of_probability
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p 1) (hqSum : HasSum q 1)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |qStoppedPrefixKLAtom (p ω) (q ω)|)) :
    0 ≤ ∑' ω, qStoppedPrefixKLAtom (p ω) (q ω) := by
  have hkl : Summable (fun ω ↦ qStoppedPrefixKLAtom (p ω) (q ω)) := hklAbs.of_abs
  have hterm (ω : Ω) : p ω - q ω ≤ qStoppedPrefixKLAtom (p ω) (q ω) :=
    qStoppedKLAtom_ge_sub (p ω) (q ω) (hp ω) (hq ω) (hsupport ω)
  have hdiff : Summable (fun ω ↦ p ω - q ω) := hpSum.summable.sub hqSum.summable
  have hsum := hdiff.tsum_le_tsum hterm hkl
  rw [hpSum.summable.tsum_sub hqSum.summable,
    hpSum.tsum_eq, hqSum.tsum_eq] at hsum
  linarith

/-- A nonnegative summable mass with total zero has no positive atom. -/
theorem qStoppedCountable_nonneg_atom_eq_zero_of_hasSum_zero
    {Ω : Type*} [Countable Ω] (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hsum : HasSum f 0) :
    ∀ ω, f ω = 0 := by
  intro ω
  have hle := hsum.summable.sum_le_tsum ({ω}) (fun x hx ↦ hf x)
  rw [hsum.tsum_eq] at hle
  have hle' : f ω ≤ 0 := by simpa using hle
  exact le_antisymm hle' (hf ω)

/-- Support inclusion forces zero numerator mass on a zero-reference cell.
This is the endpoint fact needed before splitting a countable law into two
binary cells; it does not divide by either cell mass. -/
theorem qStoppedCountable_support_zero_reference_mass
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) (A B : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p A) (hqSum : HasSum q B)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0) (hB : B = 0) :
    A = 0 := by
  have hqSum0 : HasSum q 0 := by simpa [hB] using hqSum
  have hqatoms := qStoppedCountable_nonneg_atom_eq_zero_of_hasSum_zero q hq hqSum0
  have hpatoms : ∀ ω, p ω = 0 := by
    intro ω
    by_contra hp0
    exact (hsupport ω hp0) (hqatoms ω)
  have hptsum : (∑' ω, p ω) = 0 := by simp [hpatoms]
  rw [hpSum.tsum_eq] at hptsum
  exact hptsum

end StatisticalRL.QLearning.CountablePinsker
