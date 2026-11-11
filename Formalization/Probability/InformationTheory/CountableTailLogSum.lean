import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Zero-safe countable tail log-sum inequality. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

/-- Zero-safe atomic KL term in `KL(p || q)` orientation. -/
noncomputable def klAtom (a b : ℝ) : ℝ :=
  if a = 0 then 0 else a * Real.log (a / b)

/-- A pointwise zero numerator contributes zero to the complete KL series. -/
theorem klSeries_eq_zero_of_left_eq_zero
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, p ω = 0) :
    (∑' ω, klAtom (p ω) (q ω)) = 0 := by
  simp [klAtom, hp]

/-- A nonnegative summable mass with total zero has no positive atoms. -/
theorem countable_nonneg_atom_eq_zero_of_hasSum_zero
    {Ω : Type*} [Countable Ω] (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hsum : HasSum f 0) :
    ∀ ω, f ω = 0 := by
  intro ω
  have hle := hsum.summable.sum_le_tsum ({ω}) (fun x hx ↦ hf x)
  rw [hsum.tsum_eq] at hle
  have hle' : f ω ≤ 0 := by simpa using hle
  exact le_antisymm hle' (hf ω)

/-- Absolute continuity forces a zero reference cell to have zero numerator
mass, when both countable cell laws are nonnegative and summable. -/
theorem countable_support_zero_reference_mass
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) (A B : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p A) (hqSum : HasSum q B)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0) (hB : B = 0) :
    A = 0 := by
  have hqSum0 : HasSum q 0 := by simpa [hB] using hqSum
  have hqatoms := countable_nonneg_atom_eq_zero_of_hasSum_zero q hq hqSum0
  have hpatoms : ∀ ω, p ω = 0 := by
    intro ω
    by_contra hp0
    exact (hsupport ω hp0) (hqatoms ω)
  have hptsum : (∑' ω, p ω) = 0 := by simp [hpatoms]
  rw [hpSum.tsum_eq] at hptsum
  exact hptsum

/-- Normalization identity for a positive atom. The second law may have
zero mass only off the first law's support. -/
theorem klAtom_normalize_identity
    (a b A B : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) :
    klAtom (a / A) (b / B) =
      klAtom a b / A - (a / A) * Real.log (A / B) := by
  have hratio : (a / A) / (b / B) = (a / b) / (A / B) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hA, ne_of_gt hB]
  have hlog := Real.log_div (div_ne_zero (ne_of_gt ha) (ne_of_gt hb))
    (div_ne_zero (ne_of_gt hA) (ne_of_gt hB))
  simp only [klAtom, if_neg (ne_of_gt (div_pos ha hA)), if_neg (ne_of_gt ha)]
  rw [hratio, hlog]
  field_simp [ne_of_gt hA]

/-- Absolute summability of the normalized KL series follows from absolute
summability of the original KL series and summability of the numerator law.
This is the convergence fact needed before the normalized Gibbs argument. -/
theorem klAtom_normalized_abs_summable
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) (A B : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p A) (hA : 0 < A) (hB : 0 < B)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |klAtom (p ω) (q ω)|)) :
    Summable (fun ω ↦ |klAtom (p ω / A) (q ω / B)|) := by
  have hfirst : Summable (fun ω ↦ |klAtom (p ω) (q ω)| * A⁻¹) :=
    hklAbs.mul_right A⁻¹
  have hsecond : Summable (fun ω ↦ p ω * (A⁻¹ * |Real.log (B / A)|)) :=
    hpSum.summable.mul_right _
  have hmajor : Summable (fun ω ↦
      |klAtom (p ω) (q ω)| / A + (p ω / A) * |Real.log (B / A)|) := by
    convert hfirst.add hsecond using 1 <;> ext ω <;>
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  apply Summable.of_norm_bounded hmajor
  intro ω
  simp only [Real.norm_eq_abs, abs_abs]
  by_cases hp0 : p ω = 0
  · simp [klAtom, hp0]
  · have hpPos : 0 < p ω := lt_of_le_of_ne (hp ω) (Ne.symm hp0)
    have hq0 := hsupport ω hp0
    have hqPos : 0 < q ω := lt_of_le_of_ne (hq ω) (Ne.symm hq0)
    rw [klAtom_normalize_identity (p ω) (q ω) A B hpPos hqPos hA hB]
    calc
      |klAtom (p ω) (q ω) / A - (p ω / A) * Real.log (A / B)|
          ≤ |klAtom (p ω) (q ω) / A| + |(p ω / A) * Real.log (A / B)| := abs_sub _ _
      _ = |klAtom (p ω) (q ω)| / A + (p ω / A) * |Real.log (B / A)| := by
        have hlogInv : Real.log (B / A) = -Real.log (A / B) := by
          rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA),
            Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
          ring
        rw [abs_div, abs_of_pos hA, abs_mul,
          abs_of_nonneg (div_nonneg (hp ω) hA.le), hlogInv, abs_neg]

/-- Countable Gibbs nonnegativity with explicit absolute summability. -/
theorem klSeries_nonneg_of_probability
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p 1) (hqSum : HasSum q 1)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |klAtom (p ω) (q ω)|)) :
    0 ≤ ∑' ω, klAtom (p ω) (q ω) := by
  have hkl : Summable (fun ω ↦ klAtom (p ω) (q ω)) := hklAbs.of_abs
  have hterm (ω : Ω) : p ω - q ω ≤ klAtom (p ω) (q ω) := by
    by_cases hp0 : p ω = 0
    · simpa [klAtom, hp0] using (neg_nonpos.mpr (hq ω))
    · have hpPos : 0 < p ω := lt_of_le_of_ne (hp ω) (Ne.symm hp0)
      have hq0 := hsupport ω hp0
      have hqPos : 0 < q ω := lt_of_le_of_ne (hq ω) (Ne.symm hq0)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqPos hpPos)
      have hlogQ : Real.log (q ω / p ω) = Real.log (q ω) - Real.log (p ω) :=
        Real.log_div (ne_of_gt hqPos) (ne_of_gt hpPos)
      have hlogP : Real.log (p ω / q ω) = Real.log (p ω) - Real.log (q ω) :=
        Real.log_div (ne_of_gt hpPos) (ne_of_gt hqPos)
      have hmul := mul_le_mul_of_nonneg_left hlog hpPos.le
      have hmul' : p ω * (Real.log (q ω) - Real.log (p ω)) ≤ q ω - p ω := by
        calc
          _ ≤ p ω * (q ω / p ω - 1) := by rw [← hlogQ]; exact hmul
          _ = q ω - p ω := by field_simp [ne_of_gt hpPos]
      rw [klAtom, if_neg hp0, hlogP]
      nlinarith [hmul']
  have hdiff : Summable (fun ω ↦ p ω - q ω) := hpSum.summable.sub hqSum.summable
  have hsum := hdiff.tsum_le_tsum hterm hkl
  rw [hpSum.summable.tsum_sub hqSum.summable,
    hpSum.tsum_eq, hqSum.tsum_eq] at hsum
  linarith

/-- Countable log-sum inequality on a positive-mass cell. The original KL
series is absolutely summable; the proof derives absolute summability of the
normalized conditional series from it and from numerator-mass summability. -/
theorem klSeries_logSum_of_pos
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) (A B : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p A) (hqSum : HasSum q B)
    (hA : 0 < A) (hB : 0 < B)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |klAtom (p ω) (q ω)|)) :
    klAtom A B ≤ ∑' ω, klAtom (p ω) (q ω) := by
  let pn : Ω → ℝ := fun ω ↦ p ω / A
  let qn : Ω → ℝ := fun ω ↦ q ω / B
  have hpnSum : HasSum pn 1 := by
    dsimp [pn]
    simpa [div_self (ne_of_gt hA)] using hpSum.div_const A
  have hqnSum : HasSum qn 1 := by
    dsimp [qn]
    simpa [div_self (ne_of_gt hB)] using hqSum.div_const B
  have hpn : ∀ ω, 0 ≤ pn ω := fun ω ↦ div_nonneg (hp ω) hA.le
  have hqn : ∀ ω, 0 ≤ qn ω := fun ω ↦ div_nonneg (hq ω) hB.le
  have hnormSupport : ∀ ω, pn ω ≠ 0 → qn ω ≠ 0 := by
    intro ω hpn0 hqn0
    have hp0 : p ω ≠ 0 := by
      intro hpz
      apply hpn0
      simp [pn, hpz]
    have hq0 := hsupport ω hp0
    apply hq0
    rcases (div_eq_zero_iff).mp hqn0 with hqz | hBz
    · exact hqz
    · exact False.elim ((ne_of_gt hB) hBz)
  have hnormAbs := klAtom_normalized_abs_summable p q A B hp hq hpSum hA hB
    hsupport hklAbs
  have hnormKL := klSeries_nonneg_of_probability pn qn hpn hqn hpnSum hqnSum
    hnormSupport hnormAbs
  have hkl : Summable (fun ω ↦ klAtom (p ω) (q ω)) := hklAbs.of_abs
  have hnorm : Summable (fun ω ↦ klAtom (pn ω) (qn ω)) := hnormAbs.of_abs
  have hpMul : Summable (fun ω ↦ p ω * Real.log (A / B)) :=
    hpSum.summable.mul_right _
  have hnormMul : Summable (fun ω ↦ A * klAtom (pn ω) (qn ω)) :=
    hnorm.mul_left A
  have hpoint (ω : Ω) :
      klAtom (p ω) (q ω) = A * klAtom (pn ω) (qn ω) +
        p ω * Real.log (A / B) := by
    by_cases hp0 : p ω = 0
    · simp [klAtom, pn, qn, hp0]
    · have hpPos : 0 < p ω := lt_of_le_of_ne (hp ω) (Ne.symm hp0)
      have hq0 := hsupport ω hp0
      have hqPos : 0 < q ω := lt_of_le_of_ne (hq ω) (Ne.symm hq0)
      have hratio : (p ω / A) / (q ω / B) = (p ω / q ω) / (A / B) := by
        field_simp [ne_of_gt hpPos, ne_of_gt hqPos, ne_of_gt hA, ne_of_gt hB]
      have hlog := Real.log_div (div_ne_zero (ne_of_gt hpPos) (ne_of_gt hqPos))
        (div_ne_zero (ne_of_gt hA) (ne_of_gt hB))
      have hpn0 : pn ω ≠ 0 := by
        dsimp [pn]
        exact div_ne_zero (ne_of_gt hpPos) (ne_of_gt hA)
      rw [klAtom, if_neg hp0, klAtom, if_neg hpn0, hratio, hlog]
      dsimp [pn, qn]
      field_simp [ne_of_gt hA, ne_of_gt hB]
      ring
  have hidentity :
      (∑' ω, klAtom (p ω) (q ω)) =
        A * (∑' ω, klAtom (pn ω) (qn ω)) + A * Real.log (A / B) := by
    calc
      _ = ∑' ω, (A * klAtom (pn ω) (qn ω) +
          p ω * Real.log (A / B)) := tsum_congr fun ω ↦ hpoint ω
      _ = (∑' ω, A * klAtom (pn ω) (qn ω)) +
          ∑' ω, p ω * Real.log (A / B) := hnormMul.tsum_add hpMul
      _ = A * (∑' ω, klAtom (pn ω) (qn ω)) +
          (∑' ω, p ω) * Real.log (A / B) := by
        rw [hnorm.tsum_mul_left A, hpSum.summable.tsum_mul_right]
      _ = A * (∑' ω, klAtom (pn ω) (qn ω)) + A * Real.log (A / B) := by
        rw [hpSum.tsum_eq]
  have hnonneg : 0 ≤ A * (∑' ω, klAtom (pn ω) (qn ω)) :=
    mul_nonneg hA.le hnormKL
  rw [klAtom, if_neg (ne_of_gt hA)]
  calc
    _ ≤ A * Real.log (A / B) + A * (∑' ω, klAtom (pn ω) (qn ω)) := by linarith
    _ = ∑' ω, klAtom (p ω) (q ω) := by rw [hidentity]; ring


/-- Zero-safe countable log-sum inequality. If the numerator cell has zero
mass, all its atoms vanish and both KL sides use the zero convention. If its
mass is positive, support inclusion forces positive reference mass and the
positive-cell theorem applies. -/
theorem klSeries_logSum
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) (A B : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p A) (hqSum : HasSum q B)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |klAtom (p ω) (q ω)|)) :
    klAtom A B ≤ ∑' ω, klAtom (p ω) (q ω) := by
  by_cases hAzero : A = 0
  · have hpSum0 : HasSum p 0 := by simpa [hAzero] using hpSum
    have hpatoms := countable_nonneg_atom_eq_zero_of_hasSum_zero p hp hpSum0
    have hklzero := klSeries_eq_zero_of_left_eq_zero p q hpatoms
    rw [klAtom, if_pos hAzero, hklzero]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hBne : B ≠ 0 := by
      intro hBzero
      have hAzero' := countable_support_zero_reference_mass p q A B hp hq
        hpSum hqSum hsupport hBzero
      exact hAzero hAzero'
    have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBne)
    exact klSeries_logSum_of_pos p q A B hp hq hpSum hqSum hApos hBpos
      hsupport hklAbs

end StatisticalRL.QLearning.CountablePinsker
