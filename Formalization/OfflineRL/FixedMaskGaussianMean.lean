import Formalization.Probability.GaussianSubgaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-! Fixed-action-vector Gaussian arm-mean confidence bound.

Source: `chapters/offlineRL.tex:243–260, 322–334, 400–403, 427–443, 524–556`.
For a fixed action vector, the independent Gaussian noises on a positively sampled
arm satisfy the stated mean bound. Random action vectors, their counts, and the
union over arms are handled by separate declarations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatisticalRL.OfflineRL

/-- Fixed-mask arm-mean bound for independent standard Gaussian noise on an
arbitrary probability space. -/
theorem fixedMask_gaussianMean_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Act : Type*} [Fintype Act] [DecidableEq Act]
    (n : ℕ) (Z : Fin n → Ω → ℝ) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ)
    (a : Fin n → Act) (b : Act)
    (hb : 0 < (Finset.univ.filter (fun i => a i = b)).card)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Real.sqrt (2 * Real.log (4 * Fintype.card Act / δ) /
          (Finset.univ.filter (fun i => a i = b)).card) <
        |(∑ i ∈ Finset.univ.filter (fun i => a i = b), Z i ω) /
          (Finset.univ.filter (fun i => a i = b)).card|} ≤
      δ / (2 * Fintype.card Act) := by
  set s := Finset.univ.filter (fun i => a i = b) with hs
  set k : ℝ := (s.card : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast hb
  have hA : (0 : ℝ) < Fintype.card Act := by
    have : 0 < Fintype.card Act := Fintype.card_pos_iff.mpr ⟨b⟩
    exact_mod_cast this
  set L := Real.log (4 * Fintype.card Act / δ) with hL
  have hratio : 1 < 4 * (Fintype.card Act : ℝ) / δ := by
    rw [lt_div_iff₀ hδ]
    have : (1 : ℝ) ≤ Fintype.card Act := by
      have : 0 < Fintype.card Act := Fintype.card_pos_iff.mpr ⟨b⟩
      exact_mod_cast this
    linarith
  have hL0 : 0 < L := Real.log_pos hratio
  set ε := Real.sqrt (2 * L / k) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  -- Each noise coordinate is 1-sub-Gaussian with mean zero.
  have hsub : ∀ i, HasSubgaussianMGF (Z i) 1 μ := by
    intro i
    simpa using hasSubgaussianMGF_sub_of_hasLaw_gaussianReal μ (Z i) 0 (hlaw i)
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hind (s := s) (fun i _ => hsub i)
  have hM := hS.const_mul (1 / k)
  set c : ℝ≥0 := ⟨(1 / k) ^ 2, sq_nonneg _⟩ * ∑ i ∈ s, (1 : ℝ≥0) with hc
  have hcR : (c : ℝ) = 1 / k := by
    rw [hc, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_sum]
    simp only [NNReal.coe_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hk]
    field_simp
  have hexp : Real.exp (-ε ^ 2 / (2 * (c : ℝ))) = δ / (4 * Fintype.card Act) := by
    rw [hcR, hε, Real.sq_sqrt (by positivity)]
    have : -(2 * L / k) / (2 * (1 / k)) = -L := by field_simp
    rw [this, Real.exp_neg, hL, Real.exp_log (by positivity)]
    field_simp
  have hup := hM.measure_ge_le hε0
  have hlo := hM.neg.measure_ge_le hε0
  rw [hexp] at hup hlo
  have hsubset : {ω | ε < |(∑ i ∈ s, Z i ω) / k|} ⊆
      {ω | ε ≤ 1 / k * ∑ i ∈ s, Z i ω} ∪ {ω | ε ≤ (-(fun ω => 1 / k * ∑ i ∈ s, Z i ω)) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, Pi.neg_apply]
    have he : (∑ i ∈ s, Z i ω) / k = 1 / k * ∑ i ∈ s, Z i ω := by ring
    rw [he] at hω
    by_contra hcon
    push_neg at hcon
    have : |1 / k * ∑ i ∈ s, Z i ω| < ε := abs_lt.mpr ⟨by linarith [hcon.2], hcon.1⟩
    linarith
  calc μ.real {ω | ε < |(∑ i ∈ s, Z i ω) / k|}
      ≤ μ.real ({ω | ε ≤ 1 / k * ∑ i ∈ s, Z i ω} ∪
          {ω | ε ≤ (-(fun ω => 1 / k * ∑ i ∈ s, Z i ω)) ω}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | ε ≤ 1 / k * ∑ i ∈ s, Z i ω} +
          μ.real {ω | ε ≤ (-(fun ω => 1 / k * ∑ i ∈ s, Z i ω)) ω} := measureReal_union_le _ _
    _ ≤ δ / (4 * Fintype.card Act) + δ / (4 * Fintype.card Act) := add_le_add hup hlo
    _ = δ / (2 * Fintype.card Act) := by field_simp; ring

/-- The same bound on the actual Gaussian product law: noise vector
`z ~ ⊗ᵢ N(0,1)` on `Fin n → ℝ`, coordinates as the noise variables. -/
theorem fixedMask_gaussianMean_tail_pi
    {Act : Type*} [Fintype Act] [DecidableEq Act]
    (n : ℕ) (a : Fin n → Act) (b : Act)
    (hb : 0 < (Finset.univ.filter (fun i => a i = b)).card)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {z : Fin n → ℝ | Real.sqrt (2 * Real.log (4 * Fintype.card Act / δ) /
          (Finset.univ.filter (fun i => a i = b)).card) <
        |(∑ i ∈ Finset.univ.filter (fun i => a i = b), z i) /
          (Finset.univ.filter (fun i => a i = b)).card|} ≤
      δ / (2 * Fintype.card Act) := by
  have hind : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hlaw : ∀ i : Fin n, HasLaw (fun z : Fin n → ℝ => z i) (gaussianReal 0 1)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    fun i => (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).hasLaw
  have h := fixedMask_gaussianMean_tail (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) n
    (fun i z => z i) hind hlaw a b hb δ hδ hδ1
  exact h

end StatisticalRL.OfflineRL
