import Formalization.Probability.EmpiricalVarianceBernstein

/-! Exact leave-one-out variance structure. No self-normalized probability
inequality is assumed or asserted. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]

private theorem sum_sq_sub_const {ι : Type*} (s : Finset ι) (x : ι → ℝ) (c : ℝ) :
    ∑ j ∈ s, (x j - c) ^ 2 =
      (∑ j ∈ s, x j ^ 2) - 2 * c * (∑ j ∈ s, x j) + (s.card : ℝ) * c ^ 2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Mean of the observations other than coordinate i, for N≥2. -/
noncomputable def leaveOneOutMean (N : ℕ) (_hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) (i : Fin N) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, V (ω j)) / ((N : ℝ) - 1)

/-- Minimum residual squared sum after removing coordinate i, normalized by N.
The denominator N is retained for comparison with the full empirical variance. -/
noncomputable def leaveOneOutResidual (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) (i : Fin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
    (V (ω j) - leaveOneOutMean N hN2 V ω i) ^ 2

/-- The exact removal decrement for the actual empirical frequency variance. -/
theorem empiricalVariance_sub_leaveOneOutResidual (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) (i : Fin N) :
    let hN : 0 < N := by omega
    empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i =
      (V (ω i) - (empiricalRow N hN ω).expectation V) ^ 2 / ((N : ℝ) - 1) := by
  intro hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hc : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hs : ∑ j ∈ Finset.univ.erase i, V (ω j) =
      (∑ j : Fin N, V (ω j)) - V (ω i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hsq : ∑ j ∈ Finset.univ.erase i, V (ω j) ^ 2 =
      (∑ j : Fin N, V (ω j) ^ 2) - V (ω i) ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  unfold leaveOneOutResidual
  rw [sum_sq_sub_const, hc]
  unfold leaveOneOutMean
  rw [hsq, hs]
  unfold empiricalVariance variance
  rw [empiricalRow_expectation, empiricalRow_expectation]
  field_simp
  ring

/-- Exact total leave-one-out decrement. -/
theorem sum_empiricalVariance_leaveOneOut_decrement (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) :
    let hN : 0 < N := by omega
    (∑ i : Fin N, (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i)) =
      (N : ℝ) / ((N : ℝ) - 1) * empiricalVariance N hN V ω := by
  intro hN
  simp_rw [empiricalVariance_sub_leaveOneOutResidual N hN2 V ω]
  rw [← Finset.sum_div]
  have hcenter := (empiricalRow N hN ω).variance_eq_expectation_centered_sq V
  rw [empiricalRow_expectation] at hcenter
  change empiricalVariance N hN V ω = _ at hcenter
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  rw [hcenter]
  field_simp

omit [Fintype State] in
/-- The deleted residual depends only on the other observations. -/
theorem leaveOneOutResidual_congr (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω ω' : Fin N → State) (i : Fin N)
    (h : ∀ j, j ≠ i → ω j = ω' j) :
    leaveOneOutResidual N hN2 V ω i = leaveOneOutResidual N hN2 V ω' i := by
  have hm : leaveOneOutMean N hN2 V ω i = leaveOneOutMean N hN2 V ω' i := by
    unfold leaveOneOutMean
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.mem_erase.mp hj).1]
  unfold leaveOneOutResidual
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_erase.mp hj).1]

omit [Fintype State] in
/-- Orthogonal decomposition proves the deleted mean minimizes the residual. -/
theorem leaveOneOutResidual_minimizes (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) (i : Fin N) (c : ℝ) :
    leaveOneOutResidual N hN2 V ω i ≤
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (V (ω j) - c) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hc : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have heq : (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (V (ω j) - c) ^ 2 =
      leaveOneOutResidual N hN2 V ω i +
        ((N : ℝ) - 1) / N * (c - leaveOneOutMean N hN2 V ω i) ^ 2 := by
    unfold leaveOneOutResidual
    rw [sum_sq_sub_const, sum_sq_sub_const, hc]
    unfold leaveOneOutMean
    field_simp
    ring
  rw [heq]
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hn1.le hn.le) (sq_nonneg _))

/-- Every deleted residual lies below the empirical variance. -/
theorem empiricalVariance_leaveOneOut_decrement_nonneg (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (ω : Fin N → State) (i : Fin N) :
    let hN : 0 < N := by omega
    0 ≤ empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i := by
  intro hN
  rw [empiricalVariance_sub_leaveOneOutResidual]
  apply div_nonneg (sq_nonneg _)
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  linarith

omit [Fintype State] in
/-- The mean after deleting one sample remains in the original interval. -/
theorem leaveOneOutMean_mem_Icc (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (ω : Fin N → State) (i : Fin N) :
    leaveOneOutMean N hN2 V ω i ∈ Set.Icc 0 B := by
  have hn1 : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hc : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  unfold leaveOneOutMean
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun j _ ↦ (hV (ω j)).1)) hn1.le
  · apply (div_le_iff₀ hn1).2
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, B :=
        Finset.sum_le_sum (fun j _ ↦ (hV (ω j)).2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hc]; ring

/-- Sharp range bound on a deleted-coordinate variance decrement. -/
theorem empiricalVariance_leaveOneOut_decrement_le_sharp (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (ω : Fin N → State) (i : Fin N) :
    let hN : 0 < N := by omega
    empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i ≤
      ((N : ℝ) - 1) / (N : ℝ) ^ 2 * B ^ 2 := by
  intro hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hn1 : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hm := leaveOneOutMean_mem_Icc N hN2 V B hV ω i
  have hsq : (V (ω i) - leaveOneOutMean N hN2 V ω i) ^ 2 ≤ B ^ 2 := by
    have hp : 0 ≤ (B - V (ω i) + leaveOneOutMean N hN2 V ω i) *
        (B + V (ω i) - leaveOneOutMean N hN2 V ω i) :=
      mul_nonneg (by linarith [(hV (ω i)).2, hm.1]) (by linarith [(hV (ω i)).1, hm.2])
    nlinarith
  have heq : empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i =
      ((N : ℝ) - 1) / (N : ℝ) ^ 2 *
        (V (ω i) - leaveOneOutMean N hN2 V ω i) ^ 2 := by
    rw [empiricalVariance_sub_leaveOneOutResidual]
    unfold leaveOneOutMean
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), empiricalRow_expectation]
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hsq (div_nonneg hn1.le (sq_nonneg _))

/-- The sharp quadratic self-bound scales as B²/N times empirical variance. -/
theorem sum_sq_empiricalVariance_leaveOneOut_decrement_le_sharp (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (ω : Fin N → State) :
    let hN : 0 < N := by omega
    (∑ i : Fin N, (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i) ^ 2) ≤
      B ^ 2 / (N : ℝ) * empiricalVariance N hN V ω := by
  intro hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hsum : (∑ i : Fin N,
      (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i) ^ 2) ≤
      (((N : ℝ) - 1) / (N : ℝ) ^ 2 * B ^ 2) * ∑ i : Fin N,
        (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h0 := empiricalVariance_leaveOneOut_decrement_nonneg N hN2 V ω i
    have hb := empiricalVariance_leaveOneOut_decrement_le_sharp N hN2 V B hV ω i
    nlinarith
  rw [sum_empiricalVariance_leaveOneOut_decrement] at hsum
  convert hsum using 1
  field_simp

end StatisticalRL.FiniteDistribution
