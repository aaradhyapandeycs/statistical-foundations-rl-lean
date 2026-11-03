import Formalization.Generative.PolicyEvaluationInverse
import Formalization.Generative.PolicyEvaluationVarianceResolvent
import Formalization.Generative.PolicyEvaluationHoeffding
import Formalization.Probability.BernsteinFamily

/-! Empirical/true policy-resolvent comparison for the fixed true variance vector. -/

open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance empiricalResolventStateDecidable : DecidableEq State := Classical.decEq State
local instance empiricalResolventStateMeasurable : MeasurableSpace State := ⊤

/-- The true-policy resolvent applied to the fixed true-value standard deviation. -/
noncomputable def trueVarianceResolvent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : State → ℝ :=
  (1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
    (fun s ↦ Real.sqrt (M.evaluationPolicyVariance π s))

/-- The same fixed vector evaluated through the actual sample-built resolvent. -/
noncomputable def empiricalVarianceResolvent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N) : State → ℝ :=
  (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
    (fun s ↦ Real.sqrt (M.evaluationPolicyVariance π s))

/-- Exact resolvent identity for arbitrary finite state vectors. -/
theorem empirical_true_resolvent_identity (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (f : State → ℝ) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f -
      (1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f =
    M.discount • ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
      ((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ
        ((1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f))) := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  let B : Matrix State State ℝ := 1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π
  have hA : IsUnit A := empiricalResolvent_isUnit M N hN data
  have hB : IsUnit B := M.evaluationPolicyResolvent_isUnit π
  have hd : B - A = M.discount • (empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) := by
    ext s t
    simp only [A, B, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  change A⁻¹ *ᵥ f - B⁻¹ *ᵥ f = M.discount • (A⁻¹ *ᵥ
    ((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ (B⁻¹ *ᵥ f)))
  rw [← Matrix.sub_mulVec, Matrix.inv_sub_inv (iff_of_true hA hB), hd]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.smul_mulVec]

/-- The empirical stochastic resolvent has sup-norm operator bound 1/(1−γ). -/
theorem empirical_resolvent_norm_le (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) (f : State → ℝ) :
    ‖(1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f‖ ≤
      ‖f‖ / (1 - M.discount) := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  letI : Invertible A := (empiricalResolvent_isUnit M N hN data).invertible
  let u := A⁻¹ *ᵥ f
  have hu : A *ᵥ u = f := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hbound : ‖u‖ ≤ ‖f‖ + M.discount * ‖u‖ := by
    have hc : 0 ≤ ‖f‖ + M.discount * ‖u‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg M.discount_nonneg (norm_nonneg _))
    apply (pi_norm_le_iff_of_nonneg hc).2
    intro s
    have he := congrFun hu s
    simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, empiricalMatrix_mulVec] at he
    have hrow := (empiricalPolicyRow N hN data s).abs_expectation_le
      (f := u) (c := ‖u‖) (fun t ↦ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u t)
    rw [Real.norm_eq_abs]
    have hid : u s = f s + M.discount * (empiricalPolicyRow N hN data s).expectation u := by linarith
    rw [hid]
    calc
      _ ≤ |f s| + M.discount * |(empiricalPolicyRow N hN data s).expectation u| := by
        simpa [abs_mul, abs_of_nonneg M.discount_nonneg] using
          abs_add_le (f s) (M.discount * (empiricalPolicyRow N hN data s).expectation u)
      _ ≤ ‖f‖ + M.discount * ‖u‖ := add_le_add
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm f s)
        (mul_le_mul_of_nonneg_left hrow M.discount_nonneg)
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  change ‖u‖ ≤ ‖f‖ / (1 - M.discount)
  apply (le_div_iff₀ hd).2
  nlinarith only [hbound]

/-- Deterministic comparison in terms of the actual true-resolvent residual. -/
theorem empirical_true_resolvent_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (f : State → ℝ) :
    ‖(1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f -
      (1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f‖ ≤
      M.discount / (1 - M.discount) *
        ‖(empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ
          ((1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f)‖ := by
  rw [empirical_true_resolvent_identity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg M.discount_nonneg]
  have h := empirical_resolvent_norm_le M N hN data
    ((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ
      ((1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f))
  calc
    _ ≤ M.discount * (‖(empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ
      ((1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f)‖ /
        (1 - M.discount)) := mul_le_mul_of_nonneg_left h M.discount_nonneg
    _ = _ := by ring


/-- The true-resolvent standard-deviation vector is nonnegative for positive γ. -/
theorem trueVarianceResolvent_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hγ : 0 < M.discount) (s : State) :
    0 ≤ trueVarianceResolvent M π s := by
  have h := M.evaluationPolicyResolvent_sqrtVariance_scaled π s
  have hn := (M.discountedPolicySqrtVarianceBudget_bounds π s).1
  change M.discount * trueVarianceResolvent M π s = _ at h
  nlinarith only [hγ, h, hn]

/-- At zero discount the empirical and true resolvents are identical. -/
theorem empirical_true_resolvent_eq_of_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (f : State → ℝ) (hγ : M.discount = 0) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f =
      (1 - M.discount • DiscountedMDP.evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f := by
  simp [hγ]

/-- Source Bernstein radius for the fixed first auxiliary value at each state. -/
noncomputable def trueVarianceResolventBernsteinRadius (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (δ : ℝ) : State → ℝ := fun s ↦
  (M.policyTransition π s).bernsteinRadius N 1 (δ / Fintype.card State)
    (trueVarianceResolvent M π)

/-- The source's literal rowwise logarithmic radius for this fixed vector. -/
theorem trueVarianceResolventBernsteinRadius_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (δ : ℝ) (s : State) :
    trueVarianceResolventBernsteinRadius M π N δ s =
      Real.sqrt (2 * Real.log (4 * Fintype.card State / δ) / N) *
        Real.sqrt ((M.policyTransition π s).variance (trueVarianceResolvent M π)) +
      2 * ‖trueVarianceResolvent M π‖ * Real.log (4 * Fintype.card State / δ) / (3 * N) := by
  letI : Nonempty State := M.state_nonempty
  have hs : (Fintype.card State : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold trueVarianceResolventBernsteinRadius
  rw [FiniteDistribution.bernsteinRadius_eq_source]
  have hlog : 4 * (1 : ℕ) / (δ / Fintype.card State) =
      4 * Fintype.card State / δ := by
    field_simp
    norm_num
  rw [hlog]

/-- Fixed-vector Bernstein control under the actual policy-row sample law,
without any cross-event independence assumption. -/
theorem trueVarianceResolvent_residual_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < M.discount) :
    1 - δ < (samplingLaw M π N).real {data | ∀ s,
      |((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ
        trueVarianceResolvent M π) s| ≤ trueVarianceResolventBernsteinRadius M π N δ s} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let μ := samplingLaw M π N
  let V := trueVarianceResolvent M π
  let m : ℝ := Fintype.card State
  let η : ℝ := δ / m
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; rw [div_lt_iff₀ hm]; linarith
  have hV (s : State) : 0 ≤ V s := trueVarianceResolvent_nonneg M π hγ s
  let bad (s : State) : Set (Samples State N) := {data |
    trueVarianceResolventBernsteinRadius M π N δ s <
      |(empiricalPolicyRow N hN data s).expectation V - (M.policyTransition π s).expectation V|}
  have hbad (s : State) : μ.real (bad s) < η := by
    let d := M.policyTransition π s
    let F : Finset (State → ℝ) := {V}
    have hF : ∀ v ∈ F, ∀ t, 0 ≤ v t := by simpa [F] using hV
    have hs := d.empiricalRow_bernsteinFamily_success_gt N hN F η hη hη1 hF
    let E : Set (Fin N → State) := {ω |
      d.bernsteinRadius N 1 η V < |(FiniteDistribution.empiricalRow N hN ω).expectation V - d.expectation V|}
    have hE : MeasurableSet E := (Set.to_countable _).measurableSet
    have heq : Eᶜ = {ω | ∀ v ∈ F,
      |(FiniteDistribution.empiricalRow N hN ω).expectation v - d.expectation v| ≤
        d.bernsteinRadius N F.card η v} := by
      ext ω
      simp [E, F, not_lt]
    have hc := measureReal_compl (μ := d.sampleMeasure N) hE
    rw [heq, probReal_univ] at hc
    have ht : (d.sampleMeasure N).real E < η := by linarith
    rw [← samplingLaw_stateRow M π N s, measureReal_def,
      Measure.map_apply (measurable_of_countable _) hE] at ht
    change μ.real (bad s) < η at ht
    exact ht
  have hbadall : μ.real (⋃ s : State, bad s) < δ := by
    have hi : (Finset.univ : Finset State).Nonempty := Finset.univ_nonempty
    calc
      _ ≤ ∑ s : State, μ.real (bad s) := measureReal_iUnion_fintype_le _
      _ < ∑ _s : State, η := Finset.sum_lt_sum_of_nonempty hi (fun s _ ↦ hbad s)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change m * η = δ
        dsimp [η]
        field_simp
  have heq : (⋃ s : State, bad s)ᶜ = {data | ∀ s,
      |((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ V) s| ≤
        trueVarianceResolventBernsteinRadius M π N δ s} := by
    ext data
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists, not_lt, Set.mem_setOf_eq,
      Matrix.sub_mulVec, Pi.sub_apply, empiricalMatrix_mulVec,
      DiscountedMDP.evaluationPolicyMatrix_mulVec, bad]
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ s : State, bad s)).measurableSet)
  rw [heq, probReal_univ] at hc
  change 1 - δ < μ.real {data | ∀ s,
      |((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ V) s| ≤
        trueVarianceResolventBernsteinRadius M π N δ s}
  linarith

/-- The actual high-probability empirical-vs-true resolvent comparison,
with the explicit source Bernstein radius for the fixed auxiliary value. -/
theorem empirical_true_varianceResolvent_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < M.discount) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖empiricalVarianceResolvent M π N hN data - trueVarianceResolvent M π‖ ≤
        M.discount / (1 - M.discount) * ‖trueVarianceResolventBernsteinRadius M π N δ‖} := by
  let μ := samplingLaw M π N
  let V := trueVarianceResolvent M π
  let R := trueVarianceResolventBernsteinRadius M π N δ
  let good₁ : Set (Samples State N) := {data | ∀ s,
    |((empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ V) s| ≤ R s}
  let good₂ : Set (Samples State N) := {data |
    ‖empiricalVarianceResolvent M π N hN data - V‖ ≤ M.discount / (1 - M.discount) * ‖R‖}
  have hs : 1 - δ < μ.real good₁ := trueVarianceResolvent_residual_bernstein M π N hN δ hδ hδ1 hγ
  have hsub : good₁ ⊆ good₂ := by
    intro data hd
    have hr : ‖(empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ V‖ ≤ ‖R‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
      intro s
      rw [Real.norm_eq_abs]
      exact (hd s).trans ((le_abs_self (R s)).trans (by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm R s))
    have hc : 0 ≤ M.discount / (1 - M.discount) :=
      div_nonneg M.discount_nonneg (sub_nonneg.mpr M.discount_lt_one.le)
    calc
      _ ≤ M.discount / (1 - M.discount) *
          ‖(empiricalMatrix N hN data - DiscountedMDP.evaluationPolicyMatrix M π) *ᵥ V‖ :=
        empirical_true_resolvent_norm_le M π N hN data _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr hc
  have hm := measureReal_mono hsub (measure_ne_top μ good₂)
  change 1 - δ < μ.real good₂
  linarith


/-- A source-style bound on the empirical resolvent itself: the true
resolvent contribution is controlled by the proved variance budget, and the
remaining higher-order Bernstein radius is explicit. -/
theorem empirical_varianceResolvent_scaled_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < M.discount) :
    1 - δ < (samplingLaw M π N).real {data |
      M.discount * ‖empiricalVarianceResolvent M π N hN data‖ ≤
        ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) +
          (M.discount ^ 2 / (1 - M.discount)) *
            ‖trueVarianceResolventBernsteinRadius M π N δ‖} := by
  let μ := samplingLaw M π N
  let V := trueVarianceResolvent M π
  let R := trueVarianceResolventBernsteinRadius M π N δ
  let good₁ : Set (Samples State N) := {data |
    ‖empiricalVarianceResolvent M π N hN data - V‖ ≤ M.discount / (1 - M.discount) * ‖R‖}
  let good₂ : Set (Samples State N) := {data |
    M.discount * ‖empiricalVarianceResolvent M π N hN data‖ ≤
      ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) +
        (M.discount ^ 2 / (1 - M.discount)) * ‖R‖}
  have hs : 1 - δ < μ.real good₁ :=
    empirical_true_varianceResolvent_bernstein M π N hN δ hδ hδ1 hγ
  have htrue := M.evaluationPolicyResolvent_sqrtVariance_bound π
  change M.discount * ‖V‖ ≤ ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) at htrue
  have hsub : good₁ ⊆ good₂ := by
    intro data hd
    have htri : ‖empiricalVarianceResolvent M π N hN data‖ ≤
        ‖empiricalVarianceResolvent M π N hN data - V‖ + ‖V‖ := by
      calc
        _ = ‖(empiricalVarianceResolvent M π N hN data - V) + V‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hmul := mul_le_mul_of_nonneg_left htri M.discount_nonneg
    have hres := mul_le_mul_of_nonneg_left hd M.discount_nonneg
    have hid : M.discount * (M.discount / (1 - M.discount) * ‖R‖) =
        (M.discount ^ 2 / (1 - M.discount)) * ‖R‖ := by ring
    change M.discount * ‖empiricalVarianceResolvent M π N hN data‖ ≤ _
    nlinarith only [hmul, hres, htrue, hid]
  have hm := measureReal_mono hsub (measure_ne_top μ good₂)
  change 1 - δ < μ.real good₂
  linarith

end StatisticalRL.ModelBasedPolicyEvaluation
