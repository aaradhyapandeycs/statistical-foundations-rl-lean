import Formalization.Generative.ModelBasedPolicyEvaluation
import Formalization.Probability.EmpiricalHoeffdingFamily
import Formalization.Generative.PolicyEvaluationPerturbation

/-! A conservative finite-sample policy-evaluation bound from Hoeffding. -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance hoeffdingEvalStateMeasurable : MeasurableSpace State := ⊤

/-- The true MDP after averaging its reward and transitions under the fixed policy. -/
noncomputable def policyCollapsedModel (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := fun s _ ↦ M.policyTransition π s
  reward := fun s _ ↦ (π s).expectation (M.reward s)
  reward_nonneg := by intro s a; exact (π s).expectation_nonneg (M.reward_nonneg s)
  reward_le_one := by intro s a; exact (π s).expectation_le_const (M.reward_le_one s)
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- The collapsed model has exactly the original policy Bellman operator. -/
theorem policyCollapsedModel_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) :
    (policyCollapsedModel M π).valueBellman π V = M.valueBellman π V := by
  funext s
  change (π s).expectation (fun _ ↦ (π s).expectation (M.reward s)) +
    M.discount * ((π s).bind (fun _ ↦ M.policyTransition π s)).expectation V = _
  rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_bind,
    FiniteDistribution.expectation_const]
  rfl

/-- Its actual trajectory value is the original true policy value. -/
theorem policyCollapsedModel_trajectoryValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    (policyCollapsedModel M π).trajectoryExpectedValue π = M.trajectoryExpectedValue π := by
  rw [(policyCollapsedModel M π).trajectoryExpectedValue_eq_valueFixedPoint,
    M.trajectoryExpectedValue_eq_valueFixedPoint]
  apply (M.valueFixedPoint_characterization π _).mp
  rw [← policyCollapsedModel_bellman]
  exact (policyCollapsedModel M π).valueFixedPoint_spec π

/-- The direct algorithm's empirical value has the deterministic error bound
for its actual policy-row residual on the original true trajectory value. -/
theorem valueEstimator_perturbation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hres : ∀ s, |(empiricalPolicyRow N hN data s).expectation (M.trajectoryExpectedValue π) -
      (M.policyTransition π s).expectation (M.trajectoryExpectedValue π)| ≤ ε) :
    ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
      M.discount * ε / (1 - M.discount) := by
  let C := policyCollapsedModel M π
  let H := empiricalModel M π N hN data
  have hr : H.reward = C.reward := rfl
  have hg : H.discount = C.discount := rfl
  have hC : C.trajectoryExpectedValue π = M.trajectoryExpectedValue π :=
    policyCollapsedModel_trajectoryValue M π
  have hR (s : State) : DiscountedMDP.policyValueResidual C H π s =
      (empiricalPolicyRow N hN data s).expectation (M.trajectoryExpectedValue π) -
        (M.policyTransition π s).expectation (M.trajectoryExpectedValue π) := by
    unfold DiscountedMDP.policyValueResidual
    rw [hC]
    change ((π s).bind (fun _ ↦ empiricalPolicyRow N hN data s)).expectation _ -
      ((π s).bind (fun _ ↦ M.policyTransition π s)).expectation _ = _
    rw [FiniteDistribution.expectation_bind, FiniteDistribution.expectation_const,
      FiniteDistribution.expectation_bind, FiniteDistribution.expectation_const]
  have hb := DiscountedMDP.trajectoryValue_perturbation_bound_of_residual C H π hr hg ε hε
    (fun s ↦ by rw [hR]; exact hres s)
  change ‖H.trajectoryExpectedValue π - C.trajectoryExpectedValue π‖ ≤
    M.discount * ε / (1 - M.discount) at hb
  rw [hC, ← valueEstimator_eq_trajectory] at hb
  exact hb

/-- Every state's sample vector has the policy row's actual iid product law. -/
theorem samplingLaw_stateRow (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (s : State) :
    (samplingLaw M π N).map (fun data i ↦ data (s,i)) =
      (M.policyTransition π s).sampleMeasure N := by
  let f : Fin N → State × Fin N := fun i ↦ (s,i)
  have hf : Function.Injective f := by intro i j h; exact Prod.mk.inj h |>.2
  have hind := (samplingLaw_independent M π N).precomp hf
  have hm : ∀ i : Fin N, AEMeasurable (fun data : Samples State N ↦ data (s,i)) (samplingLaw M π N) :=
    fun i ↦ (measurable_pi_apply (s,i)).aemeasurable
  rw [(iIndepFun_iff_map_fun_eq_pi_map hm).mp hind]
  unfold FiniteDistribution.sampleMeasure
  congr 1
  funext i
  exact samplingLaw_marginal M π N (s,i)


/-- One-vector Hoeffding radius with a statewise union-bound allocation. -/
noncomputable def policyHoeffdingRadius (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (δ : ℝ) : ℝ :=
  FiniteDistribution.familyRadius N 1 (δ / Fintype.card State) (M.trajectoryExpectedValue π)

/-- Explicit source-Hoeffding radius, including the S factor from the union. -/
theorem policyHoeffdingRadius_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (δ : ℝ) :
    policyHoeffdingRadius M π N δ = ‖M.trajectoryExpectedValue π‖ *
      Real.sqrt (Real.log (2 * Fintype.card State / δ) / (2 * N)) := by
  letI : Nonempty State := M.state_nonempty
  have hs : (Fintype.card State : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold policyHoeffdingRadius FiniteDistribution.familyRadius
  congr 1
  congr 1
  congr 1
  field_simp
  norm_num

/-- Hoeffding control for the actual sample experiment and the direct policy
value estimator. The source's singleton-family radius is used exactly. -/
theorem valueEstimator_hoeffding (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        M.discount * policyHoeffdingRadius M π N δ / (1 - M.discount)} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let μ := samplingLaw M π N
  let V := M.trajectoryExpectedValue π
  let m : ℝ := Fintype.card State
  let η : ℝ := δ / m
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; rw [div_lt_iff₀ hm]; linarith
  have hV (s : State) : 0 ≤ V s := (M.trajectoryExpectedValue_bounds π s).1
  let R : ℝ := policyHoeffdingRadius M π N δ
  have hR : 0 ≤ R := FiniteDistribution.familyRadius_nonneg _ _ _ _
  let bad (s : State) : Set (Samples State N) := {data |
    R < |(empiricalPolicyRow N hN data s).expectation V - (M.policyTransition π s).expectation V|}
  have hbad (s : State) : μ.real (bad s) < η := by
    let d := M.policyTransition π s
    have ht := d.familyViolation_lt N 1 hN (by norm_num) η hη hη1 V hV
    have hmeas : MeasurableSet (d.familyViolation N hN 1 η V) :=
      (Set.to_countable _).measurableSet
    rw [← samplingLaw_stateRow M π N s, measureReal_def,
      Measure.map_apply (measurable_of_countable _) hmeas] at ht
    simp only [Nat.cast_one, div_one] at ht
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
  let good : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - V‖ ≤ M.discount * R / (1 - M.discount)}
  have hsub : (⋃ s : State, bad s)ᶜ ⊆ good := by
    intro data hd
    have hrs (s : State) : |(empiricalPolicyRow N hN data s).expectation V -
        (M.policyTransition π s).expectation V| ≤ R := by
      have : data ∉ bad s := by
        intro hs
        exact hd (Set.mem_iUnion.mpr ⟨s, hs⟩)
      exact not_lt.mp this
    exact valueEstimator_perturbation M π N hN data R hR hrs
  have hmono : μ.real ((⋃ s : State, bad s)ᶜ) ≤ μ.real good :=
    measureReal_mono hsub (measure_ne_top μ _)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ s : State, bad s)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ < μ.real good
  linarith


/-- The true trajectory value has the usual uniform geometric bound. -/
theorem truePolicyValue_norm_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ‖M.trajectoryExpectedValue π‖ ≤ 1 / (1 - M.discount) := by
  have hpos : 0 ≤ 1 / (1 - M.discount) :=
    div_nonneg zero_le_one (sub_nonneg.mpr M.discount_lt_one.le)
  apply (pi_norm_le_iff_of_nonneg hpos).2
  intro s
  have hv := M.trajectoryExpectedValue_bounds π s
  rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
  exact hv.2

/-- A bound with no unknown true-value norm. -/
theorem valueEstimator_hoeffding_uniform (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        M.discount / (1 - M.discount) ^ 2 *
          Real.sqrt (Real.log (2 * Fintype.card State / δ) / (2 * N))} := by
  let μ := samplingLaw M π N
  let V := M.trajectoryExpectedValue π
  let q := Real.sqrt (Real.log (2 * Fintype.card State / δ) / (2 * N))
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hr : policyHoeffdingRadius M π N δ ≤ (1 / (1 - M.discount)) * q := by
    rw [policyHoeffdingRadius_eq]
    exact mul_le_mul_of_nonneg_right (truePolicyValue_norm_bound M π) (Real.sqrt_nonneg _)
  have hcoeff : M.discount * policyHoeffdingRadius M π N δ / (1 - M.discount) ≤
      M.discount / (1 - M.discount) ^ 2 * q := by
    calc
      _ ≤ M.discount * ((1 / (1 - M.discount)) * q) / (1 - M.discount) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr M.discount_nonneg) hd.le
      _ = _ := by field_simp
  let good₁ : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - V‖ ≤ M.discount * policyHoeffdingRadius M π N δ / (1 - M.discount)}
  let good₂ : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - V‖ ≤ M.discount / (1 - M.discount) ^ 2 * q}
  have hs : 1 - δ < μ.real good₁ := valueEstimator_hoeffding M π N hN δ hδ hδ1
  have hsub : good₁ ⊆ good₂ := by intro data hd; exact hd.trans hcoeff
  have hm := measureReal_mono hsub (measure_ne_top μ good₂)
  change 1 - δ < μ.real good₂
  linarith

/-- An explicit conservative sufficient sample size. Its fourth power of the
horizon is weaker than the sharp source policy-evaluation theorem. -/
theorem valueEstimator_hoeffding_sample_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hNbound : Real.log (2 * Fintype.card State / δ) /
      (2 * ε ^ 2 * (1 - M.discount) ^ 4) ≤ N) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ ε} := by
  let μ := samplingLaw M π N
  let V := M.trajectoryExpectedValue π
  let d : ℝ := 1 - M.discount
  let L : ℝ := Real.log (2 * Fintype.card State / δ)
  have hd : 0 < d := sub_pos.mpr M.discount_lt_one
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 2 * ε ^ 2 * d ^ 4 := by positivity
  have hh : L ≤ (N : ℝ) * (2 * ε ^ 2 * d ^ 4) :=
    (div_le_iff₀ hden).mp hNbound
  have hsquare : L / (2 * N) ≤ (ε * d ^ 2) ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).2
    calc
      L ≤ (N : ℝ) * (2 * ε ^ 2 * d ^ 4) := hh
      _ = (ε * d ^ 2) ^ 2 * (2 * N) := by ring
  have hroot : Real.sqrt (L / (2 * N)) ≤ ε * d ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsquare⟩
  have hcoef : 0 ≤ M.discount / d ^ 2 := div_nonneg M.discount_nonneg (sq_nonneg d)
  have hbound : M.discount / d ^ 2 * Real.sqrt (L / (2 * N)) ≤ ε := by
    calc
      _ ≤ M.discount / d ^ 2 * (ε * d ^ 2) := mul_le_mul_of_nonneg_left hroot hcoef
      _ = M.discount * ε := by field_simp
      _ ≤ ε := by nlinarith [M.discount_lt_one]
  let good₁ : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - V‖ ≤ M.discount / d ^ 2 * Real.sqrt (L / (2 * N))}
  let good₂ : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - V‖ ≤ ε}
  have hs : 1 - δ < μ.real good₁ := valueEstimator_hoeffding_uniform M π N hN δ hδ hδ1
  have hsub : good₁ ⊆ good₂ := by intro data hd; exact hd.trans hbound
  have hm := measureReal_mono hsub (measure_ne_top μ good₂)
  change 1 - δ < μ.real good₂
  linarith

end StatisticalRL.ModelBasedPolicyEvaluation
