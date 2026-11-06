import Formalization.Generative.GenerativeLowerBoundQMixtureFinalDeterministic

/-! Baseline-versus-mixture deterministic Q-risk for every positive action count.

`qMixtureSource_deterministic_Q_risk` assumes `2 ≤ A`; its only use of that premise is the
cardinality inequality `qMixture_log_card_lower`, which holds for `1 ≤ A`. This module
restates both for `1 ≤ A` (new declarations; the reviewed ones are unchanged). -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance qAnyActionState (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance qAnyActionAction (A : ℕ) : MeasurableSpace (Fin A) := ⊤

/-- `log((m+1)A) ≤ 2 log(mA+1)` for all `m, A ≥ 1`. -/
theorem qMixture_log_card_lower_of_pos (m A : ℕ) (hm : 1 ≤ m) (hA : 1 ≤ A) :
    Real.log (((m + 1) * A : ℕ) : ℝ) ≤ 2 * Real.log ((m * A + 1 : ℕ) : ℝ) := by
  have hS : (((m + 1) * A : ℕ) : ℝ) ≤ ((m * A + 1 : ℕ) : ℝ) ^ 2 := by
    have hmA : A ≤ m * A := by nlinarith [Nat.mul_le_mul_right A hm]
    have hnat : (m + 1) * A ≤ (m * A + 1) ^ 2 := by
      nlinarith [Nat.zero_le ((m * A) ^ 2)]
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < (((m + 1) * A : ℕ) : ℝ) := by
    have : 0 < (m + 1) * A := Nat.mul_pos (Nat.succ_pos m) hA
    exact_mod_cast this
  have hlog := Real.log_le_log hpos hS
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- The corrected deterministic Q-estimator lower bound of
`qMixtureSource_deterministic_Q_risk` for every positive action count, including `A = 1`.
The proof is the same argument; only the cardinality inequality is replaced by
`qMixture_log_card_lower_of_pos`. -/
theorem qMixtureSource_deterministic_Q_risk_of_pos {m A : ℕ} (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hsize : 16 ≤ (m + 1) * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((m + 1) * A))
    (estimate : Samples (Option (Fin m)) (Fin A) N → Option (Fin m) → Fin A → ℝ) :
    letI : NeZero A := ⟨by omega⟩
    ∃ i : QMixtureIndex m A,
      let M := qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 4 ≤ (samplingLaw M N).real
        {data | ε < ‖estimate data - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero A := ⟨by omega⟩
  let Θ := Fin m × Fin A
  let Ω := QMixtureActiveCoordinates m A N → Bool
  haveI : Nonempty Θ := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p : ℝ≥0 := ⟨baseProbability γ, by linarith [ha.1]⟩
  let q : ℝ≥0 := ⟨baseProbability γ + probabilityIncrement γ ε, by linarith [ha.1, ha.2.1]⟩
  have hp : 0 < p := by change 0 < baseProbability γ; linarith [ha.1]
  have hp1 : p < 1 := by exact_mod_cast (show baseProbability γ < 1 by linarith [ha.2.1, ha.2.2.1])
  have hpq : p ≤ q := by change baseProbability γ ≤ baseProbability γ + probabilityIncrement γ ε; linarith [ha.2.1]
  have hq : q < 1 := by exact_mod_cast ha.2.2.1
  let μ₀ : Measure Ω := qMixtureActiveBaseline p q hp1.le hq.le
  let P (θ : Θ) : Measure Ω := qMixtureActiveAlternative p q hp1.le hq.le θ
  let mix : Measure Ω := qMixtureActiveLaw p q hp1.le hq.le
  haveI : IsProbabilityMeasure μ₀ := by dsimp [μ₀]; infer_instance
  haveI (θ : Θ) : IsProbabilityMeasure (P θ) := by dsimp [P]; infer_instance
  haveI : IsProbabilityMeasure mix := by dsimp [mix]; infer_instance
  let d : ℝ := ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))
  have hd : 0 ≤ d := by
    have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
    have hpReal1 : (p : ℝ) < 1 := by exact_mod_cast hp1
    change 0 ≤ ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))
    exact div_nonneg (sq_nonneg _) (mul_nonneg hpReal.le (sub_nonneg.mpr hpReal1.le))
  have hdBound : d ≤ 256 * (1 - γ) ^ 3 * ε ^ 2 := by
    dsimp [d, p, q]
    change (baseProbability γ + probabilityIncrement γ ε - baseProbability γ) ^ 2 / (baseProbability γ * (1 - baseProbability γ)) ≤ _
    rw [show baseProbability γ + probabilityIncrement γ ε - baseProbability γ = probabilityIncrement γ ε by ring]
    exact qMixture_source_chi_factor_bound γ ε hγ hγ1 hε hεmax
  have hlog := qMixture_log_card_lower_of_pos m A hm hA
  push_cast at hlog
  have hN : (0 : ℝ) ≤ N := by positivity
  have hNd : (N : ℝ) * d ≤ Real.log (m * A + 1) := by
    have hmul : (N : ℝ) * d ≤ 256 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) := by
      convert mul_le_mul_of_nonneg_left hdBound hN using 1 <;> ring
    have htotal := hbudget.trans hlog
    linarith only [hmul, htotal]
  have hchi : (∫ x, ((mix.rnDeriv μ₀ x).toReal - 1) ^ 2 ∂μ₀) ≤ 1 := by
    rw [qMixtureActual_density_chi_integral p q hp hp1 hq.le]
    have hc := qMixture_chi_le_one_of_log_budget d N (m * A) hd (by positivity)
      (by simpa only [Nat.cast_mul] using hNd)
    simpa only [d, Nat.cast_mul] using hc
  have hpos : ∀ x, μ₀ {x} ≠ 0 := qMixtureActiveBaseline_atom_ne_zero (m := m) (A := A) (N := N) p q hp hp1 hq.le
  have hover : (1 : ℝ) / 2 ≤ finiteOverlap μ₀ mix := by
    have hv := finiteOverlap_ge_half_of_density_integral mix μ₀ hpos hchi
    unfold finiteOverlap at hv ⊢
    convert hv using 1
    apply Finset.sum_congr rfl
    intro x _
    exact min_comm _ _
  let Q (i : QMixtureIndex m A) :=
    (qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax).trajectoryExpectedQ
      (qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax).optimalGreedyPolicy
  have hsep (θ : Θ) : 2 * ε < ‖Q (some θ) - Q none‖ := by
    exact qMixtureSourceMDP_baseline_norm_gap θ.1 θ.2 γ ε hγ hγ1 hε hεmax
  let est : Ω → Option (Fin m) → Fin A → ℝ := fun x ↦ estimate (qMixtureReconstruct x)
  have hmix (E : Set Ω) : mix.real E = (∑ θ, (P θ).real E) / Fintype.card Θ := by
    simpa [mix, P, Θ, Fintype.card_prod] using qMixtureActiveLaw_real_event p q hp1.le hq.le E
  have hr := finite_mixture_baseline_risk_selection μ₀ P mix hmix hover est (Q none)
    (fun θ ↦ Q (some θ)) ε hsep
  have hevent (i : QMixtureIndex m A) :
      let M := qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax
      (samplingLaw M N).real {data | ε < ‖estimate data - Q i‖} =
      (indexedBernoulliLaw (qMixtureBernoulliParameter i p q)
        (qMixtureBernoulliParameter_le_one i p q hp1.le hq.le)).real
        {x | ε < ‖est x - Q i‖} := by
    have h := qMixtureSamplingLaw_eq_reconstructed_product i γ p q (by linarith) hγ1 hpq hq N
    dsimp only [qMixtureSourceMDP]
    change (samplingLaw (qMixtureMDP i γ (p : ℝ) (q : ℝ) _ _ _ _ _) N).real _ = _
    rw [h]
    simp only [measureReal_def]
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  rcases hr with h₀ | ⟨θ, hθ⟩
  · refine ⟨none, ?_⟩
    change (1 : ℝ) / 4 ≤ (samplingLaw (qMixtureSourceMDP none γ ε hγ hγ1 hε hεmax) N).real
      {data | ε < ‖estimate data - Q none‖}
    rw [hevent none]
    exact h₀
  · refine ⟨some θ, ?_⟩
    change (1 : ℝ) / 4 ≤ (samplingLaw (qMixtureSourceMDP (some θ) γ ε hγ hγ1 hε hεmax) N).real
      {data | ε < ‖estimate data - Q (some θ)‖}
    rw [hevent (some θ)]
    exact hθ

end StatisticalRL.GenerativeLowerBound
