import Formalization.Generative.GenerativeLowerBoundQMixtureOverlap
import Formalization.Generative.GenerativeLowerBoundQMixtureThreshold
import Formalization.Generative.GenerativeLowerBoundQMixtureSourceGap
import Formalization.Generative.GenerativeLowerBoundQRandomReconstruct

/-! Corrected baseline-versus-mixture deterministic Q-risk assembly. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance qRandomFinalState (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance qRandomFinalAction (A : ℕ) : MeasurableSpace (Fin A) := ⊤

/-- Exact χ² expression is at most one under the exponential budget. -/
theorem qMixture_random_chi_le_one_of_log_budget (d : ℝ) (N K : ℕ)
    (hd : 0 ≤ d) (hK : 0 < K) (hbudget : (N : ℝ) * d ≤ Real.log (K + 1)) :
    ((1 + d) ^ N - 1) / K ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hpow : (1 + d) ^ N ≤ Real.exp ((N : ℝ) * d) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + d) (by simpa [add_comm] using Real.add_one_le_exp d) N
    rw [Real.exp_nat_mul]
    exact h
  have hexp : Real.exp ((N : ℝ) * d) ≤ K + 1 := by
    have h := Real.exp_le_exp.mpr hbudget
    simpa [Real.exp_log (by positivity : (0 : ℝ) < K + 1)] using h
  apply (div_le_iff₀ hK').2
  linarith

/-- Corrected source-size deterministic Q-estimator lower bound for actual
N-per-row full-array observations. -/
theorem qMixtureSource_randomized_Q_risk {m A : ℕ} (hm : 1 ≤ m) (hA : 2 ≤ A)
    (hsize : 16 ≤ (m + 1) * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((m + 1) * A))
    (κ : Samples (Option (Fin m)) (Fin A) N → Measure (Option (Fin m) → Fin A → ℝ))
    (hκ : ∀ data, IsProbabilityMeasure (κ data)) :
    letI : NeZero A := ⟨by omega⟩
    ∃ i : QMixtureIndex m A,
      let M := qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw (samplingLaw M N) κ).real
        (Set.univ ×ˢ {Qhat | ε < ‖Qhat - M.trajectoryExpectedQ M.optimalGreedyPolicy‖}) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero A := ⟨by omega⟩
  letI (data : Samples (Option (Fin m)) (Fin A) N) : IsProbabilityMeasure (κ data) := hκ data
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
  have hlog := qMixture_log_card_lower m A hm hA
  push_cast at hlog
  have hN : (0 : ℝ) ≤ N := by positivity
  have hNd : (N : ℝ) * d ≤ Real.log (m * A + 1) := by
    have hmul : (N : ℝ) * d ≤ 256 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) := by
      convert mul_le_mul_of_nonneg_left hdBound hN using 1 <;> ring
    have htotal := hbudget.trans hlog
    linarith only [hmul, htotal]
  have hchi : (∫ x, ((mix.rnDeriv μ₀ x).toReal - 1) ^ 2 ∂μ₀) ≤ 1 := by
    rw [qMixtureActual_density_chi_integral p q hp hp1 hq.le]
    have hc := qMixture_random_chi_le_one_of_log_budget d N (m * A) hd (by positivity)
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
  let κactive : Ω → Measure (Option (Fin m) → Fin A → ℝ) :=
    fun x ↦ κ (qMixtureReconstruct x)
  haveI (x : Ω) : IsProbabilityMeasure (κactive x) := hκ _
  have hE : MeasurableSet {Qhat : Option (Fin m) → Fin A → ℝ | ε < ‖Qhat - Q none‖} := by
    exact measurableSet_lt measurable_const ((measurable_id.sub measurable_const).norm)
  have hmix (E : Set Ω) : mix.real E = (∑ θ, (P θ).real E) / Fintype.card Θ := by
    simpa [mix, P, Θ, Fintype.card_prod] using qMixtureActiveLaw_real_event p q hp1.le hq.le E
  have hr := finiteRandomOutput_mixture_risk_selection μ₀ P mix κactive hmix hover (Q none)
    (fun θ ↦ Q (some θ)) ε hE hsep
  have hevent (i : QMixtureIndex m A) (E : Set (Option (Fin m) → Fin A → ℝ))
      (hE : MeasurableSet E) :
      let M := qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax
      (finiteDataRandomOutputLaw (samplingLaw M N) κ).real (Set.univ ×ˢ E) =
      (finiteDataRandomOutputLaw
        (indexedBernoulliLaw (qMixtureBernoulliParameter i p q)
          (qMixtureBernoulliParameter_le_one i p q hp1.le hq.le)) κactive).real (Set.univ ×ˢ E) := by
    have h := qMixtureSamplingLaw_eq_reconstructed_product i γ p q (by linarith) hγ1 hpq hq N
    dsimp only [qMixtureSourceMDP]
    change (finiteDataRandomOutputLaw
      (samplingLaw (qMixtureMDP i γ (p : ℝ) (q : ℝ) _ _ _ _ _) N) κ).real _ = _
    rw [h]
    exact finiteDataRandomOutputLaw_map_event _ qMixtureReconstruct κ E hE
  rcases hr with h₀ | ⟨θ, hθ⟩
  · refine ⟨none, ?_⟩
    change (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw
      (samplingLaw (qMixtureSourceMDP none γ ε hγ hγ1 hε hεmax) N) κ).real
        (Set.univ ×ˢ {Qhat | ε < ‖Qhat - Q none‖})
    rw [hevent none _ hE]
    exact h₀
  · refine ⟨some θ, ?_⟩
    have hEθ : MeasurableSet {Qhat : Option (Fin m) → Fin A → ℝ | ε < ‖Qhat - Q (some θ)‖} := by
      exact measurableSet_lt measurable_const ((measurable_id.sub measurable_const).norm)
    change (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw
      (samplingLaw (qMixtureSourceMDP (some θ) γ ε hγ hγ1 hε hεmax) N) κ).real
        (Set.univ ×ˢ {Qhat | ε < ‖Qhat - Q (some θ)‖})
    rw [hevent (some θ) _ hEθ]
    exact hθ

end StatisticalRL.GenerativeLowerBound
