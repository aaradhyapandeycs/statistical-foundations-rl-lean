import Formalization.Generative.GenerativeLowerBoundTwoStateMDP
import Formalization.Generative.GenerativeLowerBoundKLAffinity
import Formalization.Generative.PolicyLearningHoeffding

/-! Full two-state observation arrays and their active-row projection. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning

/-- The source nonabsorbing row is the actual Bernoulli transition law. -/
theorem hardRow_true_measure (p : ℝ≥0) (hp : p ≤ 1) :
    (hardRow (p : ℝ) (by positivity) (by exact_mod_cast hp) true).rowMeasure =
      (PMF.bernoulli p hp).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  cases b <;> simp [FiniteDistribution.toPMF_apply, hardRow, PMF.bernoulli_apply, hp,
    ENNReal.ofReal_sub, ENNReal.ofReal_coe_nnreal]

/-- Project the actual full state-action sample array to its nonabsorbing row. -/
def activeRowSamples (N : ℕ) (data : Samples Bool Unit N) : Fin N → Bool :=
  fun i ↦ data ((true, ()), i)

/-- The full product experiment projects to the genuine Bernoulli product law. -/
theorem hardMDP_activeRow_samplingLaw (γ : ℝ) (p : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : p ≤ 1) (N : ℕ) :
    (samplingLaw (hardMDP γ (p : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hp)) N).map
      (activeRowSamples N) = bernoulliProductLaw N p hp := by
  rw [show activeRowSamples N = (fun data i ↦ data ((true, ()), i)) from rfl,
    samplingLaw_stateActionRow]
  unfold FiniteDistribution.sampleMeasure bernoulliProductLaw
  congr 1
  funext i
  exact hardRow_true_measure p hp

/-- Reconstruct the complete array by filling the absorbing row with false. -/
def completeSamples (N : ℕ) (x : Fin N → Bool) : Samples Bool Unit N :=
  fun i ↦ if i.1.1 then x i.2 else false

/-- The absorbing row is constant almost surely in the actual full experiment. -/
theorem hardMDP_absorbingRow_ae (γ : ℝ) (p : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : p ≤ 1) (N : ℕ) :
    ∀ᵐ data ∂(samplingLaw (hardMDP γ (p : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hp)) N),
      ∀ i : Fin N, data ((false, ()), i) = false := by
  apply ae_all_iff.mpr
  intro i
  rw [ae_iff]
  have heq : {data : Samples Bool Unit N | ¬ data ((false, ()), i) = false} =
      (fun data : Samples Bool Unit N ↦ data ((false, ()), i)) ⁻¹' {true} := by
    ext data
    cases h : data ((false, ()), i) <;> simp [h]
  rw [heq, ← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
    samplingLaw_marginal]
  simp [hardMDP, FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton,
    FiniteDistribution.toPMF_apply, hardRow]

/-- The full array law is the pushforward of the sole random row; the
absorbing row is filled deterministically and carries no extra information. -/
theorem hardMDP_full_samplingLaw (γ : ℝ) (p : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : p ≤ 1) (N : ℕ) :
    samplingLaw (hardMDP γ (p : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hp)) N =
      (bernoulliProductLaw N p hp).map (completeSamples N) := by
  let μ := samplingLaw (hardMDP γ (p : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hp)) N
  have hactive : μ.map (activeRowSamples N) = bernoulliProductLaw N p hp :=
    hardMDP_activeRow_samplingLaw γ p hγ hγ1 hp N
  have hae : (fun data ↦ completeSamples N (activeRowSamples N data)) =ᵐ[μ] id := by
    filter_upwards [hardMDP_absorbingRow_ae γ p hγ hγ1 hp N] with data hd
    funext i
    rcases i with ⟨⟨s, a⟩, j⟩
    cases a
    cases s <;> simp [completeSamples, activeRowSamples, hd]
  calc
    μ = μ.map id := (Measure.map_id).symm
    _ = μ.map (fun data ↦ completeSamples N (activeRowSamples N data)) := (Measure.map_congr hae).symm
    _ = (μ.map (activeRowSamples N)).map (completeSamples N) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by rw [hactive]

/-- Transfer the strict two-point estimation lower bound to one estimator on
the complete state-action arrays of the two actual hard MDPs. -/
theorem hardMDP_full_estimation_error (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (N : ℕ)
    (hbudget : N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ≤ 9 / 10)
    (estimate : Samples Bool Unit N → ℝ) (v₀ v₁ ε : ℝ) (hsep : 2 * ε < v₁ - v₀) :
    (1 : ℝ) / 10 < (samplingLaw
      (hardMDP γ (p : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hp1.le)) N).real
        {data | ε < |estimate data - v₀|} ∨
    (1 : ℝ) / 10 < (samplingLaw
      (hardMDP γ (q : ℝ) hγ hγ1 (by positivity) (by exact_mod_cast hq1.le)) N).real
        {data | ε < |estimate data - v₁|} := by
  have he := bernoulliProduct_estimation_error_gt_one_tenth N q p hp hp1 hq hq1 hbudget
    (fun x ↦ estimate (completeSamples N x)) v₀ v₁ ε hsep
  rw [hardMDP_full_samplingLaw γ p hγ hγ1 hp1.le N,
    hardMDP_full_samplingLaw γ q hγ hγ1 hq1.le N]
  simp only [measureReal_def,
    Measure.map_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)]
  exact he

/-- The source sample budget bounds the Bernoulli testing KL proxy. -/
theorem sourceHardMDP_quadratic_budget (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hN : (N : ℝ) ≤ 9 / (2560 * (1 - γ) ^ 3 * ε ^ 2)) :
    N * (probabilityIncrement γ ε ^ 2 /
      (baseProbability γ * (1 - baseProbability γ))) ≤ 9 / 10 := by
  let p := baseProbability γ
  let a := probabilityIncrement γ ε
  let h := 1 - γ
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  have hr := (source_parameters_squared_ratio γ ε hγ hγ1 hε).2
  change a ^ 2 / (1 - p) ≤ 128 * h ^ 3 * ε ^ 2 at hr
  have hp : 0 < p := by linarith [ha.1]
  have hp1 : 0 < 1 - p := by linarith [ha.2.1, ha.2.2.1]
  have hh : 0 < h := sub_pos.mpr hγ1
  have hc : a ^ 2 / (p * (1 - p)) ≤ 2 * (a ^ 2 / (1 - p)) := by
    rw [mul_comm p (1 - p), div_mul_eq_div_div]
    apply (div_le_iff₀ hp).2
    have hs : 0 ≤ a ^ 2 / (1 - p) := by positivity
    nlinarith [ha.1]
  have hn : (0 : ℝ) ≤ N := by positivity
  have hbound : (N : ℝ) * (256 * h ^ 3 * ε ^ 2) ≤ 9 / 10 := by
    have hd : 0 < 2560 * h ^ 3 * ε ^ 2 := by positivity
    have hh' := (le_div_iff₀ hd).1 hN
    nlinarith
  have hc' : a ^ 2 / (p * (1 - p)) ≤ 256 * h ^ 3 * ε ^ 2 := by
    calc
      _ ≤ 2 * (a ^ 2 / (1 - p)) := hc
      _ ≤ 256 * h ^ 3 * ε ^ 2 := by nlinarith [hr]
  have hmul := mul_le_mul_of_nonneg_left hc' hn
  exact hmul.trans hbound

/-- An arbitrary single full-array Q estimator has strict source risk above
0.1 in one of the two actual source models at the explicit sample budget. -/
theorem sourceHardMDP_full_Q_estimation_lower (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hN : (N : ℝ) ≤ 9 / (2560 * (1 - γ) ^ 3 * ε ^ 2))
    (estimate : Samples Bool Unit N → Bool → Unit → ℝ) :
    let M₀ := sourceHardMDP γ ε hγ hγ1 hε hεmax false
    let M₁ := sourceHardMDP γ ε hγ hγ1 hε hεmax true
    (1 : ℝ) / 10 < (samplingLaw M₀ N).real {data |
      ε < |estimate data true () - M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ()|} ∨
    (1 : ℝ) / 10 < (samplingLaw M₁ N).real {data |
      ε < |estimate data true () - M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()|} := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p : ℝ≥0 := ⟨baseProbability γ, by linarith [ha.1]⟩
  let q : ℝ≥0 := ⟨baseProbability γ + probabilityIncrement γ ε, by linarith [ha.1, ha.2.1]⟩
  have hp : 0 < p := by change 0 < baseProbability γ; linarith [ha.1]
  have hp1 : p < 1 := by change baseProbability γ < 1; linarith [ha.2.1, ha.2.2.1]
  have hq : 0 < q := by change 0 < baseProbability γ + probabilityIncrement γ ε; linarith [ha.1, ha.2.1]
  have hq1 : q < 1 := by exact_mod_cast ha.2.2.1
  have hbudget : N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ≤ 9 / 10 := by
    change N * ((baseProbability γ + probabilityIncrement γ ε - baseProbability γ) ^ 2 /
      (baseProbability γ * (1 - baseProbability γ))) ≤ 9 / 10
    convert sourceHardMDP_quadratic_budget γ ε hγ hγ1 hε hεmax N hN using 1 <;> ring
  let M₀ := sourceHardMDP γ ε hγ hγ1 hε hεmax false
  let M₁ := sourceHardMDP γ ε hγ hγ1 hε hεmax true
  have hsep : 2 * ε < M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true () -
      M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true () :=
    sourceHardMDP_optimalQ_separation γ ε hγ hγ1 hε hεmax
  have he := hardMDP_full_estimation_error γ p q (by linarith) hγ1 hp hp1 hq hq1 N hbudget
    (fun data ↦ estimate data true ())
    (M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ())
    (M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()) ε hsep
  simpa [M₀, M₁, sourceHardMDP, p, q] using he

end StatisticalRL.GenerativeLowerBound
