import Formalization.Generative.GenerativeLowerBoundQMixtureFinalRandomized
import Formalization.Generative.GenerativeLowerBoundQMixtureAnyAction
import Formalization.Generative.GenerativeLowerBoundTheorem37Fin
import Formalization.Generative.PolicyEvalLowerBoundA1
import Formalization.Generative.GenerativeLowerBoundObservationLaw

/-!
# Theorem 3.7(ii) for randomized Q-function estimators

Source: `theorem:azar`, `source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464`
(proof 1838–2173), part (ii) "any Q-function estimator"; the single-action comparisons at
`generative_model_model_based.tex:1468–1474` and `generative_model_model_free.tex:248–249`; and the
two-point display `eq:P-Mi-Q-inaccurate-lower-generative`
(`generative_model_model_based.tex:1541–1556`).

A randomized estimator is a family of probability laws on estimates indexed by the data (a
Markov kernel from the finite sample space; no measurability in the data is needed since the
sample space is finite and discrete). The failure probability is the probability of the error
event under the joint data/estimate law, written `∫ data, (κ data).real E ∂(samplingLaw M N)`.
The σ-algebra on the estimate space is arbitrary provided the error balls are measurable
(in particular every `OpensMeasurableSpace`, including `⊤` and the Borel σ-algebra).

* `qMixtureSource_randomized_Q_risk_of_pos`: the reviewed randomized mixture bound
  `qMixtureSource_randomized_Q_risk` for every `A ≥ 1` (its premise `2 ≤ A` was used only for the
  cardinality inequality, replaced by `qMixture_log_card_lower_of_pos`) and arbitrary σ-algebra.
* `theorem37_Q_fin_randomized`: corrected Theorem 3.7(ii) on `Fin S × Fin A`, randomized.
* `theorem37_Q_fin_randomized_seed`: the same for data plus an independent seed.
* `policyEvaluation_lowerBound_singleAction_randomized`: the `A = 1` policy-evaluation form.
* `sourceHardMDP_randomized_Q_estimation_lower`: the two-point display, randomized.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatisticalRL.GenerativeLowerBound

open StatisticalRL.ModelBasedPolicyLearning StatisticalRL.DiscountedMDP

local instance randQOptionMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

/-- The joint data/estimate probability of an output event is the expected conditional
probability. -/
theorem finiteDataRandomOutputLaw_real_event_eq_integral {X Y : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) [IsProbabilityMeasure μ]
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (hE : MeasurableSet E) :
    (finiteDataRandomOutputLaw μ κ).real (Set.univ ×ˢ E) = ∫ x, (κ x).real E ∂μ := by
  rw [finiteDataRandomOutputLaw_real_event μ κ E hE, integral_fintype _ Integrable.of_finite]
  simp [smul_eq_mul]

/-- Randomized baseline-versus-mixture Q-risk for every positive action count and every
σ-algebra on the estimate space in which the error balls are measurable. Same argument as
`qMixtureSource_randomized_Q_risk`, with `qMixture_log_card_lower_of_pos`. -/
theorem qMixtureSource_randomized_Q_risk_of_pos {m A : ℕ} (hm : 1 ≤ m) (hA : 1 ≤ A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((m + 1) * A))
    [MeasurableSpace (Option (Fin m) → Fin A → ℝ)]
    (hE : ∀ Q₀ : Option (Fin m) → Fin A → ℝ, MeasurableSet {Q | ε < ‖Q - Q₀‖})
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
  have hE' : MeasurableSet {Qhat : Option (Fin m) → Fin A → ℝ | ε < ‖Qhat - Q none‖} :=
    hE (Q none)
  have hmix (E : Set Ω) : mix.real E = (∑ θ, (P θ).real E) / Fintype.card Θ := by
    simpa [mix, P, Θ, Fintype.card_prod] using qMixtureActiveLaw_real_event p q hp1.le hq.le E
  have hr := finiteRandomOutput_mixture_risk_selection μ₀ P mix κactive hmix hover (Q none)
    (fun θ ↦ Q (some θ)) ε hE' hsep
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
    rw [hevent none _ hE']
    exact h₀
  · refine ⟨some θ, ?_⟩
    have hEθ : MeasurableSet {Qhat : Option (Fin m) → Fin A → ℝ | ε < ‖Qhat - Q (some θ)‖} :=
      hE (Q (some θ))
    change (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw
      (samplingLaw (qMixtureSourceMDP (some θ) γ ε hγ hγ1 hε hεmax) N) κ).real
        (Set.univ ×ˢ {Qhat | ε < ‖Qhat - Q (some θ)‖})
    rw [hevent (some θ) _ hEθ]
    exact hθ


/-- Sup-norm distance is invariant under relabeling the state coordinate. -/
theorem norm_comp_equiv_sub {σ τ β : Type*} [Fintype σ] [Fintype τ] [SeminormedAddCommGroup β]
    (e : σ ≃ τ) (F : τ → β) (G : σ → β) :
    ‖(fun s ↦ F (e s)) - G‖ = ‖F - (fun t ↦ G (e.symm t))‖ := by
  rw [← norm_comp_equiv_symm e ((fun s ↦ F (e s)) - G)]
  congr 1
  funext t
  simp

/-- Corrected Theorem 3.7(ii) on `Fin S × Fin A` for randomized Q-function estimators. The
estimator is a probability law `QHat r γ data` on Q-tables for each value of the known reward
table, the known discount and the full `N`-per-pair sample array; its failure probability is the
probability, under the joint law of data and estimate, that the sup-norm error exceeds `ε`. The
σ-algebra on Q-tables is arbitrary provided the open error balls are measurable. -/
theorem theorem37_Q_fin_randomized {S A N : ℕ} (hS : 2 ≤ S) (hSA : 16 ≤ S * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((S : ℝ) * (A : ℝ)))
    [MeasurableSpace (Fin S → Fin A → ℝ)]
    (hE : ∀ Q₀ : Fin S → Fin A → ℝ, MeasurableSet {Q | ε < ‖Q - Q₀‖})
    (QHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Measure (Fin S → Fin A → ℝ))
    (hQ : ∀ r g data, IsProbabilityMeasure (QHat r g data)) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ ∫ data, (QHat M.reward M.discount data).real
          {Q | ε < ‖Q - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} ∂(samplingLaw M N) := by
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; omega
    · exact h
  letI : NeZero A := ⟨by omega⟩
  let mF : MeasurableSpace (Fin (m + 1) → Fin A → ℝ) := inferInstance
  let e : Option (Fin m) ≃ Fin (m + 1) := (finSuccEquiv m).symm
  let r₀ : Fin (m + 1) → Fin A → ℝ :=
    ((qMixtureSourceMDP (none : QMixtureIndex m A) γ ε hγ hγ1 hε hεmax).relabelStates e).reward
  let g : (Fin (m + 1) → Fin A → ℝ) → (Option (Fin m) → Fin A → ℝ) := fun Q s ↦ Q (e s)
  letI mO : MeasurableSpace (Option (Fin m) → Fin A → ℝ) := MeasurableSpace.map g mF
  have hg : Measurable g := fun _ hs ↦ hs
  have hEO : ∀ Q₀ : Option (Fin m) → Fin A → ℝ, MeasurableSet {Q | ε < ‖Q - Q₀‖} := by
    intro Q₀
    change MeasurableSet[mF] (g ⁻¹' {Q | ε < ‖Q - Q₀‖})
    convert hE (fun t ↦ Q₀ (e.symm t)) using 1
    ext Q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, g]
    rw [norm_comp_equiv_sub e Q Q₀]
  let κ : Samples (Option (Fin m)) (Fin A) N → Measure (Option (Fin m) → Fin A → ℝ) :=
    fun d ↦ (QHat r₀ γ (relabelSamples e N d)).map g
  have hκ : ∀ d, IsProbabilityMeasure (κ d) := by
    intro d
    haveI := hQ r₀ γ (relabelSamples e N d)
    exact Measure.isProbabilityMeasure_map hg.aemeasurable
  have hgap : 0 ≤ 1 - γ := by linarith
  have hterm : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by positivity
  have hb' : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((m + 1) * A) := by
    have h := hbudget
    push_cast at h
    linarith
  obtain ⟨i, hi⟩ := qMixtureSource_randomized_Q_risk_of_pos (by omega) hA
    γ ε hγ hγ1 hε hεmax N hb' hEO κ hκ
  haveI := hκ
  refine ⟨(qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax).relabelStates e, rfl, ?_⟩
  dsimp only at hi
  rw [finiteDataRandomOutputLaw_real_event_eq_integral _ _ _ (hEO _)] at hi
  rw [samplingLaw_relabelStates, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  refine hi.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun d ↦ ?_))
  simp only [κ]
  rw [map_measureReal_apply hg (hEO _)]
  congr 1
  ext Q
  simp only [Set.mem_preimage, Set.mem_setOf_eq, g]
  rw [relabelStates_estimate_Q_loss_norm]


/-- The printed sample bound with `c_N = 1/32768`, randomized Q-estimators, and every
σ-algebra on Q-tables containing the open sets. -/
theorem theorem37_Q_fin_randomized_sampleBound {S A N : ℕ} (hS : 2 ≤ S) (hSA : 16 ≤ S * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hN : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2))
    [MeasurableSpace (Fin S → Fin A → ℝ)] [OpensMeasurableSpace (Fin S → Fin A → ℝ)]
    (QHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Measure (Fin S → Fin A → ℝ))
    (hQ : ∀ r g data, IsProbabilityMeasure (QHat r g data)) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ ∫ data, (QHat M.reward M.discount data).real
          {Q | ε < ‖Q - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} ∂(samplingLaw M N) :=
  theorem37_Q_fin_randomized hS hSA γ ε hγ hγ1 hε hεmax
    (theorem37_budget_of_sampleBound S A N γ ε hγ1 hε hN)
    (fun _ ↦ (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet)
    QHat hQ

/-- For a finite data space and an independent seed, the probability of an output event under
`data ⊗ seed` is the expected probability under the induced output kernel. -/
theorem prod_real_eq_integral_map {X Ξ Y : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Ξ] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (f : X → Ξ → Y) (hf : ∀ x, Measurable (f x)) (E : Set Y) (hE : MeasurableSet E) :
    (μ.prod ν).real {z | f z.1 z.2 ∈ E} = ∫ x, (ν.map (f x)).real E ∂μ := by
  classical
  have hT : MeasurableSet {z : X × Ξ | f z.1 z.2 ∈ E} := by
    have h : {z : X × Ξ | f z.1 z.2 ∈ E} = ⋃ x, {x} ×ˢ (f x ⁻¹' E) := by
      ext ⟨x, ω⟩
      simp
    rw [h]
    exact MeasurableSet.iUnion fun x ↦ (measurableSet_singleton x).prod (hf x hE)
  rw [integral_fintype _ Integrable.of_finite, measureReal_def, Measure.prod_apply hT,
    lintegral_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [map_measureReal_apply (hf x) hE, ENNReal.toReal_mul, smul_eq_mul, mul_comm]
    rfl
  · intro x _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Corrected Theorem 3.7(ii) on `Fin S × Fin A` for estimators that use the data and an
independent seed `ξ ∼ ν` on an arbitrary measurable space (measurable in the seed for each
fixed data array). -/
theorem theorem37_Q_fin_randomized_seed {S A N : ℕ} (hS : 2 ≤ S) (hSA : 16 ≤ S * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hN : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2))
    {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (QHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Ξ → Fin S → Fin A → ℝ)
    (hmeas : ∀ r g data, Measurable (QHat r g data)) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ ((samplingLaw M N).prod ν).real
        {z | ε < ‖QHat M.reward M.discount z.1 z.2 -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  obtain ⟨M, hMγ, hM⟩ := theorem37_Q_fin_randomized_sampleBound hS hSA γ ε hγ hγ1 hε hεmax hN
    (fun r g data ↦ ν.map (QHat r g data))
    (fun r g data ↦ Measure.isProbabilityMeasure_map (hmeas r g data).aemeasurable)
  refine ⟨M, hMγ, hM.trans_eq ?_⟩
  exact (prod_real_eq_integral_map (samplingLaw M N) ν (QHat M.reward M.discount)
    (hmeas M.reward M.discount) _
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet).symm

/-- Policy-evaluation lower bound at `A = 1` for randomized value estimators: every family of
probability laws on value vectors indexed by the known reward table, the known discount and the
`N`-per-state policy samples fails with probability at least `1/4` on some MDP. The σ-algebra
on value vectors is arbitrary provided the open error balls are measurable. -/
theorem policyEvaluation_lowerBound_singleAction_randomized {S N : ℕ} (hS : 16 ≤ S)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hN : (N : ℝ) ≤ (1 / 32768) * Real.log (S : ℝ) / ((1 - γ) ^ 3 * ε ^ 2))
    [MeasurableSpace (Fin S → ℝ)]
    (hE : ∀ V₀ : Fin S → ℝ, MeasurableSet {V | ε < ‖V - V₀‖})
    (VHat : (Fin S → Fin 1 → ℝ) → ℝ →
      StatisticalRL.ModelBasedPolicyEvaluation.Samples (Fin S) N → Measure (Fin S → ℝ))
    (hV : ∀ r g data, IsProbabilityMeasure (VHat r g data)) :
    ∃ M : DiscountedMDP (Fin S) (Fin 1), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ ∫ data, (VHat M.reward M.discount data).real
          {V | ε < ‖V - M.trajectoryExpectedValue
            (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1))‖}
        ∂(StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M
          (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1)) N) := by
  have hN' : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * ((1 : ℕ) : ℝ)) /
      ((1 - γ) ^ 3 * ε ^ 2) := by
    simpa using hN
  have hb := theorem37_budget_of_sampleBound S 1 N γ ε hγ1 hε hN'
  let mV : MeasurableSpace (Fin S → ℝ) := inferInstance
  let lift : (Fin S → ℝ) → (Fin S → Fin 1 → ℝ) := fun h s _ ↦ h s
  letI mQ : MeasurableSpace (Fin S → Fin 1 → ℝ) := MeasurableSpace.map lift mV
  have hlift : Measurable lift := fun _ hs ↦ hs
  have hliftsub (h : Fin S → ℝ) (Q₀ : Fin S → Fin 1 → ℝ) :
      lift h - Q₀ = fun s _ ↦ (h - fun t ↦ Q₀ t 0) s := by
    funext s a
    simp only [Pi.sub_apply, lift]
    rw [Subsingleton.elim a 0]
  have hEQ : ∀ Q₀ : Fin S → Fin 1 → ℝ, MeasurableSet {Q | ε < ‖Q - Q₀‖} := by
    intro Q₀
    change MeasurableSet[mV] (lift ⁻¹' {Q | ε < ‖Q - Q₀‖})
    convert hE (fun t ↦ Q₀ t 0) using 1
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [hliftsub, norm_singleAction_lift]
  let f : Fin S → Fin 1 := fun _ ↦ 0
  let QHat : (Fin S → Fin 1 → ℝ) → ℝ → Samples (Fin S) (Fin 1) N →
      Measure (Fin S → Fin 1 → ℝ) :=
    fun r g data ↦ (VHat r g (projectPolicySamples N f data)).map lift
  have hQ : ∀ r g data, IsProbabilityMeasure (QHat r g data) := by
    intro r g data
    haveI := hV r g (projectPolicySamples N f data)
    exact Measure.isProbabilityMeasure_map hlift.aemeasurable
  obtain ⟨M, hMγ, hrisk⟩ := theorem37_Q_fin_randomized (S := S) (A := 1) (by omega) (by omega)
    γ ε hγ hγ1 hε hεmax hb hEQ QHat hQ
  refine ⟨M, hMγ, ?_⟩
  change (1 : ℝ) / 4 ≤ ∫ data, (VHat M.reward M.discount data).real
      {V | ε < ‖V - M.trajectoryExpectedValue (singleActionPolicy S)‖}
    ∂(StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M
      (fun t ↦ EnvironmentStage.pointMass (f t)) N)
  rw [← samplingLaw_projectPolicySamples M N f, integral_map
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  refine hrisk.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun d ↦ ?_))
  simp only [QHat]
  rw [map_measureReal_apply hlift (hEQ _)]
  congr 1
  ext h
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hQV : M.trajectoryExpectedQ M.optimalGreedyPolicy =
      fun s _ ↦ M.trajectoryExpectedValue (singleActionPolicy S) s := by
    funext s a
    exact singleAction_trajectoryExpectedQ_eq M s a
  rw [hliftsub, hQV, norm_singleAction_lift]


/-- Change of variables for a real function on a countable data space. -/
theorem integral_map_of_countable {X Z : Type*} [Countable X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (μ : Measure X) (c : X → Z) (f : Z → ℝ) :
    ∫ z, f z ∂(μ.map c) = ∫ x, f (c x) ∂μ :=
  integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Two-point estimation with a randomized scalar estimator on the two actual Bernoulli product
laws: under the quadratic budget, one of the two strict error probabilities exceeds `1/10`.
The σ-algebra `mR` on the estimate line is arbitrary (no measurability of the error events is
used: the two events cover the line, and outer measure is subadditive); it is passed as an
implicit argument rather than an instance argument. -/
theorem bernoulliProduct_randomized_estimation_error_gt_one_tenth (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hbudget : N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ≤ 9 / 10)
    {mR : MeasurableSpace ℝ} (κ : (Fin N → Bool) → @Measure ℝ mR)
    (hκ : ∀ x, @IsProbabilityMeasure ℝ mR (κ x)) (v₀ v₁ ε : ℝ) (hsep : 2 * ε < v₁ - v₀) :
    (1 : ℝ) / 10 < ∫ x, (κ x).real {y | ε < |y - v₀|} ∂(bernoulliProductLaw N p hp1.le) ∨
    (1 : ℝ) / 10 < ∫ x, (κ x).real {y | ε < |y - v₁|} ∂(bernoulliProductLaw N q hq1.le) := by
  classical
  let μ₀ := bernoulliProductLaw N p hp1.le
  let μ₁ := bernoulliProductLaw N q hq1.le
  let f₀ : (Fin N → Bool) → ℝ := fun x ↦ (κ x).real {y | ε < |y - v₀|}
  let f₁ : (Fin N → Bool) → ℝ := fun x ↦ (κ x).real {y | ε < |y - v₁|}
  have hcover (x : Fin N → Bool) : 1 ≤ f₀ x + f₁ x := by
    haveI := hκ x
    have hsub : (Set.univ : Set ℝ) ⊆ {y | ε < |y - v₀|} ∪ {y | ε < |y - v₁|} := by
      intro y _
      by_contra hy
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hy
      have h0 := (abs_le.mp hy.1).2
      have h1 := (abs_le.mp hy.2).1
      linarith
    have h := (measureReal_mono hsub (measure_ne_top _ _)).trans
      (measureReal_union_le (μ := κ x) {y | ε < |y - v₀|} {y | ε < |y - v₁|})
    rw [probReal_univ] at h
    exact h
  have hKL : (InformationTheory.klDiv μ₁ μ₀).toReal ≤ 9 / 10 :=
    (bernoulliProduct_klDiv_le_quadratic N q p hp hp1 hq hq1).trans hbudget
  have ho := finite_exp_neg_klDiv_le_two_overlap μ₁ μ₀
    (bernoulliProductLaw_atom_ne_zero N q hq hq1) (bernoulliProductLaw_atom_ne_zero N p hp hp1)
  have hex := sourceExpBranch_strict _ hKL
  have hover : (1 : ℝ) / 5 < finiteOverlap μ₀ μ₁ := by
    have hm : finiteOverlap μ₁ μ₀ = finiteOverlap μ₀ μ₁ := by
      unfold finiteOverlap
      simp only [min_comm]
    rw [hm] at ho
    linarith
  have hsum : finiteOverlap μ₀ μ₁ ≤ (∫ x, f₀ x ∂μ₀) + ∫ x, f₁ x ∂μ₁ := by
    rw [integral_fintype _ Integrable.of_finite, integral_fintype _ Integrable.of_finite,
      ← Finset.sum_add_distrib]
    unfold finiteOverlap
    apply Finset.sum_le_sum
    intro x _
    have hf₀ : 0 ≤ f₀ x := measureReal_nonneg
    have hf₁ : 0 ≤ f₁ x := measureReal_nonneg
    have hm₀ : min (μ₀.real {x}) (μ₁.real {x}) ≤ μ₀.real {x} := min_le_left _ _
    have hm₁ : min (μ₀.real {x}) (μ₁.real {x}) ≤ μ₁.real {x} := min_le_right _ _
    have hm : 0 ≤ min (μ₀.real {x}) (μ₁.real {x}) := le_min measureReal_nonneg measureReal_nonneg
    simp only [smul_eq_mul]
    nlinarith [hcover x, mul_le_mul_of_nonneg_right hm₀ hf₀, mul_le_mul_of_nonneg_right hm₁ hf₁]
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  have : (∫ x, f₀ x ∂μ₀) + ∫ x, f₁ x ∂μ₁ ≤ 1 / 5 := by
    have := hcon.1
    have := hcon.2
    simp only [f₀, f₁, μ₀, μ₁] at *
    linarith
  linarith

/-- The two-point Q-estimation lower bound of `eq:P-Mi-Q-inaccurate-lower-generative` for
randomized estimators: a probability law `QHat data` on estimates of `Q⋆(s₁,a)` for each full
sample array, on an arbitrary σ-algebra `mR` of the real line. -/
theorem sourceHardMDP_randomized_Q_estimation_lower (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hN : (N : ℝ) ≤ 9 / (2560 * (1 - γ) ^ 3 * ε ^ 2))
    {mR : MeasurableSpace ℝ}
    (QHat : Samples Bool Unit N → @Measure ℝ mR)
    (hQ : ∀ data, @IsProbabilityMeasure ℝ mR (QHat data)) :
    let M₀ := sourceHardMDP γ ε hγ hγ1 hε hεmax false
    let M₁ := sourceHardMDP γ ε hγ hγ1 hε hεmax true
    (1 : ℝ) / 10 < ∫ data, (QHat data).real
        {y | ε < |y - M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ()|}
        ∂(samplingLaw M₀ N) ∨
    (1 : ℝ) / 10 < ∫ data, (QHat data).real
        {y | ε < |y - M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()|}
        ∂(samplingLaw M₁ N) := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p : ℝ≥0 := ⟨baseProbability γ, by linarith [ha.1]⟩
  let q : ℝ≥0 := ⟨baseProbability γ + probabilityIncrement γ ε, by linarith [ha.1, ha.2.1]⟩
  have hp : 0 < p := by change 0 < baseProbability γ; linarith [ha.1]
  have hp1 : p < 1 := by change baseProbability γ < 1; linarith [ha.2.1, ha.2.2.1]
  have hq : 0 < q := by
    change 0 < baseProbability γ + probabilityIncrement γ ε; linarith [ha.1, ha.2.1]
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
  have he := bernoulliProduct_randomized_estimation_error_gt_one_tenth N q p hp hp1 hq hq1
    hbudget (fun x ↦ QHat (completeSamples N x)) (fun x ↦ hQ _)
    (M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ())
    (M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()) ε hsep
  have h₀ : samplingLaw M₀ N = (bernoulliProductLaw N p hp1.le).map (completeSamples N) :=
    hardMDP_full_samplingLaw γ p (by linarith) hγ1 hp1.le N
  have h₁ : samplingLaw M₁ N = (bernoulliProductLaw N q hq1.le).map (completeSamples N) :=
    hardMDP_full_samplingLaw γ q (by linarith) hγ1 hq1.le N
  intro M₀' M₁'
  change (1 : ℝ) / 10 < ∫ data, (QHat data).real
        {y | ε < |y - M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ()|}
        ∂(samplingLaw M₀ N) ∨
    (1 : ℝ) / 10 < ∫ data, (QHat data).real
        {y | ε < |y - M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()|}
        ∂(samplingLaw M₁ N)
  rw [h₀, h₁, integral_map_of_countable, integral_map_of_countable]
  exact he

end StatisticalRL.GenerativeLowerBound
