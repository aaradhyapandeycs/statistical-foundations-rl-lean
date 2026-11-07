import Formalization.RobustRL.Ch7.LowerBound73Values
import Formalization.Generative.GenerativeLowerBoundKLAffinity

/-!
# Corrected Theorem 7.3: two-point testing bound for the hard pair

For the two hard models `hardMDP h a₀ …` and `hardMDP h a₁ …` (same `lg, lb`), the actual
product sampling laws `P₀, P₁` (`ModelBasedPolicyLearning.samplingLaw`) satisfy, for every
pair of events containing the two sides of a binary test,
`P₀(E₀) + P₁(E₁) ≥ (affinity)² / 2 ≥ 1/4` as soon as
`2 N (lg - lb)² / (lb (1 - lb)) ≤ log 2`.
Route: Cauchy–Schwarz overlap bound (`finite_affinity_sq_le_two_overlap`), exact product
factorization of the Hellinger affinity, and Jensen (`finite_log_affinity_lower`) with the
χ² bound on the Bernoulli KL (`bernoulliKLExpression_le_quadratic`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.RobustRL.Ch7.LowerBound73

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.GenerativeLowerBound

local instance thm73StateMeasurable (State : Type*) : MeasurableSpace State := ⊤

local instance thm73StateSingleton (State : Type*) : MeasurableSingletonClass State :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

section Product

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

omit [DecidableEq State] [DecidableEq Action] in
instance thm73SamplingLawProbability (M : DiscountedMDP State Action) (N : ℕ) :
    IsProbabilityMeasure (ModelBasedPolicyLearning.samplingLaw M N) := by
  unfold ModelBasedPolicyLearning.samplingLaw; infer_instance

omit [DecidableEq State] [DecidableEq Action] in
theorem rowMeasure_singleton (d : FiniteDistribution State) (x : State) :
    d.rowMeasure {x} = ENNReal.ofReal (d.prob x) := by
  unfold FiniteDistribution.rowMeasure
  rw [@PMF.toMeasure_apply_singleton State ⊤ d.toPMF x MeasurableSpace.measurableSet_top]
  unfold FiniteDistribution.toPMF
  rw [PMF.ofFintype_apply]

omit [DecidableEq State] [DecidableEq Action] in
/-- Atoms of the actual product sampling law. -/
theorem samplingLaw_real_singleton (M : DiscountedMDP State Action) (N : ℕ)
    (x : ModelBasedPolicyLearning.Samples State Action N) :
    (ModelBasedPolicyLearning.samplingLaw M N).real {x} =
      ∏ i, (M.transition i.1.1 i.1.2).prob (x i) := by
  rw [measureReal_def, ← Set.univ_pi_singleton, ModelBasedPolicyLearning.samplingLaw,
    Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [rowMeasure_singleton, ENNReal.toReal_ofReal ((M.transition i.1.1 i.1.2).prob_nonneg _)]

theorem sqrt_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (hf a), ih]

/-- Hellinger affinity of two rows. -/
noncomputable def rowAff (p q : FiniteDistribution State) : ℝ :=
  ∑ y, Real.sqrt (p.prob y) * Real.sqrt (q.prob y)

omit [DecidableEq State] [DecidableEq Action] in
theorem rowAff_self (p : FiniteDistribution State) : rowAff p p = 1 := by
  unfold rowAff
  simp_rw [Real.mul_self_sqrt (p.prob_nonneg _)]
  exact p.sum_prob

/-- Exact factorization of the affinity of two product sampling laws. -/
theorem samplingLaw_affinity (M₀ M₁ : DiscountedMDP State Action) (N : ℕ) :
    ∑ x : ModelBasedPolicyLearning.Samples State Action N,
        Real.sqrt ((ModelBasedPolicyLearning.samplingLaw M₀ N).real {x}) *
          Real.sqrt ((ModelBasedPolicyLearning.samplingLaw M₁ N).real {x}) =
      ∏ sa : State × Action, rowAff (M₀.transition sa.1 sa.2) (M₁.transition sa.1 sa.2) ^ N := by
  simp_rw [samplingLaw_real_singleton]
  have hx : ∀ x : ModelBasedPolicyLearning.Samples State Action N,
      Real.sqrt (∏ i, (M₀.transition i.1.1 i.1.2).prob (x i)) *
        Real.sqrt (∏ i, (M₁.transition i.1.1 i.1.2).prob (x i)) =
      ∏ i, (Real.sqrt ((M₀.transition i.1.1 i.1.2).prob (x i)) *
        Real.sqrt ((M₁.transition i.1.1 i.1.2).prob (x i))) := by
    intro x
    rw [sqrt_prod Finset.univ (fun i ↦ (M₀.transition i.1.1 i.1.2).prob (x i))
        (fun i ↦ (M₀.transition i.1.1 i.1.2).prob_nonneg _),
      sqrt_prod Finset.univ (fun i ↦ (M₁.transition i.1.1 i.1.2).prob (x i))
        (fun i ↦ (M₁.transition i.1.1 i.1.2).prob_nonneg _),
      ← Finset.prod_mul_distrib]
  simp_rw [hx]
  rw [← Fintype.prod_sum (fun (i : (State × Action) × Fin N) (y : State) ↦
      Real.sqrt ((M₀.transition i.1.1 i.1.2).prob y) *
        Real.sqrt ((M₁.transition i.1.1 i.1.2).prob y))]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro sa _
  dsimp only
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Overlap form of the two-point testing bound for the actual sampling laws. -/
theorem samplingLaw_test_sum (M₀ M₁ : DiscountedMDP State Action) (N : ℕ)
    (E₀ E₁ : Set (ModelBasedPolicyLearning.Samples State Action N))
    (test : ModelBasedPolicyLearning.Samples State Action N → Bool)
    (h₀ : {x | test x = false} ⊆ E₀) (h₁ : {x | test x = true} ⊆ E₁) :
    (∏ sa : State × Action,
        rowAff (M₀.transition sa.1 sa.2) (M₁.transition sa.1 sa.2) ^ N) ^ 2 / 2 ≤
      (ModelBasedPolicyLearning.samplingLaw M₀ N).real E₀ +
        (ModelBasedPolicyLearning.samplingLaw M₁ N).real E₁ := by
  set P₀ := ModelBasedPolicyLearning.samplingLaw M₀ N
  set P₁ := ModelBasedPolicyLearning.samplingLaw M₁ N
  have hsum (P : Measure (ModelBasedPolicyLearning.Samples State Action N))
      [IsProbabilityMeasure P] : ∑ x, P.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hCS := finite_affinity_sq_le_two_overlap (fun x ↦ P₁.real {x}) (fun x ↦ P₀.real {x})
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg) (hsum P₁) (hsum P₀)
  have hov := finiteOverlap_le_test_error_sum P₁ P₀ test
  unfold finiteOverlap at hov
  have hA := samplingLaw_affinity M₀ M₁ N
  have hcomm : ∑ x, Real.sqrt (P₁.real {x}) * Real.sqrt (P₀.real {x}) =
      ∑ x, Real.sqrt (P₀.real {x}) * Real.sqrt (P₁.real {x}) :=
    Finset.sum_congr rfl (fun x _ ↦ mul_comm _ _)
  rw [hcomm, hA] at hCS
  have hm₁ : P₁.real {x | test x = true} ≤ P₁.real E₁ := measureReal_mono h₁
  have hm₀ : P₀.real {x | test x = false} ≤ P₀.real E₀ := measureReal_mono h₀
  linarith

end Product

section Hard

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

theorem twoRow_rowAff {s₀ s₁ : State} (h : s₀ ≠ s₁) {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) :
    rowAff (twoRow h t) (twoRow h t') =
      Real.sqrt (1 - t) * Real.sqrt (1 - t') + Real.sqrt t * Real.sqrt t' := by
  unfold rowAff
  rw [sum_pair h, twoRow_prob_s₀ h ht0 ht1, twoRow_prob_s₀ h ht0' ht1',
    twoRow_prob_s₁ h ht0 ht1, twoRow_prob_s₁ h ht0' ht1']
  intro x hx0 hx1
  rw [twoRow_prob_other h t hx0 hx1, Real.sqrt_zero, zero_mul]

/-- Jensen + χ²: the Bernoulli affinity is at least `exp(-(lg-lb)²/(2 lb(1-lb)))`. -/
theorem bernoulli_log_affinity {lg lb : ℝ} (hlb : 0 < lb) (hlbg : lb ≤ lg) (hlg : lg < 1) :
    -((lg - lb) ^ 2 / (lb * (1 - lb))) / 2 ≤
      Real.log (Real.sqrt (1 - lg) * Real.sqrt (1 - lb) + Real.sqrt lg * Real.sqrt lb) := by
  have hlg0 : 0 < lg := by linarith
  have hlb1 : lb < 1 := by linarith
  have h := finite_log_affinity_lower (ι := Fin 2) ![lg, 1 - lg] ![lb, 1 - lb]
    (by intro i; fin_cases i <;> simp <;> linarith)
    (by intro i; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_two])
  have hA : finiteAffinity ![lg, 1 - lg] ![lb, 1 - lb] =
      Real.sqrt (1 - lg) * Real.sqrt (1 - lb) + Real.sqrt lg * Real.sqrt lb := by
    simp [finiteAffinity, Fin.sum_univ_two]; ring
  have hK : finiteKLExpression ![lg, 1 - lg] ![lb, 1 - lb] = bernoulliKLExpression lg lb := by
    simp [finiteKLExpression, bernoulliKLExpression, Fin.sum_univ_two]
  rw [hA, hK] at h
  have hq := bernoulliKLExpression_le_quadratic lg lb hlb hlb1 hlg0 hlg
  linarith

variable {s₀ s₁ : State} (h : s₀ ≠ s₁) {a₀ a₁ : Action} {γ lg lb : ℝ}
  (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- **Testing bound for the hard pair.** -/
theorem hard_test_sum (ha : a₀ ≠ a₁) (hlb : 0 < lb) (hlbg : lb ≤ lg) (hlg : lg < 1) (N : ℕ)
    (hN : 2 * N * ((lg - lb) ^ 2 / (lb * (1 - lb))) ≤ Real.log 2)
    (E₀ E₁ : Set (ModelBasedPolicyLearning.Samples State Action N))
    (test : ModelBasedPolicyLearning.Samples State Action N → Bool)
    (h₀ : {x | test x = false} ⊆ E₀) (h₁ : {x | test x = true} ⊆ E₁) :
    1 / 4 ≤ (ModelBasedPolicyLearning.samplingLaw (hardMDP h a₀ γ lg lb hγ0 hγ1) N).real E₀ +
      (ModelBasedPolicyLearning.samplingLaw (hardMDP h a₁ γ lg lb hγ0 hγ1) N).real E₁ := by
  have hT := samplingLaw_test_sum (hardMDP h a₀ γ lg lb hγ0 hγ1) (hardMDP h a₁ γ lg lb hγ0 hγ1)
    N E₀ E₁ test h₀ h₁
  set α := Real.sqrt (1 - lg) * Real.sqrt (1 - lb) + Real.sqrt lg * Real.sqrt lb with hα
  have hlg0 : 0 ≤ lg := by linarith
  have hlb1 : lb ≤ 1 := by linarith
  -- row affinities
  have hrow : ∀ sa : State × Action,
      rowAff ((hardMDP h a₀ γ lg lb hγ0 hγ1).transition sa.1 sa.2)
        ((hardMDP h a₁ γ lg lb hγ0 hγ1).transition sa.1 sa.2) ^ N =
      (if sa = (s₀, a₀) ∨ sa = (s₀, a₁) then α else 1) ^ N := by
    rintro ⟨s, a⟩
    simp only [hardMDP]
    by_cases hs : s = s₀
    · subst hs
      simp only [if_true]
      by_cases h0 : a = a₀
      · subst h0
        have : ell a₁ lg lb a = lb := by unfold ell; rw [if_neg ha]
        rw [this, show ell a lg lb a = lg by unfold ell; rw [if_pos rfl],
          twoRow_rowAff h hlg0 hlg.le hlb.le hlb1]
        simp [hα]
      · by_cases h1 : a = a₁
        · subst h1
          rw [show ell a₀ lg lb a = lb by unfold ell; rw [if_neg (Ne.symm ha)],
            show ell a lg lb a = lg by unfold ell; rw [if_pos rfl],
            twoRow_rowAff h hlb.le hlb1 hlg0 hlg.le]
          simp [h0, hα]
          ring
        · rw [show ell a₀ lg lb a = lb by unfold ell; rw [if_neg h0],
            show ell a₁ lg lb a = lb by unfold ell; rw [if_neg h1], rowAff_self]
          simp [h0, h1]
    · simp only [if_neg hs, rowAff_self]
      simp [hs]
  rw [Finset.prod_congr rfl (fun sa _ ↦ hrow sa)] at hT
  have hprod : ∏ sa : State × Action,
      (if sa = (s₀, a₀) ∨ sa = (s₀, a₁) then α else 1) ^ N = α ^ N * α ^ N := by
    rw [Finset.prod_eq_mul_of_mem (s₀, a₀) (s₀, a₁) (Finset.mem_univ _) (Finset.mem_univ _)
      (by simp [ha])]
    · simp
    · intro c _ hc
      simp [hc.1, hc.2]
  rw [hprod] at hT
  -- `α^(4N) ≥ 1/2`
  have hαpos : 0 < α := by
    have h1 : 0 < Real.sqrt lg * Real.sqrt lb :=
      mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_pos.2 hlb)
    have h2 : 0 ≤ Real.sqrt (1 - lg) * Real.sqrt (1 - lb) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  have hlog := bernoulli_log_affinity hlb hlbg hlg
  rw [← hα] at hlog
  have hpow : (α ^ N * α ^ N) ^ 2 = Real.exp (4 * N * Real.log α) := by
    rw [show (4 : ℝ) * N * Real.log α = ((4 * N : ℕ) : ℝ) * Real.log α by push_cast; ring,
      ← Real.log_pow, Real.exp_log (pow_pos hαpos _)]
    ring
  have hexp : Real.exp (-Real.log 2) ≤ Real.exp (4 * N * Real.log α) := by
    apply Real.exp_le_exp.mpr
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 4 * N)
    nlinarith
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at hexp
  rw [hpow] at hT
  linarith

end Hard

end StatisticalRL.RobustRL.Ch7.LowerBound73
