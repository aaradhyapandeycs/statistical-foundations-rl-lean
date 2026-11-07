import Formalization.RobustRL.Ch7.LowerBound75Core
import Formalization.RobustRL.Ch7.LowerBound73SingleState

/-!
# Corrected Theorem 7.5: full case analysis

Extends the core case (`core_explicit`: `S ≥ 2`, `A ≥ 2`, `ε > 0`) to
* `ε ≤ 0` (trivial for `ε < 0`; `ε = 0` forces `N = 0` through the Lean value `c₄/0 = 0`), and
* `S = 1` (reward-blind estimators only: two one-state models differing in reward).

The one-state χ² value lemma, the gap-nonnegativity lemma and the `ε ≤ 0` / `S = 1` case
arguments are adapted from the independent review probe
(`minAt_explicit`).
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage
  StatisticalRL.RobustRL.Ch7.LowerBound73

local instance lowerBound75MainStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

-- adapted from the independent review probe 
/-- Robust gap is nonnegative for every model and policy (χ² ball, `σ ≥ 0`). -/
theorem gap_nonneg {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) {σ : ℝ} (hσ : 0 ≤ σ) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) :
    0 ≤ robustOptimalValueAt chiBall M σ μ - robustPolicyValueAt chiBall M σ π μ := by
  have := FiniteDistribution.expectation_mono μ (fun s ↦
    HorizonTrap.robustPolicyValue_le_optimal chiBall M σ
      (fun p ↦ QLearning.qChiBall_self p σ hσ) π s)
  unfold robustOptimalValueAt robustPolicyValueAt
  linarith

section Single

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action] [Nonempty State] [Subsingleton State] (g : Action) {γ : ℝ}
  (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

omit [DecidableEq State] in
/-- One-state χ² robust value: `π(g|s)/(1-γ)`. -/
theorem chi_single_value {σ : ℝ} (hσ0 : 0 ≤ σ) (π : StationaryPolicy State Action)
    (s : State) :
    robustPolicyValue chiBall (singleMDP g γ hγ0 hγ1) σ π s =
      (π s).prob g / (1 - γ) := by
  set M := singleMDP (State := State) g γ hγ0 hγ1
  have h1γ : (1 - γ) ≠ 0 := by linarith
  set W : State → ℝ := fun _ ↦ (π s).prob g / (1 - γ) with hW
  have hval : ∀ K : State → Action → FiniteDistribution State,
      (withKernel M K).trajectoryExpectedValue π s = (π s).prob g / (1 - γ) := by
    intro K
    have hfix : (withKernel M K).valueBellman π W = W := by
      funext t
      have ht : t = s := Subsingleton.elim t s
      subst ht
      rw [valueBellman_withKernel]
      have hfun : (fun a ↦ M.reward t a + M.discount * (K t a).expectation W) =
          fun a ↦ ell g 1 0 a + γ * ((π t).prob g / (1 - γ)) := by
        funext a
        rw [expectation_subsingleton _ _ t]
        rfl
      rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
        expectation_ell]
      simp only [hW]
      field_simp
      ring
    rw [(withKernel M K).trajectoryExpectedValue_eq_valueFixedPoint,
      ← ((withKernel M K).valueFixedPoint_characterization π W).mp hfix]
  have hset : {v | ∃ K, RobustAdmissible chiBall M σ K ∧
      v = (withKernel M K).trajectoryExpectedValue π s} = {(π s).prob g / (1 - γ)} := by
    ext v
    constructor
    · rintro ⟨K, -, rfl⟩
      exact hval K
    · intro hv
      rw [Set.mem_singleton_iff.mp hv]
      exact ⟨M.transition, fun _ _ ↦ QLearning.qChiBall_self _ σ hσ0, (hval _).symm⟩
  unfold robustPolicyValue
  rw [hset, csInf_singleton]

omit [DecidableEq State] in
theorem chi_single_gap {σ : ℝ} (hσ0 : 0 ≤ σ) (π : StationaryPolicy State Action) (s : State)
    (hπ : (π s).prob g ≤ 1 / 2) :
    1 / (2 * (1 - γ)) ≤
      robustOptimalValueAt chiBall (singleMDP g γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt chiBall (singleMDP g γ hγ0 hγ1) σ π (pointMass s) := by
  unfold robustOptimalValueAt robustPolicyValueAt
  rw [expectation_pointMass, expectation_pointMass]
  have hopt := HorizonTrap.robustPolicyValue_le_optimal chiBall
    (singleMDP g γ hγ0 hγ1) σ (fun p ↦ QLearning.qChiBall_self p σ hσ0)
    (detPolicy fun _ ↦ g) s
  rw [chi_single_value g hγ0 hγ1 hσ0] at hopt
  rw [chi_single_value g hγ0 hγ1 hσ0]
  have hdet : (detPolicy (fun _ : State ↦ g) s).prob g = 1 := by simp [detPolicy, pointMass]
  rw [hdet] at hopt
  have h1γ : 0 < 1 - γ := by linarith
  have : 1 / (2 * (1 - γ)) = 1 / (1 - γ) - (1 / 2) / (1 - γ) := by field_simp; ring
  have hle : (π s).prob g / (1 - γ) ≤ (1 / 2) / (1 - γ) :=
    div_le_div_of_nonneg_right hπ h1γ.le
  linarith

end Single


/-- `ε ≤ 0` reduces to the core case at `ε' = (1/512)/(1-γ)`, `N = 0` (adapted from the
independent review probe). -/
theorem kr_nonpos (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hε : ε ≤ 0) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hN : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ))) :
    KRConclusion State Action γ σ ε N := by
  have hh0 : 0 < 1 - γ := by linarith
  set ε' : ℝ := 1 / 512 / (1 - γ) with hε'
  have hε'0 : 0 < ε' := by positivity
  rcases hε.lt_or_eq with hneg | hzero
  · obtain ⟨M₀, M₁, μ, h0, h1, hr, -⟩ := core_explicit State Action γ σ ε' 0 hS hA hε'0 hγ hγ1
      hσ le_rfl (by rw [Nat.cast_zero]; positivity)
    refine ⟨M₀, M₁, μ, h0, h1, hr, fun est ↦ ?_⟩
    have huniv : {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
        robustPolicyValueAt chiBall M₀ σ (est data) μ} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      linarith [gap_nonneg M₀ hσ.le (est data) μ]
    rw [huniv, probReal_univ]
    exact le_trans (by norm_num) (le_max_left _ _)
  · subst hzero
    have hN0 : N = 0 := by
      have : (N : ℝ) ≤ 0 := by simpa using hN
      exact_mod_cast le_antisymm this (Nat.cast_nonneg N)
    subst hN0
    obtain ⟨M₀, M₁, μ, h0, h1, hr, H⟩ := core_explicit State Action γ σ ε' 0 hS hA hε'0 hγ
      hγ1 hσ le_rfl (by rw [Nat.cast_zero]; positivity)
    refine ⟨M₀, M₁, μ, h0, h1, hr, fun est ↦ (H est).trans (max_le_max ?_ ?_)⟩
    · refine measureReal_mono ?_ (measure_ne_top _ _)
      intro data hd
      simp only [Set.mem_setOf_eq] at hd ⊢
      linarith
    · refine measureReal_mono ?_ (measure_ne_top _ _)
      intro data hd
      simp only [Set.mem_setOf_eq] at hd ⊢
      linarith

/-- **Corrected Theorem 7.5, known-reward form, explicit constants** `c₃ = 1/512`,
`c₄ = 1/5308416`. -/
theorem thm7_5_corrected_knownReward_at_explicit :
    Thm7_5_corrected_knownReward_at (1 / 512) (1 / 5308416) := by
  intro State Action _ _ _ _ γ σ ε N hS hA hγ hγ1 hσ hεle hN
  rcases lt_or_ge 0 ε with hε | hε
  · exact core_explicit State Action γ σ ε N hS hA hε hγ hγ1 hσ hεle hN
  · exact kr_nonpos State Action γ σ ε N hS hA hε hγ hγ1 hσ hN

/-- One-state case (`S = 1`, `A ≥ 2`), reward-blind estimators: two one-state models sharing
the self-loop kernel with rewards `1[a = a_j]` (adapted from the independent review probe). -/
theorem one_state_explicit (State Action : Type) [Fintype State] [Fintype Action]
    [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : ¬ 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hεle : ε ≤ 1 / 512 / (1 - γ)) :
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
              robustPolicyValueAt chiBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
              robustPolicyValueAt chiBall M₁ σ (est data) μ}) := by
  classical
  have hh0 : 0 < 1 - γ := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  have hS1 : Fintype.card State ≤ 1 := by omega
  haveI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hS1
  obtain ⟨a₀, a₁, ha⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Action)
  obtain ⟨s⟩ := (inferInstance : Nonempty State)
  have hεlt : ε < 1 / (2 * (1 - γ)) := by
    have : 1 / 512 / (1 - γ) < 1 / (2 * (1 - γ)) := by
      rw [div_lt_div_iff₀ hh0 (by positivity)]; nlinarith
    linarith
  refine ⟨singleMDP a₀ γ hγ0 hγ1, singleMDP a₁ γ hγ0 hγ1, pointMass s,
    rfl, rfl, fun est ↦ ?_⟩
  let test : ModelBasedPolicyLearning.Samples State Action N → Bool :=
    fun data ↦ decide (1 / 2 < (est data s).prob a₀)
  have hsum := single_test_sum hγ0 hγ1 a₀ a₁ N
    {data | ε < robustOptimalValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
      (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
        (est data) (pointMass s)}
    {data | ε < robustOptimalValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
      (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
        (est data) (pointMass s)}
    test ?_ ?_
  · have h₀ := le_max_left
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₀ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
          (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
            (est data) (pointMass s)})
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₁ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
          (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
            (est data) (pointMass s)})
    have h₁ := le_max_right
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₀ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
          (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ
            (est data) (pointMass s)})
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₁ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
          (pointMass s) - robustPolicyValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ
            (est data) (pointMass s)})
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_false_iff_not, not_lt] at hdata
    have := chi_single_gap a₀ hγ0 hγ1 hσ.le (est data) s hdata
    show ε < _
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_true_eq] at hdata
    have hsum1 : (est data s).prob a₀ + (est data s).prob a₁ ≤ 1 := by
      have h := (est data s).sum_prob
      have := Finset.add_le_sum (f := (est data s).prob)
        (fun i _ ↦ (est data s).prob_nonneg i) (Finset.mem_univ a₀) (Finset.mem_univ a₁) ha
      linarith
    have := chi_single_gap a₁ hγ0 hγ1 hσ.le (est data) s (by linarith)
    show ε < _
    linarith

/-- **Corrected Theorem 7.5 at the explicit constants** `c₃ = 1/512`, `c₄ = 1/5308416`
(single added hypothesis `A ≥ 2`). -/
theorem thm7_5_corrected_at_explicit : Thm7_5_corrected_at (1 / 512) (1 / 5308416) := by
  intro State Action _ _ _ _ γ σ ε N hA hγ hγ1 hσ hεle hN
  by_cases hS : 2 ≤ Fintype.card State
  · obtain ⟨M₀, M₁, μ, h0, h1, -, H⟩ :=
      thm7_5_corrected_knownReward_at_explicit State Action γ σ ε N hS hA hγ hγ1 hσ hεle hN
    exact ⟨M₀, M₁, μ, h0, h1, H⟩
  · exact one_state_explicit State Action γ σ ε N hS hA hγ hγ1 hσ hεle

/-- Monotonicity in the constants for `Thm7_5_corrected_at`. -/
theorem corrected_at_mono {c₃ c₄ c₃' c₄' : ℝ} (h3 : c₃ ≤ c₃') (h4 : c₄ ≤ c₄')
    (H : Thm7_5_corrected_at c₃' c₄') : Thm7_5_corrected_at c₃ c₄ := by
  intro State Action _ _ _ _ γ σ ε N hA hγ hγ1 hσ hεle hN
  have hh0 : 0 < 1 - γ := by linarith
  refine H State Action γ σ ε N hA hγ hγ1 hσ ?_ ?_
  · exact hεle.trans (div_le_div_of_nonneg_right h3 hh0.le)
  · refine hN.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right h4 (by positivity)

/-- Monotonicity in the constants for `Thm7_5_corrected_knownReward_at`. -/
theorem corrected_knownReward_at_mono {c₃ c₄ c₃' c₄' : ℝ} (h3 : c₃ ≤ c₃') (h4 : c₄ ≤ c₄')
    (H : Thm7_5_corrected_knownReward_at c₃' c₄') : Thm7_5_corrected_knownReward_at c₃ c₄ := by
  intro State Action _ _ _ _ γ σ ε N hS hA hγ hγ1 hσ hεle hN
  have hh0 : 0 < 1 - γ := by linarith
  refine H State Action γ σ ε N hS hA hγ hγ1 hσ ?_ ?_
  · exact hεle.trans (div_le_div_of_nonneg_right h3 hh0.le)
  · refine hN.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right h4 (by positivity)

/-- Corrected Theorem 7.5 for every `c₃ ≤ 1/512`, `c₄ ≤ 1/5308416`. -/
theorem thm7_5_corrected_at {c₃ c₄ : ℝ} (h3 : c₃ ≤ 1 / 512) (h4 : c₄ ≤ 1 / 5308416) :
    Thm7_5_corrected_at c₃ c₄ :=
  corrected_at_mono h3 h4 thm7_5_corrected_at_explicit

/-- Known-reward corrected Theorem 7.5 for every `c₃ ≤ 1/512`, `c₄ ≤ 1/5308416`. -/
theorem thm7_5_corrected_knownReward_at {c₃ c₄ : ℝ} (h3 : c₃ ≤ 1 / 512)
    (h4 : c₄ ≤ 1 / 5308416) : Thm7_5_corrected_knownReward_at c₃ c₄ :=
  corrected_knownReward_at_mono h3 h4 thm7_5_corrected_knownReward_at_explicit

/-- The `ε = 0` instance under the extended-real reading `c₄/0 = ∞` (no budget at all): the
known-reward conclusion at `ε = 0` holds for every `N`, because the models may depend on `N`.
So the Lean junk value `c₄/0 = 0` (which forces `N = 0`) only weakens that instance. Adapted from
the independent review probe (`eps0_anyN`). -/
theorem eps0_anyN (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ : ℝ) (N : ℕ) (hS : 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ) :
    KRConclusion State Action γ σ 0 N := by
  have hh0 : 0 < 1 - γ := by linarith
  have hh1 : 1 - γ ≤ 1 / 4 := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set e : ℝ := 1 / (5308416 * ((N : ℝ) + 1)) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 5308416 := by
    rw [he]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hNe : (N : ℝ) * e ≤ 1 / 5308416 := by
    rw [he]; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hεle : e ≤ 1 / 512 / (1 - γ) := by
    rw [le_div_iff₀ hh0]; nlinarith
  have hh3 : (1 - γ) ^ 3 ≤ 1 := pow_le_one₀ hh0.le (by linarith)
  have key : (N : ℝ) * ((1 - γ) ^ 3 * e ^ 2) ≤ 1 / 5308416 := by
    have h1 : (N : ℝ) * ((1 - γ) ^ 3 * e ^ 2) ≤ (N : ℝ) * e * e := by
      have : (1 - γ) ^ 3 * e ^ 2 ≤ e * e := by nlinarith [sq_nonneg e]
      nlinarith
    have h2 : (N : ℝ) * e * e ≤ 1 / 5308416 * 1 := by
      apply mul_le_mul hNe (by linarith) he0.le (by norm_num)
    linarith
  have hN : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * e ^ 2) * (1 + σ / (1 - γ)) := by
    have hpos : 0 < (1 - γ) ^ 3 * e ^ 2 := by positivity
    have : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * e ^ 2) := by rw [le_div_iff₀ hpos]; exact key
    refine this.trans (le_mul_of_one_le_right (by positivity) ?_)
    have : 0 ≤ σ / (1 - γ) := by positivity
    linarith
  obtain ⟨M₀, M₁, μ, h0, h1, hr, H⟩ :=
    core_explicit State Action γ σ e N hS hA he0 hγ hγ1 hσ hεle hN
  refine ⟨M₀, M₁, μ, h0, h1, hr, fun est ↦ (H est).trans (max_le_max ?_ ?_)⟩
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro data hd; simp only [Set.mem_setOf_eq] at hd ⊢; linarith
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro data hd; simp only [Set.mem_setOf_eq] at hd ⊢; linarith

/-- **Corrected Theorem 7.5** (`thm:chi2-lower-bound`, `robust_RL.tex:461–480`, with `A ≥ 2`;
SOURCE-ISSUES C7). -/
theorem thm7_5_corrected : Thm7_5_corrected :=
  ⟨1 / 512, 1 / 5308416, by norm_num, by norm_num, thm7_5_corrected_at le_rfl le_rfl⟩

/-- **Corrected Theorem 7.5, known-reward form** (`S ≥ 2`, `A ≥ 2`, shared reward; C7). -/
theorem thm7_5_corrected_knownReward : Thm7_5_corrected_knownReward :=
  ⟨1 / 512, 1 / 5308416, by norm_num, by norm_num,
    thm7_5_corrected_knownReward_at le_rfl le_rfl⟩

end StatisticalRL.RobustRL.Ch7.LowerBound75
