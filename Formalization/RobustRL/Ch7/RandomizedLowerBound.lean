import Formalization.RobustRL.Ch7.LowerBound73
import Formalization.RobustRL.Ch7.LowerBound75
import Formalization.OfflineRL.LowerBoundRandomized

/-!
# Corrected Theorems 7.3 and 7.5 for externally randomized estimators

`thm:l1-lower-bound` (`chapters/robust_RL.tex:377–391`) and `thm:chi2-lower-bound`
(`chapters/robust_RL.tex:461–480`) take the infimum over all estimators `π̂`. The library exports
`LowerBound73.thm7_3_corrected(_knownReward)` and `LowerBound75.thm7_5_corrected(_knownReward)`
cover deterministic maps `data ↦ π̂(data)` (SOURCE-ISSUES C7, C38). This file covers estimators
that also use an independent seed `ω ~ ν` on an arbitrary probability space `(Ω, ν)`: the joint
law of `(ω, data)` under model `i` is `ν ⊗ P_i`, with the same models `M₀, M₁` and the same
initial distribution `μ` as the deterministic exports.

Route (no new testing argument):

* `pair_sum_of_policy_gap`: the Le Cam step of the existing proofs in sum form. If every policy
  with `π(a_j | s₀) ≤ 1/2` fails in model `j`, and the two sampling laws satisfy a two-point
  testing bound `c ≤ P₀(E₀) + P₁(E₁)` (`LowerBound73.hard_test_sum`,
  `LowerBound73.single_test_sum`), then every deterministic estimator has summed failure
  probability at least `c`.
* `max_prod_ge_of_sum`: if for every seed the sections satisfy the sum bound `c`, some model has
  joint failure probability at least `c/2` (`OfflineRL.LowerBound.
  exists_prod_measureReal_ge_of_sum_sections'`, with index `Bool`).

The per-case parameter choices (models, initial distribution, sample budget arithmetic) repeat
those of `LowerBound73.lb_two_states_knownReward`, `LowerBound73.lb_one_state`,
`LowerBound75.core_explicit`, `LowerBound75.kr_nonpos` and `LowerBound75.one_state_explicit`;
only the final step changes from `max` to the sum.

Measurability: no measurability of `π̂` in the seed is assumed. The conclusion is about
`(ν ⊗ P_i)` of the failure set; when that set is measurable this is its probability, otherwise it
is the outer probability (as in `Thm6_13_randomized`). Since the data range over a finite set,
every estimator given as a Markov kernel from data to policies is of the seeded form
(`Ω = ∏_data Policy`, `ν = ⊗_data κ(data)`, `π̂(ω, data) = ω data`). Deterministic estimators are
the case `Ω = Unit`.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.RandomizedLowerBound

universe u

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage
  StatisticalRL.RobustRL.Ch7.LowerBound73

local instance randLBStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

section Generic

/-- Two models, sum form of the seed average: if for every seed the two section probabilities
sum to at least `c`, then one of the two joint (seed ⊗ data) failure probabilities is at least
`c / 2`. -/
theorem max_prod_ge_of_sum {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P₀ P₁ : Measure D) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (F₀ F₁ : Set (Ω × D)) (c : ℝ)
    (h : ∀ ω, c ≤ P₀.real (Prod.mk ω ⁻¹' F₀) + P₁.real (Prod.mk ω ⁻¹' F₁)) :
    c / 2 ≤ max ((ν.prod P₀).real F₀) ((ν.prod P₁).real F₁) := by
  haveI : ∀ b : Bool, IsProbabilityMeasure (cond b P₁ P₀) := by
    intro b; cases b <;> assumption
  obtain ⟨b, hb⟩ := OfflineRL.LowerBound.exists_prod_measureReal_ge_of_sum_sections' (I := Bool)
    ν (fun b ↦ cond b P₁ P₀) (fun b ↦ cond b F₁ F₀) (c / 2) (fun ω ↦ by
      rw [Fintype.sum_bool, Fintype.card_bool]
      have := h ω
      simp only [cond_true, cond_false]
      linarith)
  cases b
  · exact hb.trans (le_max_left _ _)
  · exact hb.trans (le_max_right _ _)

variable {State Action : Type*} [Fintype State] [Fintype Action]

omit [Fintype State] in
/-- Le Cam step in sum form: the existing two-point testing bounds apply to the test
`1/2 < π̂(data)(a₀ | s₀)`, whose two error events lie inside the two failure events. -/
theorem pair_sum_of_policy_gap {N : ℕ}
    (P₀ P₁ : Measure (ModelBasedPolicyLearning.Samples State Action N)) (c : ℝ)
    (htest : ∀ (E₀ E₁ : Set (ModelBasedPolicyLearning.Samples State Action N))
      (test : ModelBasedPolicyLearning.Samples State Action N → Bool),
      {x | test x = false} ⊆ E₀ → {x | test x = true} ⊆ E₁ → c ≤ P₀.real E₀ + P₁.real E₁)
    (s₀ : State) {a₀ a₁ : Action} (ha : a₀ ≠ a₁) (G₀ G₁ : StationaryPolicy State Action → Prop)
    (hG₀ : ∀ π : StationaryPolicy State Action, (π s₀).prob a₀ ≤ 1 / 2 → G₀ π)
    (hG₁ : ∀ π : StationaryPolicy State Action, (π s₀).prob a₁ ≤ 1 / 2 → G₁ π)
    (est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action) :
    c ≤ P₀.real {data | G₀ (est data)} + P₁.real {data | G₁ (est data)} := by
  classical
  refine htest _ _ (fun data ↦ decide (1 / 2 < (est data s₀).prob a₀)) ?_ ?_
  · intro data hdata
    simp only [Set.mem_setOf_eq, decide_eq_false_iff_not, not_lt] at hdata
    exact hG₀ _ hdata
  · intro data hdata
    simp only [Set.mem_setOf_eq, decide_eq_true_eq] at hdata
    have hsum1 : (est data s₀).prob a₀ + (est data s₀).prob a₁ ≤ 1 := by
      have h := (est data s₀).sum_prob
      have := Finset.add_le_sum (f := (est data s₀).prob)
        (fun i _ ↦ (est data s₀).prob_nonneg i) (Finset.mem_univ a₀) (Finset.mem_univ a₁) ha
      linarith
    exact hG₁ _ (by linarith)

end Generic

/-- Deterministic sum form of the Theorem 7.3 / 7.5 conclusion (ball `ball`), without the
shared-reward clause: every deterministic estimator has summed failure probability `≥ 1/4`. -/
def SumConclusion {State : Type} [Fintype State] (ball : RowBall State) (Action : Type)
    [Fintype Action]
    (σ ε γ : ℝ) (N : ℕ) : Prop :=
  ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
    M₀.discount = γ ∧ M₁.discount = γ ∧
    ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 4 ≤
        (ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt ball M₀ σ μ -
            robustPolicyValueAt ball M₀ σ (est data) μ} +
        (ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt ball M₁ σ μ -
            robustPolicyValueAt ball M₁ σ (est data) μ}

/-- `SumConclusion` with the shared-reward clause `M₀.reward = M₁.reward`. -/
def SumConclusionKR {State : Type} [Fintype State] (ball : RowBall State) (Action : Type)
    [Fintype Action]
    (σ ε γ : ℝ) (N : ℕ) : Prop :=
  ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
    M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
    ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 4 ≤
        (ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt ball M₀ σ μ -
            robustPolicyValueAt ball M₀ σ (est data) μ} +
        (ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt ball M₁ σ μ -
            robustPolicyValueAt ball M₁ σ (est data) μ}

section Seed

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- The seed average applied to the sum form, for one fixed pair of models. -/
theorem randomized_of_sum (ball : RowBall State) (σ ε : ℝ) (N : ℕ)
    (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State)
    (H : ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 4 ≤
        (ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt ball M₀ σ μ -
            robustPolicyValueAt ball M₀ σ (est data) μ} +
        (ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt ball M₁ σ μ -
            robustPolicyValueAt ball M₁ σ (est data) μ})
    (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (est : Ω → ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action) :
    1 / 8 ≤ max
      ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
        {p | ε < robustOptimalValueAt ball M₀ σ μ -
          robustPolicyValueAt ball M₀ σ (est p.1 p.2) μ})
      ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
        {p | ε < robustOptimalValueAt ball M₁ σ μ -
          robustPolicyValueAt ball M₁ σ (est p.1 p.2) μ}) := by
  have h := max_prod_ge_of_sum ν (ModelBasedPolicyLearning.samplingLaw M₀ N)
    (ModelBasedPolicyLearning.samplingLaw M₁ N)
    {p | ε < robustOptimalValueAt ball M₀ σ μ - robustPolicyValueAt ball M₀ σ (est p.1 p.2) μ}
    {p | ε < robustOptimalValueAt ball M₁ σ μ - robustPolicyValueAt ball M₁ σ (est p.1 p.2) μ}
    (1 / 4) (fun ω ↦ H (est ω))
  linarith

end Seed

section Thm73

/-- Sum form of `LowerBound73.lb_two_states_knownReward` (`S ≥ 2`, `A ≥ 2`): the same hard pair,
initial distribution and budget arithmetic; the last step keeps the sum instead of the `max`. -/
theorem lb73_two_states_sum {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (State Action : Type)
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ)
    (hS : 2 ≤ Fintype.card State) (hA : 2 ≤ Fintype.card Action) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεle : ε ≤ c₀ / (256 * (1 - γ)))
    (hN : (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2)) :
    SumConclusionKR (tvBall (State := State)) Action σ ε γ N := by
  classical
  obtain ⟨s₀, s₁, hs⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card State)
  obtain ⟨a₀, a₁, ha⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Action)
  have hγ0 : 0 ≤ γ := by linarith
  set m := max (1 - γ) σ with hm
  have hm1 : 1 - γ ≤ m := le_max_left _ _
  have hmσ : σ ≤ m := le_max_right _ _
  have hm_le : m ≤ 1 := max_le (by linarith) (by linarith)
  have hmpos : 0 < m := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hε' : (1 - γ) * ε ≤ c₀ / 256 := by
    rw [le_div_iff₀ (by positivity)] at hεle
    linarith
  set Δ := 16 * (1 - γ) * m * ε with hΔdef
  have hΔpos : 0 < Δ := by positivity
  have hΔ : Δ ≤ c₀ * m / 16 := by
    have : Δ = 16 * m * ((1 - γ) * ε) := by rw [hΔdef]; ring
    rw [this]
    nlinarith
  set u := c₀ * m / 4 with hu
  have hcm : c₀ * m ≤ c₀ := by nlinarith
  have hvar := lb_variance hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle
  rw [← hm, ← hΔdef, ← hu] at hvar
  have hlbpos : 0 < σ + u - Δ := by
    have : 0 < c₀ * m := by positivity
    linarith
  have hlg : σ + u < 1 := by linarith
  have hNb : 2 * N * ((σ + u - (σ + u - Δ)) ^ 2 / ((σ + u - Δ) * (1 - (σ + u - Δ)))) ≤
      Real.log 2 := by
    rw [show σ + u - (σ + u - Δ) = Δ by ring]
    have hcm0 : 0 < c₀ * m / 16 := by positivity
    have hdiv : Δ ^ 2 / ((σ + u - Δ) * (1 - (σ + u - Δ))) ≤ Δ ^ 2 / (c₀ * m / 16) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hcm0 hvar
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hden : 0 < 8192 * (1 - γ) ^ 2 * m * ε ^ 2 := by positivity
    rw [le_div_iff₀ hden] at hN
    have heq : 2 * N * (Δ ^ 2 / (c₀ * m / 16)) =
        (N * (8192 * (1 - γ) ^ 2 * m * ε ^ 2)) / c₀ := by
      rw [hΔdef]; field_simp; ring
    have h2 : (N * (8192 * (1 - γ) ^ 2 * m * ε ^ 2)) / c₀ ≤ Real.log 2 := by
      rw [div_le_iff₀ hc₀]; linarith
    have := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * N)
    linarith
  refine ⟨hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1,
    hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1, pointMass s₀, rfl, rfl, rfl, fun est ↦ ?_⟩
  exact pair_sum_of_policy_gap _ _ (1 / 4)
    (fun E₀ E₁ test h₀ h₁ ↦ hard_test_sum hs hγ0 hγ1 (a₀ := a₀) (a₁ := a₁) ha hlbpos
      (by linarith) hlg N hNb E₀ E₁ test h₀ h₁) s₀ ha
    (fun π ↦ ε < robustOptimalValueAt tvBall (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt tvBall
          (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ π (pointMass s₀))
    (fun π ↦ ε < robustOptimalValueAt tvBall (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt tvBall
          (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ π (pointMass s₀))
    (fun π hπ ↦ hard_gap_event hs a₀ hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle π hπ)
    (fun π hπ ↦ hard_gap_event hs a₁ hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle π hπ) est

/-- Sum form of `LowerBound73.lb_one_state` (`S = 1`, `A ≥ 2`; reward-blind estimators): two
one-state models with the shared self-loop kernel and rewards `1[a = a_j]`. -/
theorem lb73_one_state_sum {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (State Action : Type)
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ)
    (hS : Fintype.card State ≤ 1) (hA : 2 ≤ Fintype.card Action) (hσ0 : 0 < σ)
    (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hεle : ε ≤ c₀ / (256 * (1 - γ))) :
    SumConclusion (tvBall (State := State)) Action σ ε γ N := by
  classical
  haveI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hS
  obtain ⟨a₀, a₁, ha⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Action)
  obtain ⟨s⟩ := (inferInstance : Nonempty State)
  have hγ0 : 0 ≤ γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hεlt : ε < 1 / (2 * (1 - γ)) := by
    rw [le_div_iff₀ (by positivity)] at hεle
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨singleMDP a₀ γ hγ0 hγ1, singleMDP a₁ γ hγ0 hγ1, pointMass s, rfl, rfl, fun est ↦ ?_⟩
  exact pair_sum_of_policy_gap _ _ (1 / 4)
    (fun E₀ E₁ test h₀ h₁ ↦ by
      have := single_test_sum hγ0 hγ1 a₀ a₁ N E₀ E₁ test h₀ h₁
      linarith) s ha
    (fun π ↦ ε < robustOptimalValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ π (pointMass s))
    (fun π ↦ ε < robustOptimalValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ π (pointMass s))
    (fun π hπ ↦ by
      have := single_gap a₀ hγ0 hγ1 hσ0.le π s hπ
      show ε < _
      linarith)
    (fun π hπ ↦ by
      have := single_gap a₁ hγ0 hγ1 hσ0.le π s hπ
      show ε < _
      linarith) est

/-- **Corrected Theorem 7.3, known-reward reading, externally randomized estimators**
(`thm:l1-lower-bound`, `chapters/robust_RL.tex:377–391`; `S ≥ 2`, `A ≥ 2`, shared reward; C38).
Same hypotheses, models and initial distribution as `LowerBound73.thm7_3_corrected_knownReward`;
the estimator is any `π̂ : Ω → data → policy` with an independent seed `ω ~ ν`. -/
theorem thm7_3_corrected_knownReward_randomized :
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
      (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt tvBall M₀ σ μ -
                robustPolicyValueAt tvBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt tvBall M₁ σ μ -
                robustPolicyValueAt tvBall M₁ σ (est p.1 p.2) μ}) := by
  intro c₀ hc₀ hc₀' State Action _ _ _ _ γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN
  obtain ⟨M₀, M₁, μ, h0, h1, hr, H⟩ :=
    lb73_two_states_sum hc₀ hc₀' State Action γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN
  exact ⟨M₀, M₁, μ, h0, h1, hr, fun Ω _ ν _ est ↦ randomized_of_sum tvBall σ ε N M₀ M₁ μ H Ω ν est⟩

/-- **Corrected Theorem 7.3, externally randomized estimators** (`thm:l1-lower-bound`,
`chapters/robust_RL.tex:377–391`, with `A ≥ 2`; C38). Same hypotheses, models and initial
distribution as `LowerBound73.thm7_3_corrected`; the estimator is any `π̂ : Ω → data → policy`
with an independent seed `ω ~ ν`. -/
theorem thm7_3_corrected_randomized :
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card Action →
      0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
      (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt tvBall M₀ σ μ -
                robustPolicyValueAt tvBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt tvBall M₁ σ μ -
                robustPolicyValueAt tvBall M₁ σ (est p.1 p.2) μ}) := by
  intro c₀ hc₀ hc₀' State Action _ _ _ _ γ σ ε N hA hσ0 hσ1 hγ hγ1 hε hεle hN
  have hsum : SumConclusion (tvBall (State := State)) Action σ ε γ N := by
    rcases Nat.lt_or_ge (Fintype.card State) 2 with hS | hS
    · exact lb73_one_state_sum hc₀ hc₀' State Action γ σ ε N (by omega) hA hσ0 hγ hγ1 hεle
    · obtain ⟨M₀, M₁, μ, h0, h1, -, H⟩ :=
        lb73_two_states_sum hc₀ hc₀' State Action γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN
      exact ⟨M₀, M₁, μ, h0, h1, H⟩
  obtain ⟨M₀, M₁, μ, h0, h1, H⟩ := hsum
  exact ⟨M₀, M₁, μ, h0, h1, fun Ω _ ν _ est ↦ randomized_of_sum tvBall σ ε N M₀ M₁ μ H Ω ν est⟩

end Thm73

section Thm75

open StatisticalRL.RobustRL.Ch7.LowerBound75

/-- Sum form of `LowerBound75.core_explicit` (`S ≥ 2`, `A ≥ 2`, `ε > 0`, `c₃ = 1/512`,
`c₄ = 1/5308416`): the same hard pair, initial distribution and budget arithmetic; the last step
keeps the sum instead of the `max`. -/
theorem core75_sum (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hε : 0 < ε) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hεle : ε ≤ 1 / 512 / (1 - γ))
    (hN : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ))) :
    SumConclusionKR (chiBall (State := State)) Action σ ε γ N := by
  classical
  obtain ⟨s₀, s₁, hs⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card State)
  obtain ⟨a₀, a₁, ha⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Action)
  have hγ0 : 0 ≤ γ := by linarith
  have hh0 : 0 < 1 - γ := by linarith
  have hh1 : 1 - γ ≤ 1 / 4 := by linarith
  have hhε : (1 - γ) * ε ≤ 1 / 512 := by
    rw [le_div_iff₀ hh0] at hεle; linarith
  obtain ⟨hs0, hs2, hu, hsu, hd⟩ := uf_spec (h := 1 - γ) hσ.le hh0
  set s := Real.sqrt σ with hsdef
  set u := uf σ (1 - γ) with hudef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN' : (N : ℝ) * ((1 - γ) ^ 4 * ε ^ 2) ≤ 1 / 5308416 * ((1 - γ) + s ^ 2) := by
    have := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 4 * ε ^ 2)
    have e : 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) *
        ((1 - γ) ^ 4 * ε ^ 2) = 1 / 5308416 * ((1 - γ) + σ) := by
      field_simp
    rw [e] at this
    rw [hs2]; exact this
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hδu := df_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hdiff := tdiff_lower hs0 hu hsu hd hh0 hh1 hε hhε
  have htg := tg_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hNb := test_budget hs0 hu hsu hd hh0 hh1 hε hhε hN0 hN'
  set δ := df s u (1 - γ) ε with hδdef
  have hpg : ChiPair σ (ellf (u + δ)) (tf s (u + δ)) := chiPair_of hs0 hs2 (by linarith)
    (by linarith)
  have hpb : ChiPair σ (ellf u) (tf s u) := chiPair_of hs0 hs2 hu hsu
  have hlbg : ellf u ≤ ellf (u + δ) := by
    have := ellf_diff (u := u) δ
    have : 0 ≤ δ * (2 * u + δ) / ((1 + u ^ 2) * (1 + (u + δ) ^ 2)) := by positivity
    linarith
  have hTbg : tf s u ≤ tf s (u + δ) := by
    have : 0 ≤ 32 * (1 - γ) ^ 2 * ε := by positivity
    linarith
  have hgap : ∀ b, 0 ≤ b → b ≤ tf s (u + δ) - (tf s (u + δ) - tf s u) / 2 →
      ε < ychi γ (tf s (u + δ)) - ychi γ b := by
    intro b hb0 hb
    exact chi_gap_gt hγ hγ1 hε hb0 hb hdiff htg
  set lg := ellf (u + δ) with hlg
  set lb := ellf u with hlb
  refine ⟨hardMDP hs a₀ γ lg lb hγ0 hγ1, hardMDP hs a₁ γ lg lb hγ0 hγ1, pointMass s₀,
    rfl, rfl, rfl, fun est ↦ ?_⟩
  exact pair_sum_of_policy_gap _ _ (1 / 4)
    (fun E₀ E₁ test h₀ h₁ ↦ hard_test_sum hs hγ0 hγ1 (a₀ := a₀) (a₁ := a₁) ha hpb.pos hlbg
      hpg.lt_one N hNb E₀ E₁ test h₀ h₁) s₀ ha
    (fun π ↦ ε < robustOptimalValueAt chiBall (hardMDP hs a₀ γ lg lb hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt chiBall
          (hardMDP hs a₀ γ lg lb hγ0 hγ1) σ π (pointMass s₀))
    (fun π ↦ ε < robustOptimalValueAt chiBall (hardMDP hs a₁ γ lg lb hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt chiBall
          (hardMDP hs a₁ γ lg lb hγ0 hγ1) σ π (pointMass s₀))
    (fun π hπ ↦ chi_gap_event hs a₀ hγ0 hγ1 hσ.le hpg hpb hTbg hgap π hπ)
    (fun π hπ ↦ chi_gap_event hs a₁ hγ0 hγ1 hσ.le hpg hpb hTbg hgap π hπ) est

/-- Sum form of `LowerBound75.kr_nonpos` (`ε ≤ 0`): for `ε < 0` both failure events are sure
(`gap_nonneg`); at `ε = 0` the Lean value `c₄/0 = 0` forces `N = 0` and the core case at the
admissible accuracy `ε' = (1/512)/(1-γ)` applies, since a gap `> ε'` is a gap `> 0`. -/
theorem nonpos75_sum (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hε : ε ≤ 0) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hN : (N : ℝ) ≤ 1 / 5308416 / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ))) :
    SumConclusionKR (chiBall (State := State)) Action σ ε γ N := by
  have hh0 : 0 < 1 - γ := by linarith
  set ε' : ℝ := 1 / 512 / (1 - γ) with hε'
  have hε'0 : 0 < ε' := by positivity
  rcases hε.lt_or_eq with hneg | hzero
  · obtain ⟨M₀, M₁, μ, h0, h1, hr, -⟩ := core75_sum State Action γ σ ε' 0 hS hA hε'0 hγ hγ1
      hσ le_rfl (by rw [Nat.cast_zero]; positivity)
    refine ⟨M₀, M₁, μ, h0, h1, hr, fun est ↦ ?_⟩
    have huniv : {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
        robustPolicyValueAt chiBall M₀ σ (est data) μ} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      linarith [gap_nonneg M₀ hσ.le (est data) μ]
    rw [huniv, probReal_univ]
    have : 0 ≤ (ModelBasedPolicyLearning.samplingLaw M₁ N).real
        {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
          robustPolicyValueAt chiBall M₁ σ (est data) μ} := measureReal_nonneg
    linarith
  · subst hzero
    have hN0 : N = 0 := by
      have : (N : ℝ) ≤ 0 := by simpa using hN
      exact_mod_cast le_antisymm this (Nat.cast_nonneg N)
    subst hN0
    obtain ⟨M₀, M₁, μ, h0, h1, hr, H⟩ := core75_sum State Action γ σ ε' 0 hS hA hε'0 hγ
      hγ1 hσ le_rfl (by rw [Nat.cast_zero]; positivity)
    refine ⟨M₀, M₁, μ, h0, h1, hr, fun est ↦ (H est).trans (add_le_add ?_ ?_)⟩
    · refine measureReal_mono ?_ (measure_ne_top _ _)
      intro data hd
      simp only [Set.mem_setOf_eq] at hd ⊢
      linarith
    · refine measureReal_mono ?_ (measure_ne_top _ _)
      intro data hd
      simp only [Set.mem_setOf_eq] at hd ⊢
      linarith

/-- Sum form of `LowerBound75.one_state_explicit` (`S = 1`, `A ≥ 2`; reward-blind
estimators): two one-state models with the shared self-loop kernel and rewards `1[a = a_j]`. -/
theorem one_state75_sum (State Action : Type) [Fintype State] [Fintype Action]
    [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ) (hS : ¬ 2 ≤ Fintype.card State)
    (hA : 2 ≤ Fintype.card Action) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hεle : ε ≤ 1 / 512 / (1 - γ)) :
    SumConclusion (chiBall (State := State)) Action σ ε γ N := by
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
  refine ⟨singleMDP a₀ γ hγ0 hγ1, singleMDP a₁ γ hγ0 hγ1, pointMass s, rfl, rfl, fun est ↦ ?_⟩
  exact pair_sum_of_policy_gap _ _ (1 / 4)
    (fun E₀ E₁ test h₀ h₁ ↦ by
      have := single_test_sum hγ0 hγ1 a₀ a₁ N E₀ E₁ test h₀ h₁
      linarith) s ha
    (fun π ↦ ε < robustOptimalValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt chiBall (singleMDP a₀ γ hγ0 hγ1) σ π (pointMass s))
    (fun π ↦ ε < robustOptimalValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt chiBall (singleMDP a₁ γ hγ0 hγ1) σ π (pointMass s))
    (fun π hπ ↦ by
      have := chi_single_gap a₀ hγ0 hγ1 hσ.le π s hπ
      show ε < _
      linarith)
    (fun π hπ ↦ by
      have := chi_single_gap a₁ hγ0 hγ1 hσ.le π s hπ
      show ε < _
      linarith) est

/-- **Corrected Theorem 7.5, known-reward reading, externally randomized estimators**
(`thm:chi2-lower-bound`, `chapters/robust_RL.tex:461–480`; `S ≥ 2`, `A ≥ 2`, shared reward; C7),
at the constants `c₃ = 1/512`, `c₄ = 1/5308416` of `LowerBound75.thm7_5_corrected_knownReward`,
with the same models and initial distribution; the estimator is any `π̂ : Ω → data → policy`
with an independent seed `ω ~ ν`. -/
theorem thm7_5_corrected_knownReward_randomized :
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
      (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt chiBall M₀ σ μ -
                robustPolicyValueAt chiBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt chiBall M₁ σ μ -
                robustPolicyValueAt chiBall M₁ σ (est p.1 p.2) μ}) := by
  refine ⟨1 / 512, 1 / 5308416, by norm_num, by norm_num, ?_⟩
  intro State Action _ _ _ _ γ σ ε N hS hA hγ hγ1 hσ hεle hN
  have hsum : SumConclusionKR (chiBall (State := State)) Action σ ε γ N := by
    rcases lt_or_ge 0 ε with hε | hε
    · exact core75_sum State Action γ σ ε N hS hA hε hγ hγ1 hσ hεle hN
    · exact nonpos75_sum State Action γ σ ε N hS hA hε hγ hγ1 hσ hN
  obtain ⟨M₀, M₁, μ, h0, h1, hr, H⟩ := hsum
  exact ⟨M₀, M₁, μ, h0, h1, hr,
    fun Ω _ ν _ est ↦ randomized_of_sum chiBall σ ε N M₀ M₁ μ H Ω ν est⟩

/-- **Corrected Theorem 7.5, externally randomized estimators** (`thm:chi2-lower-bound`,
`chapters/robust_RL.tex:461–480`, with `A ≥ 2`; C7), at the constants `c₃ = 1/512`,
`c₄ = 1/5308416` of `LowerBound75.thm7_5_corrected`, with the same models and initial
distribution; the estimator is any `π̂ : Ω → data → policy` with an independent seed `ω ~ ν`. -/
theorem thm7_5_corrected_randomized :
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card Action →
      3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
      (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt chiBall M₀ σ μ -
                robustPolicyValueAt chiBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt chiBall M₁ σ μ -
                robustPolicyValueAt chiBall M₁ σ (est p.1 p.2) μ}) := by
  refine ⟨1 / 512, 1 / 5308416, by norm_num, by norm_num, ?_⟩
  intro State Action _ _ _ _ γ σ ε N hA hγ hγ1 hσ hεle hN
  have hsum : SumConclusion (chiBall (State := State)) Action σ ε γ N := by
    by_cases hS : 2 ≤ Fintype.card State
    · have hKR : SumConclusionKR (chiBall (State := State)) Action σ ε γ N := by
        rcases lt_or_ge 0 ε with hε | hε
        · exact core75_sum State Action γ σ ε N hS hA hε hγ hγ1 hσ hεle hN
        · exact nonpos75_sum State Action γ σ ε N hS hA hε hγ hγ1 hσ hN
      obtain ⟨M₀, M₁, μ, h0, h1, -, H⟩ := hKR
      exact ⟨M₀, M₁, μ, h0, h1, H⟩
    · exact one_state75_sum State Action γ σ ε N hS hA hγ hγ1 hσ hεle
  obtain ⟨M₀, M₁, μ, h0, h1, H⟩ := hsum
  exact ⟨M₀, M₁, μ, h0, h1,
    fun Ω _ ν _ est ↦ randomized_of_sum chiBall σ ε N M₀ M₁ μ H Ω ν est⟩

end Thm75

end StatisticalRL.RobustRL.Ch7.RandomizedLowerBound
