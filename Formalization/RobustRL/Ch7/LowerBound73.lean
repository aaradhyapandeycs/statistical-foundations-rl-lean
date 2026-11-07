import Formalization.RobustRL.Ch7.LowerBound73SingleState
import Formalization.RobustRL.Ch7.Ch7PrintedStatements

/-!
# Corrected Theorem 7.3: gap event and assembly

Parameters (`m = max(1-γ,σ)`): `u = c₀ m/4`, `Δ = 16(1-γ) m ε`, `lg = σ + u`, `lb = lg - Δ`.
`M_j = hardMDP h a_j γ lg lb`, `μ = δ_{s₀}`. Any policy with `π(a_j|s₀) ≤ 1/2` has robust gap
`> ε` in `M_j` (`hard_gap_event`), and the testing bound gives the printed `1/8`. The two
models share the reward and differ only in the nominal rows at `(s₀, a₀)` and `(s₀, a₁)`
(`thm7_3_corrected_knownReward`). The one-state case (`lb_one_state`) uses reward-only
differences and therefore relies on the estimator not seeing the reward.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound73

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage

section Algebra

theorem yfun_sub {γ σ u w : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ0 : 0 ≤ σ) (hu : 0 ≤ u)
    (hw : 0 ≤ w) :
    yfun γ σ u - yfun γ σ w = γ * (1 - γ + γ * σ) * (u - w) /
      ((1 - γ) * (1 - γ + γ * σ + γ * u) * (1 - γ + γ * σ + γ * w)) := by
  have h1 : (1 - γ) ≠ 0 := by linarith
  have hσ' := mul_nonneg hγ0 hσ0
  have hu' := mul_nonneg hγ0 hu
  have hw' := mul_nonneg hγ0 hw
  have h2 : (1 - γ + γ * σ + γ * u) ≠ 0 := by linarith
  have h3 : (1 - γ + γ * σ + γ * w) ≠ 0 := by linarith
  unfold yfun
  rw [div_sub_div _ _ (mul_ne_zero h1 h2) (mul_ne_zero h1 h3),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h1 h3))
      (mul_ne_zero (mul_ne_zero h1 h2) h3)]
  ring

/-- Robust gap bound: if the robust leave probability is at most `u - Δ/2`, the gap to
`yfun u` exceeds `ε`. -/
theorem gap_gt {c₀ γ σ ε w : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεle : ε ≤ c₀ / (256 * (1 - γ))) (hw0 : 0 ≤ w)
    (hw : w ≤ c₀ * max (1 - γ) σ / 4 - 16 * (1 - γ) * max (1 - γ) σ * ε / 2) :
    ε < yfun γ σ (c₀ * max (1 - γ) σ / 4) - yfun γ σ w := by
  set m := max (1 - γ) σ with hm
  have hm1 : 1 - γ ≤ m := le_max_left _ _
  have hmσ : σ ≤ m := le_max_right _ _
  have hm_le : m ≤ 1 := max_le (by linarith) (by linarith)
  have hmpos : 0 < m := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  set B := 1 - γ + γ * σ with hB
  have hγσ : 0 ≤ γ * σ := mul_nonneg hγ0 hσ0.le
  have hBpos : 0 < B := by linarith
  have hB2m : B ≤ 2 * m := by nlinarith
  have hmB : m ≤ 2 * B := max_le (by linarith) (by nlinarith)
  have hε' : (1 - γ) * ε ≤ c₀ / 256 := by
    rw [le_div_iff₀ (by positivity)] at hεle
    linarith
  set u := c₀ * m / 4 with hu
  have hupos : 0 ≤ u := by positivity
  have hγu : γ * u ≤ B / 16 := by
    have : γ * u ≤ u := by nlinarith
    have : u ≤ m / 32 := by rw [hu]; nlinarith
    linarith
  have hwu : w ≤ u := by
    have : 0 ≤ 16 * (1 - γ) * m * ε / 2 := by positivity
    linarith
  rw [yfun_sub hγ0 hγ1 hσ0.le hupos hw0, lt_div_iff₀ (by positivity)]
  have hγw : γ * w ≤ γ * u := mul_le_mul_of_nonneg_left hwu hγ0
  have h1 : (B + γ * u) * (B + γ * w) ≤ (17 / 16 * B) ^ 2 := by
    have a1 : B + γ * w ≤ 17 / 16 * B := by linarith
    have a2 : B + γ * u ≤ 17 / 16 * B := by linarith
    have := mul_le_mul a2 a1 (by nlinarith [mul_nonneg hγ0 hw0]) (by linarith)
    nlinarith
  have h2 : (17 / 16 * B) ^ 2 < 8 * γ * B * m := by
    have hγm : 1 / 2 * m ≤ γ * m := mul_le_mul_of_nonneg_right hγ hmpos.le
    have h2B : 2 * B ≤ 8 * γ * m := by linarith
    have h2a : 2 * B * B ≤ 8 * γ * m * B := mul_le_mul_of_nonneg_right h2B hBpos.le
    have hBB : 0 < B * B := mul_pos hBpos hBpos
    have he : (17 / 16 * B) ^ 2 = 289 / 256 * (B * B) := by ring
    have he2 : 8 * γ * B * m = 8 * γ * m * B := by ring
    rw [he, he2]
    linarith
  have h3 : 8 * (1 - γ) * m * ε ≤ u - w := by linarith
  have hP : 0 < (1 - γ) * ε := by positivity
  calc ε * ((1 - γ) * (B + γ * u) * (B + γ * w))
      = ((1 - γ) * ε) * ((B + γ * u) * (B + γ * w)) := by ring
    _ ≤ ((1 - γ) * ε) * (17 / 16 * B) ^ 2 := mul_le_mul_of_nonneg_left h1 hP.le
    _ < ((1 - γ) * ε) * (8 * γ * B * m) := mul_lt_mul_of_pos_left h2 hP
    _ = γ * B * (8 * (1 - γ) * m * ε) := by ring
    _ ≤ γ * B * (u - w) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- (R4): the Bernoulli variance at `lb` is at least `c₀ m/16`. -/
theorem lb_variance {c₀ γ σ ε : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεle : ε ≤ c₀ / (256 * (1 - γ))) :
    c₀ * max (1 - γ) σ / 16 ≤
      (σ + c₀ * max (1 - γ) σ / 4 - 16 * (1 - γ) * max (1 - γ) σ * ε) *
        (1 - (σ + c₀ * max (1 - γ) σ / 4 - 16 * (1 - γ) * max (1 - γ) σ * ε)) := by
  set m := max (1 - γ) σ with hm
  have hm1 : 1 - γ ≤ m := le_max_left _ _
  have hmσ : σ ≤ m := le_max_right _ _
  have hm_le : m ≤ 1 := max_le (by linarith) (by linarith)
  have hmpos : 0 < m := by linarith
  have hε' : (1 - γ) * ε ≤ c₀ / 256 := by
    rw [le_div_iff₀ (by nlinarith)] at hεle
    linarith
  have hΔ0 : 0 ≤ 16 * (1 - γ) * m * ε := by
    have : 0 ≤ 1 - γ := by linarith
    positivity
  have hΔ : 16 * (1 - γ) * m * ε ≤ c₀ * m / 16 := by
    have : 16 * (1 - γ) * m * ε = 16 * m * ((1 - γ) * ε) := by ring
    rw [this]
    nlinarith
  set lb := σ + c₀ * m / 4 - 16 * (1 - γ) * m * ε with hlb
  have hlb_lo : σ + 3 * c₀ * m / 16 ≤ lb := by linarith
  have hlb_hi : lb ≤ σ + c₀ * m / 4 := by linarith
  have hcm : c₀ * m ≤ c₀ := by nlinarith
  rcases le_or_gt (1 / 2) σ with hσh | hσh
  · have a1 : m / 2 ≤ lb := by nlinarith
    have a2 : 3 * c₀ / 4 ≤ 1 - lb := by linarith
    have := mul_le_mul a1 a2 (by positivity) (by linarith)
    nlinarith
  · have a1 : 3 * c₀ * m / 16 ≤ lb := by nlinarith
    have a2 : 15 / 32 ≤ 1 - lb := by linarith
    have := mul_le_mul a1 a2 (by norm_num) (by linarith)
    nlinarith

end Algebra

section Gap

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

/-- **Gap event.** In the hard model with good action `g`, every stationary policy putting
mass at most `1/2` on `g` at `s₀` has robust gap `> ε` at `μ = δ_{s₀}`. -/
theorem hard_gap_event {s₀ s₁ : State} (h : s₀ ≠ s₁) (g : Action) {c₀ γ σ ε : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hεle : ε ≤ c₀ / (256 * (1 - γ)))
    (π : StationaryPolicy State Action) (hπ : (π s₀).prob g ≤ 1 / 2) :
    ε < robustOptimalValueAt tvBall
        (hardMDP h g γ (σ + c₀ * max (1 - γ) σ / 4)
          (σ + c₀ * max (1 - γ) σ / 4 - 16 * (1 - γ) * max (1 - γ) σ * ε)
          (by linarith) hγ1) σ (pointMass s₀) -
      robustPolicyValueAt tvBall
        (hardMDP h g γ (σ + c₀ * max (1 - γ) σ / 4)
          (σ + c₀ * max (1 - γ) σ / 4 - 16 * (1 - γ) * max (1 - γ) σ * ε)
          (by linarith) hγ1) σ π (pointMass s₀) := by
  set m := max (1 - γ) σ with hm
  have hm1 : 1 - γ ≤ m := le_max_left _ _
  have hmσ : σ ≤ m := le_max_right _ _
  have hm_le : m ≤ 1 := max_le (by linarith) (by linarith)
  have hmpos : 0 < m := by linarith
  have hε' : (1 - γ) * ε ≤ c₀ / 256 := by
    rw [le_div_iff₀ (by nlinarith)] at hεle
    linarith
  set Δ := 16 * (1 - γ) * m * ε with hΔdef
  have hΔ0 : 0 ≤ Δ := by
    have : 0 ≤ 1 - γ := by linarith
    positivity
  have hΔ : Δ ≤ c₀ * m / 16 := by
    have : Δ = 16 * m * ((1 - γ) * ε) := by rw [hΔdef]; ring
    rw [this]
    nlinarith
  set u := c₀ * m / 4 with hu
  have hcm : c₀ * m ≤ c₀ := by nlinarith
  have hσlb : σ ≤ σ + u - Δ := by linarith
  have hlb : σ + u - Δ ≤ σ + u := by linarith
  have hlg : σ + u ≤ 1 := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  have hb : ∀ p : FiniteDistribution State, p ∈ (tvBall p σ : Set (FiniteDistribution State)) :=
    (HorizonTrap.tvBall_trapBall hσ0.le).self_mem
  unfold robustOptimalValueAt robustPolicyValueAt
  rw [expectation_pointMass, expectation_pointMass]
  have hopt := HorizonTrap.robustPolicyValue_le_optimal tvBall
    (hardMDP h g γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ hb (detPolicy fun _ ↦ g) s₀
  rw [hard_robustPolicyValue h g hγ0 hγ1 hσ0.le hσlb hlb hlg] at hopt
  rw [hard_robustPolicyValue h g hγ0 hγ1 hσ0.le hσlb hlb hlg]
  have hdet : (detPolicy (fun _ : State ↦ g) s₀).expectation (ell g (σ + u) (σ + u - Δ)) =
      σ + u := by
    simp [detPolicy, ell]
  rw [hdet, show σ + u - σ = u by ring] at hopt
  rw [expectation_ell] at ⊢
  have hπ0 := (π s₀).prob_nonneg g
  have hw0 : 0 ≤ σ + u - Δ + (π s₀).prob g * (σ + u - (σ + u - Δ)) - σ := by
    nlinarith
  have hw : σ + u - Δ + (π s₀).prob g * (σ + u - (σ + u - Δ)) - σ ≤ u - Δ / 2 := by
    have : (π s₀).prob g * Δ ≤ 1 / 2 * Δ := mul_le_mul_of_nonneg_right hπ hΔ0
    nlinarith
  have hgap := gap_gt hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle hw0 hw
  linarith

end Gap

local instance thm73LowerBoundStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- The conclusion of (corrected) Theorem 7.3 for fixed data. -/
def LBConclusion (State Action : Type) [Fintype State] [Fintype Action] (γ σ ε : ℝ) (N : ℕ) :
    Prop :=
  ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
    M₀.discount = γ ∧ M₁.discount = γ ∧
    ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 8 ≤ max
        ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt tvBall M₀ σ μ -
            robustPolicyValueAt tvBall M₀ σ (est data) μ})
        ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt tvBall M₁ σ μ -
            robustPolicyValueAt tvBall M₁ σ (est data) μ})

/-- The conclusion of `lb_two_states_knownReward`: as `LBConclusion`, with a shared reward. -/
def LBConclusionKR (State Action : Type) [Fintype State] [Fintype Action] (γ σ ε : ℝ)
    (N : ℕ) : Prop :=
  ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
    M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
    ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
      1 / 8 ≤ max
        ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
          {data | ε < robustOptimalValueAt tvBall M₀ σ μ -
            robustPolicyValueAt tvBall M₀ σ (est data) μ})
        ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
          {data | ε < robustOptimalValueAt tvBall M₁ σ μ -
            robustPolicyValueAt tvBall M₁ σ (est data) μ})

/-- One-state case (`S = 1`, `A ≥ 2`): shared self-loop kernel, rewards `1[a = a_j]`. -/
theorem lb_one_state {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (State Action : Type)
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ)
    (hS : Fintype.card State ≤ 1) (hA : 2 ≤ Fintype.card Action) (hσ0 : 0 < σ)
    (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hεle : ε ≤ c₀ / (256 * (1 - γ))) :
    LBConclusion State Action γ σ ε N := by
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
  refine ⟨singleMDP a₀ γ hγ0 hγ1, singleMDP a₁ γ hγ0 hγ1, pointMass s, rfl, rfl, ?_⟩
  intro est
  let test : ModelBasedPolicyLearning.Samples State Action N → Bool :=
    fun data ↦ decide (1 / 2 < (est data s).prob a₀)
  have hsum := single_test_sum hγ0 hγ1 a₀ a₁ N
    {data | ε < robustOptimalValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (est data) (pointMass s)}
    {data | ε < robustOptimalValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (est data) (pointMass s)}
    test ?_ ?_
  · have h₀ := le_max_left
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₀ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (pointMass s) -
          robustPolicyValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (est data) (pointMass s)})
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₁ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (pointMass s) -
          robustPolicyValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (est data) (pointMass s)})
    have h₁ := le_max_right
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₀ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (pointMass s) -
          robustPolicyValueAt tvBall (singleMDP a₀ γ hγ0 hγ1) σ (est data) (pointMass s)})
      ((ModelBasedPolicyLearning.samplingLaw (singleMDP a₁ γ hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (pointMass s) -
          robustPolicyValueAt tvBall (singleMDP a₁ γ hγ0 hγ1) σ (est data) (pointMass s)})
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_false_iff_not, not_lt] at hdata
    have := single_gap a₀ hγ0 hγ1 hσ0.le (est data) s hdata
    show ε < _
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_true_eq] at hdata
    have hsum1 : (est data s).prob a₀ + (est data s).prob a₁ ≤ 1 := by
      have h := (est data s).sum_prob
      have := Finset.add_le_sum (f := (est data s).prob)
        (fun i _ ↦ (est data s).prob_nonneg i) (Finset.mem_univ a₀) (Finset.mem_univ a₁) ha
      linarith
    have := single_gap a₁ hγ0 hγ1 hσ0.le (est data) s (by linarith)
    show ε < _
    linarith

/-- Case `S ≥ 2`, `A ≥ 2`: two models with one shared reward that differ only in the nominal
rows at `(s₀, a₀)` and `(s₀, a₁)`. -/
theorem lb_two_states_knownReward {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (State Action : Type)
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ)
    (hS : 2 ≤ Fintype.card State) (hA : 2 ≤ Fintype.card Action) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεle : ε ≤ c₀ / (256 * (1 - γ)))
    (hN : (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2)) :
    LBConclusionKR State Action γ σ ε N := by
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
  refine ⟨hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1,
    hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1, pointMass s₀, rfl, rfl, rfl, ?_⟩
  intro est
  let test : ModelBasedPolicyLearning.Samples State Action N → Bool :=
    fun data ↦ decide (1 / 2 < (est data s₀).prob a₀)
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
  have hsum := hard_test_sum hs hγ0 hγ1 (a₀ := a₀) (a₁ := a₁) ha hlbpos (by linarith) hlg N hNb
    {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt tvBall
          (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)}
    {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
        (pointMass s₀) - robustPolicyValueAt tvBall
          (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)}
    test ?_ ?_
  · have h₀ := le_max_left
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
          (pointMass s₀) - robustPolicyValueAt tvBall
            (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)})
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
          (pointMass s₀) - robustPolicyValueAt tvBall
            (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)})
    have h₁ := le_max_right
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
          (pointMass s₀) - robustPolicyValueAt tvBall
            (hardMDP hs a₀ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)})
      ((ModelBasedPolicyLearning.samplingLaw (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) N).real
        {data | ε < robustOptimalValueAt tvBall (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ
          (pointMass s₀) - robustPolicyValueAt tvBall
            (hardMDP hs a₁ γ (σ + u) (σ + u - Δ) hγ0 hγ1) σ (est data) (pointMass s₀)})
    linarith
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_false_iff_not, not_lt] at hdata
    exact hard_gap_event hs a₀ hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle (est data) hdata
  · intro data hdata
    simp only [Set.mem_setOf_eq, test, decide_eq_true_eq] at hdata
    have hsum1 : (est data s₀).prob a₀ + (est data s₀).prob a₁ ≤ 1 := by
      have h := (est data s₀).sum_prob
      have := Finset.add_le_sum (f := (est data s₀).prob)
        (fun i _ ↦ (est data s₀).prob_nonneg i) (Finset.mem_univ a₀) (Finset.mem_univ a₁) ha
      linarith
    exact hard_gap_event hs a₁ hc₀ hc₀' hσ0 hσ1 hγ hγ1 hε hεle (est data) (by linarith)

/-- Case `S ≥ 2`, `A ≥ 2` without the shared-reward conjunct. -/
theorem lb_two_states {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) (State Action : Type)
    [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] (γ σ ε : ℝ) (N : ℕ)
    (hS : 2 ≤ Fintype.card State) (hA : 2 ≤ Fintype.card Action) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 - c₀) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεle : ε ≤ c₀ / (256 * (1 - γ)))
    (hN : (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2)) :
    LBConclusion State Action γ σ ε N := by
  obtain ⟨M₀, M₁, μ, h₀, h₁, -, h⟩ :=
    lb_two_states_knownReward hc₀ hc₀' State Action γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN
  exact ⟨M₀, M₁, μ, h₀, h₁, h⟩

/-- **Corrected Theorem 7.3, known-reward reading** (`robust_RL.tex:377–391`, with `S, A ≥ 2`
and a shared reward). -/
theorem thm7_3_corrected_knownReward : Thm7_3_corrected_knownReward := by
  intro c₀ hc₀ hc₀' State Action _ _ _ _ γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN
  exact lb_two_states_knownReward hc₀ hc₀' State Action γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN

/-- **Corrected Theorem 7.3** (`thm:l1-lower-bound`, `robust_RL.tex:377–391`, with `A ≥ 2`):
case split on `S = 1` (`lb_one_state`) and `S ≥ 2` (`lb_two_states`). -/
theorem thm7_3_corrected : Thm7_3_corrected := by
  intro c₀ hc₀ hc₀' State Action _ _ _ _ γ σ ε N hA hσ0 hσ1 hγ hγ1 hε hεle hN
  rcases Nat.lt_or_ge (Fintype.card State) 2 with hS | hS
  · exact lb_one_state hc₀ hc₀' State Action γ σ ε N (by omega) hA hσ0 hγ hγ1 hεle
  · exact lb_two_states hc₀ hc₀' State Action γ σ ε N hS hA hσ0 hσ1 hγ hγ1 hε hεle hN

end StatisticalRL.RobustRL.Ch7.LowerBound73
