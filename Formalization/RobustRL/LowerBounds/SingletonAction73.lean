import Formalization.RobustRL.LowerBounds.Ch7PrintedStatements
import Formalization.RobustRL.ChiSquaredPolicyValue

/-!
# Printed Theorem 7.3 is false at `A = 1` (SOURCE-ISSUES C38)

`robust_RL.tex:377–391` places no restriction on `A`. With a single action every
stationary policy is the unique policy, so for *every* row ball, radius, model
and initial distribution the robust gap `V^{⋆,σ}(μ) - V^{π̂,σ}(μ)` is `0`, and
both strict-error probabilities vanish. The explicit admissible witness is
`S = 2, A = 1, γ = 1/2, σ = 1/2, ε = c₀/128` (the upper endpoint
`c₀/(256(1-γ))`), `N = 1`, for every `0 < c₀ ≤ 1/8`; the printed sample bound
evaluates to `16 log 2 / c₀ ≥ 1`.

Scope: this is a degenerate-domain refutation. It shows only that the printed
domain is missing a hypothesis `A ≥ 2` (reading `M₀, M₁` as RMDPs on the given
`S` states and `A` actions); it says nothing about the cited lower bound when
`A ≥ 2`, which is not proved here.
-/

open MeasureTheory

namespace StatisticalRL.RobustRL.Ch7

local instance singletonStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

section General

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- With a subsingleton action set the optimal robust value is the robust value
of any stationary policy (for every ball family, model and radius). -/
theorem robustOptimalValue_eq_of_subsingleton [Subsingleton Action]
    (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (π : StationaryPolicy State Action) (s : State) :
    robustOptimalValue ball M σ s = robustPolicyValue ball M σ π s := by
  have hrange : (Set.range fun π' : StationaryPolicy State Action ↦
      robustPolicyValue ball M σ π' s) = {robustPolicyValue ball M σ π s} := by
    ext x
    constructor
    · rintro ⟨π', rfl⟩
      rw [chiSquaredStationaryPolicy_eq_of_subsingleton π' π]
      rfl
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨π, rfl⟩
  unfold robustOptimalValue
  rw [hrange, csSup_singleton]

/-- The robust gap at any initial distribution is zero with a single action. -/
theorem robustGapAt_eq_zero_of_subsingleton [Subsingleton Action]
    (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) :
    robustOptimalValueAt ball M σ μ - robustPolicyValueAt ball M σ π μ = 0 := by
  unfold robustOptimalValueAt robustPolicyValueAt
  have : robustOptimalValue ball M σ = robustPolicyValue ball M σ π :=
    funext fun s ↦ robustOptimalValue_eq_of_subsingleton ball M σ π s
  rw [this, sub_self]

/-- Every estimator has zero strict-error probability with a single action. -/
theorem robustRisk_eq_zero_of_subsingleton [Subsingleton Action]
    (ball : RowBall State) (M : DiscountedMDP State Action) (σ ε : ℝ) (hε : 0 < ε)
    (μ : FiniteDistribution State) (N : ℕ)
    (est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action) :
    (ModelBasedPolicyLearning.samplingLaw M N).real
      {data | ε < robustOptimalValueAt ball M σ μ - robustPolicyValueAt ball M σ (est data) μ}
      = 0 := by
  have hempty : {data : ModelBasedPolicyLearning.Samples State Action N |
      ε < robustOptimalValueAt ball M σ μ - robustPolicyValueAt ball M σ (est data) μ} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [robustGapAt_eq_zero_of_subsingleton]
    exact hε.le
  rw [hempty]
  simp

end General

/-- The printed sample-size bound at the witness `γ = σ = 1/2`, `ε = c₀/128`
allows `N = 1`. -/
theorem thm7_3_witness_sampleBound (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) :
    ((1 : ℕ) : ℝ) ≤ c₀ * Real.log 2 /
      (8192 * (1 - 1 / 2 : ℝ) ^ 2 * max (1 - 1 / 2 : ℝ) (1 / 2) * (c₀ / 128) ^ 2) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    linarith
  have hden : (8192 * (1 - 1 / 2 : ℝ) ^ 2 * max (1 - 1 / 2 : ℝ) (1 / 2) * (c₀ / 128) ^ 2)
      = c₀ ^ 2 / 16 := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, max_self]
    ring
  rw [hden, le_div_iff₀ (by positivity)]
  push_cast
  nlinarith

/-- **C38.** The printed Theorem 7.3 fails at every constant `0 < c₀ ≤ 1/8`
(witness `S = 2, A = 1, γ = σ = 1/2, ε = c₀/128, N = 1`). -/
theorem not_thm7_3_printed_at (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1 / 8) :
    ¬ Thm7_3_printed_at c₀ := by
  intro h
  have hε : (0 : ℝ) < c₀ / 128 := by positivity
  obtain ⟨M₀, M₁, μ, -, -, hall⟩ := h (Fin 2) (Fin 1) (1 / 2) (1 / 2) (c₀ / 128) 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) hε
    (by rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]; apply le_of_eq; ring)
    (thm7_3_witness_sampleBound c₀ hc₀ hc₀')
  have hmax := hall (fun _ _ ↦ EnvironmentStage.pointMass 0)
  rw [robustRisk_eq_zero_of_subsingleton tvBall M₀ (1 / 2) (c₀ / 128) hε μ 1,
    robustRisk_eq_zero_of_subsingleton tvBall M₁ (1 / 2) (c₀ / 128) hε μ 1] at hmax
  norm_num at hmax

/-- **C38.** The printed Theorem 7.3, read as "for every `c₀ ∈ (0, 1/8]`", is
false. See also `not_thm7_3_exists_c0` (weakest reading: some admissible `c₀`)
and `not_thm7_3_printed_small` ("sufficiently small `c₀`"). -/
theorem not_thm7_3_printed : ¬ Thm7_3_printed := fun h ↦
  not_thm7_3_printed_at (1 / 8) (by norm_num) le_rfl (h (1 / 8) (by norm_num) le_rfl)

/-- The "sufficiently small `c₀`" reading is refuted as well. -/
theorem not_thm7_3_printed_small :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ min c (1 / 8) → Thm7_3_printed_at c₀ := by
  rintro ⟨c, hc, h⟩
  have hpos : 0 < min c (1 / 8) := lt_min hc (by norm_num)
  exact not_thm7_3_printed_at (min c (1 / 8)) hpos (min_le_right _ _)
    (h _ hpos le_rfl)

/-- **C38, weakest reading.** No admissible constant `c₀ ∈ (0, 1/8]` makes the
printed Theorem 7.3 true. -/
theorem not_thm7_3_exists_c0 :
    ¬ ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 8 ∧ Thm7_3_printed_at c₀ := by
  rintro ⟨c₀, h0, h1, h⟩
  exact not_thm7_3_printed_at c₀ h0 h1 h

end StatisticalRL.RobustRL.Ch7
