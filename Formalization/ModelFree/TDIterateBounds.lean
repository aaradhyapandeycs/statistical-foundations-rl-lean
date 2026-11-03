import Formalization.MDP.InfiniteReturn
import Formalization.MDP.FixedPoint

/-! Bounded synchronous TD iterates for every realized sample array.
This deterministic result does not assert the sampling law or a rate. -/
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The known reward of the evaluated stationary policy. -/
noncomputable def policyReward (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  (π s).expectation (M.reward s)

/-- Simultaneous update using the next-state samples for iteration `t + 1`. -/
noncomputable def tdIterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) : ℕ → State → ℝ
  | 0 => V₀
  | t + 1 => fun s ↦ (1 - η (t + 1)) * tdIterate M π η samples V₀ t s +
      η (t + 1) * (policyReward M π s + M.discount *
        tdIterate M π η samples V₀ t (samples (t + 1) s))

theorem policyReward_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ policyReward M π s ∧ policyReward M π s ≤ 1 :=
  ⟨(π s).expectation_nonneg (M.reward_nonneg s),
    (π s).expectation_le_const (M.reward_le_one s)⟩

/-- Source Lemma `lemma:TD-bounded`: the actual update remains in the return
interval, for any sample realization and any admissible deterministic rates. -/
theorem tdIterate_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ k, k ≤ t → 0 ≤ η k ∧ η k ≤ 1) (s : State) :
    0 ≤ tdIterate M π η samples V₀ t s ∧
      tdIterate M π η samples V₀ t s ≤ M.effectiveHorizon := by
  induction t generalizing s with
  | zero => exact h₀ s
  | succ t ih =>
    have he := hη (t + 1) (le_refl _)
    have hp : ∀ k, k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
      fun k hk ↦ hη k (Nat.le_trans hk (Nat.le_succ t))
    have hs := ih hp s
    have hn := ih hp (samples (t + 1) s)
    have hr := policyReward_bounds M π s
    have hh := M.effectiveHorizon_recursion
    have hg := M.discount_nonneg
    have htarget₀ : 0 ≤ policyReward M π s + M.discount *
        tdIterate M π η samples V₀ t (samples (t + 1) s) :=
      add_nonneg hr.1 (mul_nonneg hg hn.1)
    have htarget₁ : policyReward M π s + M.discount *
        tdIterate M π η samples V₀ t (samples (t + 1) s) ≤ M.effectiveHorizon := by
      calc
        _ ≤ 1 + M.discount * M.effectiveHorizon :=
          add_le_add hr.2 (mul_le_mul_of_nonneg_left hn.2 hg)
        _ = M.effectiveHorizon := hh
    change 0 ≤ (1 - η (t + 1)) * tdIterate M π η samples V₀ t s +
      η (t + 1) * (policyReward M π s + M.discount *
        tdIterate M π η samples V₀ t (samples (t + 1) s)) ∧ _
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr he.2) hs.1) (mul_nonneg he.1 htarget₀)
    · change (1 - η (t + 1)) * tdIterate M π η samples V₀ t s +
        η (t + 1) * (policyReward M π s + M.discount *
          tdIterate M π η samples V₀ t (samples (t + 1) s)) ≤ M.effectiveHorizon
      nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr hs.2),
        mul_nonneg he.1 (sub_nonneg.mpr htarget₁)]

/-- The comparison is the actual expected infinite trajectory return. -/
theorem tdIterate_error_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ k, k ≤ t → 0 ≤ η k ∧ η k ≤ 1) :
    ‖tdIterate M π η samples V₀ t - M.trajectoryExpectedValue π‖ ≤ M.effectiveHorizon := by
  apply (pi_norm_le_iff_of_nonneg M.effectiveHorizon_nonneg).2
  intro s
  have hi := tdIterate_bounds M π η samples V₀ h₀ t hη s
  have hv := M.trajectoryExpectedValue_bounds π s
  change |tdIterate M π η samples V₀ t s - M.trajectoryExpectedValue π s| ≤ M.effectiveHorizon
  apply abs_le.mpr
  constructor <;> dsimp [DiscountedMDP.effectiveHorizon] at * <;> linarith

end StatisticalRL.TemporalDifference
