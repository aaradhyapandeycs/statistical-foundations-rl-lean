import Formalization.MDP.FixedPoint
import Formalization.MDP.FiniteOptimal
import Mathlib.Tactic

/-! Two-state self-loop/absorbing hard model for the source's minimax proof.
The Bellman fixed-point values are proved, not assumed. -/

open scoped BigOperators
namespace StatisticalRL.Obstructions

/-- General valid parameters for the two-state source construction. -/
structure HardParameters where
  p : ℝ
  alpha : ℝ
  gamma : ℝ
  p_nonneg : 0 ≤ p
  p_le_one : p ≤ 1
  alpha_nonneg : 0 ≤ alpha
  q_le_one : p + alpha ≤ 1
  gamma_nonneg : 0 ≤ gamma
  gamma_lt_one : gamma < 1

namespace HardParameters

def q (θ : HardParameters) : ℝ := θ.p + θ.alpha

theorem q_nonneg (θ : HardParameters) : 0 ≤ θ.q := add_nonneg θ.p_nonneg θ.alpha_nonneg

theorem q_le_one' (θ : HardParameters) : θ.q ≤ 1 := θ.q_le_one

theorem p_le_q (θ : HardParameters) : θ.p ≤ θ.q := by
  dsimp [q]
  linarith [θ.alpha_nonneg]

theorem denom_pos (θ : HardParameters) : 0 < 1 - θ.gamma * θ.q := by
  have hmul : θ.gamma * θ.q ≤ θ.gamma := by
    simpa using mul_le_mul_of_nonneg_left θ.q_le_one' θ.gamma_nonneg
  linarith [θ.gamma_lt_one]

theorem denom_p_pos (θ : HardParameters) : 0 < 1 - θ.gamma * θ.p := by
  have hmul : θ.gamma * θ.p ≤ θ.gamma := by
    simpa using mul_le_mul_of_nonneg_left θ.p_le_one θ.gamma_nonneg
  linarith [θ.gamma_lt_one]

/-- Value in the active state when the good action is followed. -/
noncomputable def goodValue (θ : HardParameters) : ℝ := 1 / (1 - θ.gamma * θ.q)

theorem goodValue_nonneg (θ : HardParameters) : 0 ≤ θ.goodValue := by
  exact div_nonneg zero_le_one θ.denom_pos.le

theorem goodValue_equation (θ : HardParameters) :
    1 + θ.gamma * θ.q * θ.goodValue = θ.goodValue := by
  unfold goodValue
  have hne : 1 - θ.gamma * θ.q ≠ 0 := ne_of_gt θ.denom_pos
  field_simp; ring

end HardParameters

variable {Action : Type*} [Fintype Action]
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- The actual two-state Bernoulli transition row, with `true` active. -/
def bernoulliRow (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : FiniteDistribution Bool where
  prob s := if s then x else 1 - x
  prob_nonneg s := by cases s <;> simp_all
  sum_prob := by simp

/-- All actions are available at both states; false is absorbing and has reward zero. -/
noncomputable def hardMDP (θ : HardParameters) (good : Action) : DiscountedMDP Bool Action where
  state_nonempty := ⟨true⟩
  action_nonempty := ⟨good⟩
  transition s a := if s then
    if a = good then bernoulliRow θ.q θ.q_nonneg θ.q_le_one'
      else bernoulliRow θ.p θ.p_nonneg θ.p_le_one
    else bernoulliRow 0 (le_refl 0) (by norm_num)
  reward s _ := if s then 1 else 0
  reward_nonneg s _ := by cases s <;> norm_num
  reward_le_one s _ := by cases s <;> norm_num
  discount := θ.gamma
  discount_nonneg := θ.gamma_nonneg
  discount_lt_one := θ.gamma_lt_one

/-- The proposed action values: take the first action, then optimally continue. -/
noncomputable def hardQ (θ : HardParameters) (good : Action) (s : Bool) (a : Action) : ℝ :=
  if s then 1 + θ.gamma * (if a = good then θ.q else θ.p) * θ.goodValue else 0

omit [Fintype Action] in
theorem hardQ_good (θ : HardParameters) (good : Action) :
    hardQ θ good true good = θ.goodValue := by
  simpa [hardQ] using θ.goodValue_equation

omit [Fintype Action] in
theorem hardQ_le_goodValue (θ : HardParameters) (good a : Action) :
    hardQ θ good true a ≤ θ.goodValue := by
  by_cases h : a = good
  · simp [h, hardQ_good]
  · rw [show hardQ θ good true a = 1 + θ.gamma * θ.p * θ.goodValue by simp [hardQ, h]]
    calc
      1 + θ.gamma * θ.p * θ.goodValue ≤ 1 + θ.gamma * θ.q * θ.goodValue := by
        have hcoef : 0 ≤ θ.gamma * θ.goodValue := mul_nonneg θ.gamma_nonneg θ.goodValue_nonneg
        nlinarith [mul_le_mul_of_nonneg_left θ.p_le_q hcoef]
      _ = θ.goodValue := θ.goodValue_equation

/-- The maximization in the actual optimality operator selects the good value. -/
theorem hardQ_max_active (θ : HardParameters) (good : Action) :
    letI : Nonempty Action := ⟨good⟩
    actionMaximum (hardQ θ good true) = θ.goodValue := by
  letI : Nonempty Action := ⟨good⟩
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro a _
    exact hardQ_le_goodValue θ good a
  · rw [← hardQ_good θ good]
    exact le_actionMaximum _ good

theorem hardQ_max_absorbing (θ : HardParameters) (good : Action) :
    letI : Nonempty Action := ⟨good⟩
    actionMaximum (hardQ θ good false) = 0 := by
  letI : Nonempty Action := ⟨good⟩
  change actionMaximum (fun _ : Action ↦ 0) = 0
  exact Finset.sup'_const _ 0

/-- Direct verification that the candidate is the model's optimality fixed point. -/
theorem hardQ_fixed (θ : HardParameters) (good : Action) :
    (hardMDP θ good).qOptimality (hardQ θ good) = hardQ θ good := by
  letI : Nonempty Action := ⟨good⟩
  funext s a
  cases s with
  | false => simp [DiscountedMDP.qOptimality, hardMDP, bernoulliRow,
      FiniteDistribution.expectation, hardQ, hardQ_max_absorbing]
  | true =>
    by_cases h : a = good <;>
      simp [DiscountedMDP.qOptimality, hardMDP, bernoulliRow, h,
        FiniteDistribution.expectation, hardQ,
        hardQ_max_active, hardQ_max_absorbing, mul_assoc]

/-- Actual optimality Bellman fixed point, for every first action. -/
theorem optimalityFixedPoint_eq_hardQ (θ : HardParameters) (good : Action) :
    (hardMDP θ good).optimalityFixedPoint = hardQ θ good := by
  exact (((hardMDP θ good).optimalityFixedPoint_characterization (hardQ θ good)).mp
    (hardQ_fixed θ good)).symm

/-- Correct optimal Bellman value after a forced suboptimal initial action. -/
theorem optimalityFixedPoint_bad (θ : HardParameters) (good a : Action) (h : a ≠ good) :
    (hardMDP θ good).optimalityFixedPoint true a =
      1 + θ.gamma * θ.p / (1 - θ.gamma * θ.q) := by
  rw [optimalityFixedPoint_eq_hardQ]
  simp [hardQ, h, HardParameters.goodValue, div_eq_mul_inv]

/-- The good initial action gives the active-state optimal Bellman value. -/
theorem optimalityFixedPoint_good (θ : HardParameters) (good : Action) :
    (hardMDP θ good).optimalityFixedPoint true good =
      1 / (1 - θ.gamma * θ.q) := by
  rw [optimalityFixedPoint_eq_hardQ, hardQ_good]
  rfl

/-- All actions at the zero-reward absorbing state have zero optimal value. -/
theorem optimalityFixedPoint_absorbing (θ : HardParameters) (good a : Action) :
    (hardMDP θ good).optimalityFixedPoint false a = 0 := by
  rw [optimalityFixedPoint_eq_hardQ]
  rfl

/-- Exact gap of the active optimal values when stay probability rises from p to q. -/
theorem hardValue_gap (θ : HardParameters) :
    1 / (1 - θ.gamma * θ.q) - 1 / (1 - θ.gamma * θ.p) =
      θ.gamma * θ.alpha / ((1 - θ.gamma * θ.q) * (1 - θ.gamma * θ.p)) := by
  have hq : 1 - θ.gamma * θ.q ≠ 0 := ne_of_gt θ.denom_pos
  have hp : 1 - θ.gamma * θ.p ≠ 0 := ne_of_gt θ.denom_p_pos
  dsimp [HardParameters.q] at *
  field_simp; ring

/-- The source's choice of α separates the good and baseline state values by
more than `2ε`; valid model probabilities are in `HardParameters`. -/
theorem hardValue_gap_gt_two (θ : HardParameters) (ε : ℝ)
    (hγ : 0 < θ.gamma) (hε : 0 < ε)
    (hα : θ.alpha = 2 * (1 - θ.gamma * θ.p) ^ 2 * ε / θ.gamma ^ 2) :
    2 * ε < 1 / (1 - θ.gamma * θ.q) - 1 / (1 - θ.gamma * θ.p) := by
  rw [hardValue_gap]
  have hαpos : 0 < θ.alpha := by
    have hp := θ.denom_p_pos
    rw [hα]
    positivity
  have hdlt : 1 - θ.gamma * θ.q < 1 - θ.gamma * θ.p := by
    dsimp [HardParameters.q]
    nlinarith [mul_pos hγ hαpos]
  have hmul : (1 - θ.gamma * θ.q) * (1 - θ.gamma * θ.p) <
      (1 - θ.gamma * θ.p) * (1 - θ.gamma * θ.p) :=
    mul_lt_mul_of_pos_right hdlt θ.denom_p_pos
  have hlt := div_lt_div_of_pos_left (mul_pos hγ hαpos)
    (mul_pos θ.denom_pos θ.denom_p_pos) hmul
  have hid : θ.gamma * θ.alpha /
      ((1 - θ.gamma * θ.p) * (1 - θ.gamma * θ.p)) = 2 * ε / θ.gamma := by
    rw [hα]
    have hg : θ.gamma ≠ 0 := ne_of_gt hγ
    have hp : 1 - θ.gamma * θ.p ≠ 0 := ne_of_gt θ.denom_p_pos
    field_simp
  rw [hid] at hlt
  have hbound : 2 * ε ≤ 2 * ε / θ.gamma := by
    apply (le_div_iff₀ hγ).2
    nlinarith [θ.gamma_lt_one]
  exact hbound.trans_lt hlt

/-- The source's hard-instance stay probability and perturbation. -/
noncomputable def sourceP (γ : ℝ) : ℝ := (4 * γ - 1) / (3 * γ)
noncomputable def sourceAlpha (γ ε : ℝ) : ℝ := 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)

/-- The printed parameter range actually gives valid transition probabilities. -/
theorem sourceHardParameters_valid (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεup : ε < 1 / (32 * (1 - γ))) :
    0 ≤ sourceP γ ∧ sourceP γ ≤ 1 ∧ 0 ≤ sourceAlpha γ ε ∧
      sourceP γ + sourceAlpha γ ε ≤ 1 := by
  have hg : 0 < γ := by linarith
  have hd : 0 < 1 - γ := by linarith
  have hd32 : 0 < 32 * (1 - γ) := by positivity
  have he : 32 * (1 - γ) * ε < 1 := by
    have h := (lt_div_iff₀ hd32).mp hεup
    nlinarith
  have he' : 32 * (1 - γ) * ε < 3 * γ := by linarith
  have he'' : 32 * (1 - γ) ^ 2 * ε < 3 * γ * (1 - γ) := by
    nlinarith [mul_lt_mul_of_pos_right he' hd]
  have hsmall : sourceAlpha γ ε < (1 - γ) / (3 * γ) := by
    unfold sourceAlpha
    apply (div_lt_div_iff₀ (by positivity : 0 < 9 * γ ^ 2)
      (by positivity : 0 < 3 * γ)).2
    nlinarith [mul_lt_mul_of_pos_right he'' (show 0 < 3 * γ by positivity)]
  have hpform : 1 - sourceP γ = (1 - γ) / (3 * γ) := by
    unfold sourceP
    have hn : γ ≠ 0 := ne_of_gt hg
    field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sourceP
    apply div_nonneg
    · linarith
    · positivity
  · unfold sourceP
    apply (div_le_one₀ (by positivity : 0 < 3 * γ)).2
    linarith
  · unfold sourceAlpha
    positivity
  · linarith [hpform, hsmall]

/-- Construct the actual hard MDP parameters from the paper's exact ranges. -/
noncomputable def sourceHardParameters (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεup : ε < 1 / (32 * (1 - γ))) : HardParameters := by
  have hv := sourceHardParameters_valid γ ε hγ hγ1 hε hεup
  exact ⟨sourceP γ, sourceAlpha γ ε, γ, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    by linarith, hγ1⟩

/-- The two algebraic forms of the paper's perturbation agree. -/
theorem sourceAlpha_relation (γ ε : ℝ) (hγ : 0 < γ) :
    sourceAlpha γ ε = 2 * (1 - γ * sourceP γ) ^ 2 * ε / γ ^ 2 := by
  unfold sourceAlpha sourceP
  have hg : γ ≠ 0 := ne_of_gt hγ
  field_simp; ring

/-- Strict source-range separation, without adding a probability-validity premise. -/
theorem sourceHardValue_gap_gt_two (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεup : ε < 1 / (32 * (1 - γ))) :
    let θ := sourceHardParameters γ ε hγ hγ1 hε hεup
    2 * ε < 1 / (1 - θ.gamma * θ.q) - 1 / (1 - θ.gamma * θ.p) := by
  apply hardValue_gap_gt_two
  · change 0 < γ
    linarith
  · exact hε
  · change sourceAlpha γ ε = 2 * (1 - γ * sourceP γ) ^ 2 * ε / γ ^ 2
    exact sourceAlpha_relation γ ε (by linarith)

/-- Value in the active state under a stationary bad action. -/
noncomputable def badValue (θ : HardParameters) : ℝ := 1 / (1 - θ.gamma * θ.p)

theorem badValue_equation (θ : HardParameters) :
    1 + θ.gamma * θ.p * badValue θ = badValue θ := by
  unfold badValue
  have hp : 1 - θ.gamma * θ.p ≠ 0 := ne_of_gt θ.denom_p_pos
  field_simp; ring

/-- First action supplied explicitly, followed by a stationary bad action. -/
noncomputable def badPolicyQ (θ : HardParameters) (good : Action) (s : Bool) (a : Action) : ℝ :=
  if s then 1 + θ.gamma * (if a = good then θ.q else θ.p) * badValue θ else 0

omit [Fintype Action] in
theorem badPolicyQ_chosen (θ : HardParameters) (good bad : Action) (h : bad ≠ good) :
    badPolicyQ θ good true bad = badValue θ := by
  simpa [badPolicyQ, h] using badValue_equation θ

/-- The genuine bad policy Bellman operator has the stated fixed point. -/
theorem badPolicyQ_fixed (θ : HardParameters) (good bad : Action) (h : bad ≠ good) :
    (hardMDP θ good).qBellman (fun _ ↦ EnvironmentStage.pointMass bad) (badPolicyQ θ good) =
      badPolicyQ θ good := by
  funext s a
  simp only [DiscountedMDP.qBellman, EnvironmentStage.expectation_pointMass]
  have hval : 1 + θ.gamma * (θ.p * badValue θ) = badValue θ := by
    simpa [mul_assoc] using badValue_equation θ
  cases s with
  | false => simp [hardMDP, bernoulliRow, FiniteDistribution.expectation, badPolicyQ]
  | true =>
    by_cases ha : a = good <;>
      simp [hardMDP, bernoulliRow, ha, FiniteDistribution.expectation,
        badPolicyQ, h, hval, mul_assoc]

/-- The source's Q-policy loss at the good first action is γq times the value gap. -/
theorem hardPolicy_loss_good (θ : HardParameters) (good bad : Action) (h : bad ≠ good) :
    (hardMDP θ good).optimalityFixedPoint true good -
      (hardMDP θ good).policyFixedPoint (fun _ ↦ EnvironmentStage.pointMass bad) true good =
        θ.gamma * θ.q * (θ.goodValue - badValue θ) := by
  have hbad : (hardMDP θ good).policyFixedPoint (fun _ ↦ EnvironmentStage.pointMass bad) =
      badPolicyQ θ good := by
    exact (((hardMDP θ good).policyFixedPoint_characterization
      (fun _ ↦ EnvironmentStage.pointMass bad) (badPolicyQ θ good)).mp
      (badPolicyQ_fixed θ good bad h)).symm
  rw [optimalityFixedPoint_eq_hardQ, hbad]
  simp [hardQ, badPolicyQ]
  ring

/-- At the source parameters, a stationary bad policy incurs more than ε
Q-loss even when its first action is the optimal action. -/
theorem sourceHardPolicy_loss_gt (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hεup : ε < 1 / (32 * (1 - γ))) (good bad : Action) (h : bad ≠ good) :
    let θ := sourceHardParameters γ ε hγ hγ1 hε hεup
    ε < (hardMDP θ good).optimalityFixedPoint true good -
      (hardMDP θ good).policyFixedPoint (fun _ ↦ EnvironmentStage.pointMass bad) true good := by
  let θ := sourceHardParameters γ ε hγ hγ1 hε hεup
  change ε < (hardMDP θ good).optimalityFixedPoint true good -
    (hardMDP θ good).policyFixedPoint (fun _ ↦ EnvironmentStage.pointMass bad) true good
  rw [hardPolicy_loss_good θ good bad h]
  have hgap : 2 * ε < θ.goodValue - badValue θ := by
    simpa only [HardParameters.goodValue, badValue] using
      sourceHardValue_gap_gt_two γ ε hγ hγ1 hε hεup
  have hg : 0 < γ := by linarith
  have hid : γ * sourceP γ = (4 * γ - 1) / 3 := by
    unfold sourceP
    have hn : γ ≠ 0 := ne_of_gt hg
    field_simp
  have hγp : (5 : ℝ) / 9 ≤ θ.gamma * θ.p := by
    change (5 : ℝ) / 9 ≤ γ * sourceP γ
    rw [hid]
    linarith
  have hγq : (5 : ℝ) / 9 ≤ θ.gamma * θ.q := by
    dsimp [HardParameters.q]
    nlinarith [mul_nonneg θ.gamma_nonneg θ.alpha_nonneg]
  have hprod : (5 : ℝ) / 9 * (2 * ε) <
      θ.gamma * θ.q * (θ.goodValue - badValue θ) := by
    calc
      (5 : ℝ) / 9 * (2 * ε) < (5 : ℝ) / 9 * (θ.goodValue - badValue θ) :=
        mul_lt_mul_of_pos_left hgap (by norm_num)
      _ ≤ θ.gamma * θ.q * (θ.goodValue - badValue θ) :=
        mul_le_mul_of_nonneg_right hγq (by linarith)
  linarith

end StatisticalRL.Obstructions
