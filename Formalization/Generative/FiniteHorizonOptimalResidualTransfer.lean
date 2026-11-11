import Formalization.Generative.FiniteHorizonResidualAccumulation

/-! Deterministic finite optimal-control transfer from one common collection
of canonical empirical-optimal suffix residuals. No statistical rate is claimed. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Exact empirical optimality at every suffix and every state. -/
def SuffixOptimal (fs : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) : Prop :=
  ∀ n s, DecisionStage.trajectoryValue ((EnvironmentStage.controlled fs π).drop n) s =
    EnvironmentStage.optimalValue (fs.drop n) s

theorem suffixOptimal_tail (F : EnvironmentStage State Action)
    (fs : List (EnvironmentStage State Action)) (π : ℕ → StationaryPolicy State Action)
    (hf : SuffixOptimal (F :: fs) π) : SuffixOptimal fs (fun k ↦ π (k + 1)) := by
  intro n s
  simpa only [EnvironmentStage.controlled, List.drop_succ_cons] using hf (n + 1) s

/-- A total backward-greedy policy; the supplied default is used only after
the finite episode, where no decision affects its value. -/
noncomputable def backwardGreedyPolicy (default : StationaryPolicy State Action) :
    List (EnvironmentStage State Action) → ℕ → StationaryPolicy State Action
  | [], _ => default
  | E :: es, 0 => fun s ↦ EnvironmentStage.pointMass (E.greedyAction (EnvironmentStage.optimalValue es) s)
  | _ :: es, n + 1 => backwardGreedyPolicy default es n

theorem controlled_backwardGreedyPolicy (default : StationaryPolicy State Action)
    (fs : List (EnvironmentStage State Action)) :
    EnvironmentStage.controlled fs (backwardGreedyPolicy default fs) = EnvironmentStage.greedyStages fs := by
  induction fs with
  | nil => rfl
  | cons E fs ih =>
    change E.withPolicy (fun s ↦ EnvironmentStage.pointMass (E.greedyAction (EnvironmentStage.optimalValue fs) s)) ::
      EnvironmentStage.controlled fs (backwardGreedyPolicy default fs) = _
    rw [ih]
    rfl

theorem backwardGreedyPolicy_suffixOptimal (default : StationaryPolicy State Action)
    (fs : List (EnvironmentStage State Action)) : SuffixOptimal fs (backwardGreedyPolicy default fs) := by
  intro n s
  rw [controlled_backwardGreedyPolicy, EnvironmentStage.greedyStages_drop]
  exact EnvironmentStage.greedy_trajectoryValue _ s

/-- Canonical suffix residual charges do not depend on a chosen optimal tie policy. -/
noncomputable def optimalResidualCharges :
    List (EnvironmentStage State Action × EnvironmentStage State Action) → List ℝ
  | [] => []
  | (E,F) :: tail => ‖policyRowResidual E F (EnvironmentStage.optimalValue (tail.map Prod.snd))‖ ::
      optimalResidualCharges tail

theorem optimalResidualCharges_length
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action)) :
    (optimalResidualCharges pairs).length = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p tail ih => rcases p with ⟨E,F⟩; simpa only [optimalResidualCharges, List.length_cons] using congrArg Nat.succ ih

private theorem row_abs_le_norm (R : State → Action → ℝ) (s : State) (a : Action) : |R s a| ≤ ‖R‖ := by
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (R s) a).trans (norm_le_pi_norm R s)

/-- Optimal values of the two actual finite models differ by at most the
same canonical suffix residual charges. -/
theorem optimalValue_difference_abs_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) (s : State) :
    |EnvironmentStage.optimalValue (pairs.map Prod.snd) s -
      EnvironmentStage.optimalValue (pairs.map Prod.fst) s| ≤ (optimalResidualCharges pairs).sum := by
  induction pairs generalizing s with
  | nil => simp [EnvironmentStage.optimalValue, optimalResidualCharges]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    letI : Nonempty Action := E.action_nonempty
    have hh : F.reward = E.reward := hr (E,F) (by simp)
    have ht : ∀ p ∈ tail, p.2.reward = p.1.reward := fun p hp ↦ hr p (by simp [hp])
    let W := EnvironmentStage.optimalValue (tail.map Prod.snd)
    let V := EnvironmentStage.optimalValue (tail.map Prod.fst)
    let R := policyRowResidual E F W
    change |actionMaximum (F.qBackup W s) - actionMaximum (E.qBackup V s)| ≤
      ‖R‖ + (optimalResidualCharges tail).sum
    apply abs_actionMaximum_sub_le
    intro a
    have he : F.qBackup W s a - E.qBackup V s a =
      R s a + (E.transition s a).expectation (fun t ↦ W t - V t) := by
      simp only [R, policyRowResidual, EnvironmentStage.qBackup, FiniteDistribution.expectation_sub, hh]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (row_abs_le_norm R s a)
      ((E.transition s a).abs_expectation_le (fun t ↦ ih ht t)))

/-- Every exact suffix-optimal comparison policy has evaluation error bounded
by the same policy-independent residual charges. -/
theorem suffixOptimal_evaluation_abs_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (hf : SuffixOptimal (pairs.map Prod.snd) π)
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) (s : State) :
    |EnvironmentStage.optimalValue (pairs.map Prod.snd) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s| ≤
      (optimalResidualCharges pairs).sum := by
  induction pairs generalizing π s with
  | nil => simp [EnvironmentStage.optimalValue, EnvironmentStage.controlled, DecisionStage.trajectoryValue_nil, optimalResidualCharges]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    have hh : F.reward = E.reward := hr (E,F) (by simp)
    have ht : ∀ p ∈ tail, p.2.reward = p.1.reward := fun p hp ↦ hr p (by simp [hp])
    have hft := suffixOptimal_tail F (tail.map Prod.snd) π hf
    have hhead : DecisionStage.trajectoryValue (EnvironmentStage.controlled (F :: tail.map Prod.snd) π) s =
      EnvironmentStage.optimalValue (F :: tail.map Prod.snd) s := by simpa only [List.drop_zero] using hf 0 s
    have hnext : DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.snd) (fun k ↦ π (k + 1))) =
        EnvironmentStage.optimalValue (tail.map Prod.snd) := by
      funext t
      simpa only [List.drop_zero] using hft 0 t
    change |EnvironmentStage.optimalValue (F :: tail.map Prod.snd) s - _| ≤ _
    simp only [List.map_cons]
    rw [← hhead, trajectoryValue_difference_cons E F _ _ π hh s, hnext]
    let R := policyRowResidual E F (EnvironmentStage.optimalValue (tail.map Prod.snd))
    change |(π 0 s).expectation (fun a ↦ R s a + (E.transition s a).expectation
      (fun t ↦ EnvironmentStage.optimalValue (tail.map Prod.snd) t -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.fst) (fun k ↦ π (k + 1))) t))| ≤
      ‖R‖ + (optimalResidualCharges tail).sum
    apply (π 0 s).abs_expectation_le
    intro a
    exact (abs_add_le _ _).trans (add_le_add (row_abs_le_norm R s a)
      ((E.transition s a).abs_expectation_le (fun t ↦ ih _ hft ht t)))

/-- True-model suboptimality follows from one collection of canonical
comparison-optimal residuals, simultaneously for every exact optimal tie policy. -/
theorem suffixOptimal_value_loss_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (hf : SuffixOptimal (pairs.map Prod.snd) π)
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) (s : State) :
    0 ≤ EnvironmentStage.optimalValue (pairs.map Prod.fst) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s ∧
    EnvironmentStage.optimalValue (pairs.map Prod.fst) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s ≤
      2 * (optimalResidualCharges pairs).sum := by
  refine ⟨sub_nonneg.mpr (EnvironmentStage.trajectoryValue_le_optimal _ π s), ?_⟩
  have h₀ := optimalValue_difference_abs_le pairs hr s
  have h₁ := suffixOptimal_evaluation_abs_le pairs π hf hr s
  have ha := neg_abs_le (EnvironmentStage.optimalValue (pairs.map Prod.snd) s -
    EnvironmentStage.optimalValue (pairs.map Prod.fst) s)
  have hb := le_abs_self (EnvironmentStage.optimalValue (pairs.map Prod.snd) s -
    DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s)
  linarith

/-- Both actual true-model V and forced-first-action Q performance guarantees
use the same residual charges and the same optimal tie policy. -/
theorem suffixOptimal_performance_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (hf : SuffixOptimal (pairs.map Prod.snd) π)
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) :
    (∀ s, 0 ≤ EnvironmentStage.optimalValue (pairs.map Prod.fst) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s ∧
      EnvironmentStage.optimalValue (pairs.map Prod.fst) s -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s ≤
        2 * (optimalResidualCharges pairs).sum) ∧
    (∀ s a, 0 ≤ EnvironmentStage.optimalQ (pairs.map Prod.fst) s a -
      DecisionStage.trajectoryQ (EnvironmentStage.controlled (pairs.map Prod.fst) π) s a ∧
      EnvironmentStage.optimalQ (pairs.map Prod.fst) s a -
        DecisionStage.trajectoryQ (EnvironmentStage.controlled (pairs.map Prod.fst) π) s a ≤
        2 * (optimalResidualCharges pairs).sum) := by
  refine ⟨suffixOptimal_value_loss_le pairs π hf hr, ?_⟩
  intro s a
  refine ⟨sub_nonneg.mpr (EnvironmentStage.trajectoryQ_le_optimal _ π s a), ?_⟩
  cases pairs with
  | nil => simp [EnvironmentStage.optimalQ, EnvironmentStage.controlled, DecisionStage.trajectoryQ_nil, optimalResidualCharges]
  | cons p tail =>
    rcases p with ⟨E,F⟩
    have hft := suffixOptimal_tail F (tail.map Prod.snd) π hf
    have ht : ∀ p ∈ tail, p.2.reward = p.1.reward := fun p hp ↦ hr p (by simp [hp])
    have hv (t : State) := (suffixOptimal_value_loss_le tail (fun k ↦ π (k + 1)) hft ht t).2
    have he : EnvironmentStage.optimalQ (((E,F) :: tail).map Prod.fst) s a -
        DecisionStage.trajectoryQ (EnvironmentStage.controlled (((E,F) :: tail).map Prod.fst) π) s a =
      (E.transition s a).expectation (fun t ↦ EnvironmentStage.optimalValue (tail.map Prod.fst) t -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.fst) (fun k ↦ π (k + 1))) t) := by
      simp only [List.map_cons, EnvironmentStage.optimalQ, EnvironmentStage.controlled,
        DecisionStage.trajectoryQ_cons, DecisionStage.qBackup, EnvironmentStage.qBackup,
        EnvironmentStage.withPolicy, FiniteDistribution.expectation_sub]
      ring
    rw [he]
    have hp := (E.transition s a).expectation_le_const hv
    change _ ≤ 2 * (‖policyRowResidual E F (EnvironmentStage.optimalValue (tail.map Prod.snd))‖ +
      (optimalResidualCharges tail).sum)
    linarith [norm_nonneg (policyRowResidual E F (EnvironmentStage.optimalValue (tail.map Prod.snd)))]

/-- One common canonical residual envelope controls every empirical-optimal
tie policy simultaneously; no chosen-policy independence is a premise. -/
theorem empiricalSuffixOptimal_performance_uniform {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (r : ℝ)
    (hres : ∀ c ∈ optimalResidualCharges (pairedEmpiricalStages E N hN data), c ≤ r) :
    ∀ π : ℕ → StationaryPolicy State Action, SuffixOptimal (empiricalStages E N hN data) π →
      (∀ s, 0 ≤ EnvironmentStage.optimalValue (List.ofFn E) s -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π) s ∧
        EnvironmentStage.optimalValue (List.ofFn E) s -
          DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π) s ≤ 2 * H * r) ∧
      (∀ s a, 0 ≤ EnvironmentStage.optimalQ (List.ofFn E) s a -
        DecisionStage.trajectoryQ (EnvironmentStage.controlled (List.ofFn E) π) s a ∧
        EnvironmentStage.optimalQ (List.ofFn E) s a -
          DecisionStage.trajectoryQ (EnvironmentStage.controlled (List.ofFn E) π) s a ≤ 2 * H * r) := by
  intro π hf
  let pairs := pairedEmpiricalStages E N hN data
  have hr : ∀ p ∈ pairs, p.2.reward = p.1.reward := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    rfl
  have hf' : SuffixOptimal (pairs.map Prod.snd) π := by
    simpa only [pairs, pairedEmpiricalStages, List.map_ofFn, Function.comp_def, empiricalStages] using hf
  have hp := suffixOptimal_performance_le pairs π hf' hr
  have hsum : (optimalResidualCharges pairs).sum ≤ H * r := by
    have ht := List.sum_le_card_nsmul (optimalResidualCharges pairs) r hres
    simpa only [optimalResidualCharges_length, pairs, pairedEmpiricalStages, List.length_ofFn, nsmul_eq_mul] using ht
  dsimp only [pairs, pairedEmpiricalStages] at hsum
  have hv := hp.1
  have hq := hp.2
  simp only [pairs, pairedEmpiricalStages, List.map_ofFn, Function.comp_def] at hv hq
  constructor
  · intro s
    exact ⟨(hv s).1, (hv s).2.trans (by nlinarith [hsum])⟩
  · intro s a
    exact ⟨(hq s a).1, (hq s a).2.trans (by nlinarith [hsum])⟩

end StatisticalRL.FiniteHorizonGenerative
