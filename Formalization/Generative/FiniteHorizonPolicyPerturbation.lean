import Formalization.Generative.FiniteHorizonEmpiricalContinuation

/-! Exact finite-horizon true/empirical policy perturbation identities.
All values are actual trajectory expectations; no statistical premise occurs. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A transition residual applied to an explicitly supplied continuation. -/
noncomputable def policyRowResidual (E F : EnvironmentStage State Action) (V : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  (F.transition s a).expectation V - (E.transition s a).expectation V

/-- The terminal continuation contributes no transition residual. -/
theorem policyRowResidual_zero (E F : EnvironmentStage State Action) (s : State) (a : Action) :
    policyRowResidual E F (fun _ ↦ 0) s a = 0 := by
  simp [policyRowResidual]

/-- Exact backup difference with unchanged known reward, propagated by the
true transition row rather than by an assumed inverse operator. -/
theorem valueBackup_difference_eq (E F : EnvironmentStage State Action)
    (π : StationaryPolicy State Action) (V W : State → ℝ)
    (hr : F.reward = E.reward) (s : State) :
    (F.withPolicy π).valueBackup W s - (E.withPolicy π).valueBackup V s =
      (π s).expectation (fun a ↦ policyRowResidual E F W s a +
        (E.transition s a).expectation (fun t ↦ W t - V t)) := by
  unfold DecisionStage.valueBackup
  change (π s).expectation ((F.withPolicy π).qBackup W s) -
    (π s).expectation ((E.withPolicy π).qBackup V s) = _
  rw [← FiniteDistribution.expectation_sub]
  congr 1
  funext a
  simp only [DecisionStage.qBackup, EnvironmentStage.withPolicy, policyRowResidual,
    FiniteDistribution.expectation_sub, hr]
  ring

/-- Exact one-step identity for actual nonstationary trajectory values. -/
theorem trajectoryValue_difference_cons (E F : EnvironmentStage State Action)
    (es fs : List (EnvironmentStage State Action)) (π : ℕ → StationaryPolicy State Action)
    (hr : F.reward = E.reward) (s : State) :
    DecisionStage.trajectoryValue (EnvironmentStage.controlled (F :: fs) π) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (E :: es) π) s =
    (π 0 s).expectation (fun a ↦ policyRowResidual E F
      (DecisionStage.trajectoryValue (EnvironmentStage.controlled fs (fun k ↦ π (k + 1)))) s a +
      (E.transition s a).expectation (fun t ↦
        DecisionStage.trajectoryValue (EnvironmentStage.controlled fs (fun k ↦ π (k + 1))) t -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled es (fun k ↦ π (k + 1))) t)) := by
  rw [EnvironmentStage.controlled, EnvironmentStage.controlled,
    DecisionStage.trajectoryValue_cons, DecisionStage.trajectoryValue_cons]
  exact valueBackup_difference_eq E F (π 0) _ _ hr s

/-- Forced-first-action Q has the same residual and true-kernel suffix-error
propagation, without averaging the intervention action by the policy. -/
theorem trajectoryQ_difference_cons (E F : EnvironmentStage State Action)
    (es fs : List (EnvironmentStage State Action)) (π : ℕ → StationaryPolicy State Action)
    (hr : F.reward = E.reward) (s : State) (a : Action) :
    DecisionStage.trajectoryQ (EnvironmentStage.controlled (F :: fs) π) s a -
      DecisionStage.trajectoryQ (EnvironmentStage.controlled (E :: es) π) s a =
    policyRowResidual E F
      (DecisionStage.trajectoryValue (EnvironmentStage.controlled fs (fun k ↦ π (k + 1)))) s a +
      (E.transition s a).expectation (fun t ↦
        DecisionStage.trajectoryValue (EnvironmentStage.controlled fs (fun k ↦ π (k + 1))) t -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled es (fun k ↦ π (k + 1))) t) := by
  rw [EnvironmentStage.controlled, EnvironmentStage.controlled,
    DecisionStage.trajectoryQ_cons, DecisionStage.trajectoryQ_cons]
  simp only [DecisionStage.qBackup, EnvironmentStage.withPolicy, policyRowResidual,
    FiniteDistribution.expectation_sub, hr]
  ring

/-- Finite nested propagation of all suffix residuals. A pair stores one true
and one comparison stage at the same time, so both episodes have equal horizon. -/
noncomputable def propagatedPolicyResidual :
    List (EnvironmentStage State Action × EnvironmentStage State Action) →
      (ℕ → StationaryPolicy State Action) → State → ℝ
  | [], _ => fun _ ↦ 0
  | (E,F) :: tail, π => fun s ↦ (π 0 s).expectation (fun a ↦
      policyRowResidual E F
        (DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.snd)
          (fun k ↦ π (k + 1)))) s a +
      (E.transition s a).expectation (propagatedPolicyResidual tail (fun k ↦ π (k + 1))))

/-- The actual value difference equals the finite propagated residuals; the
error estimate is proved by induction and is not a recursion premise. -/
theorem trajectoryValue_difference_eq_propagatedResidual
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action)
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) (s : State) :
    DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.snd) π) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π) s =
      propagatedPolicyResidual pairs π s := by
  induction pairs generalizing π s with
  | nil => simp [EnvironmentStage.controlled, DecisionStage.trajectoryValue_nil, propagatedPolicyResidual]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    have hhead := hr (E,F) (by simp)
    have htail : ∀ p ∈ tail, p.2.reward = p.1.reward := fun p hp ↦ hr p (by simp [hp])
    simp only [List.map_cons]
    rw [trajectoryValue_difference_cons E F _ _ π hhead s]
    have he : (fun t ↦
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.snd) (fun k ↦ π (k + 1))) t -
        DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.fst) (fun k ↦ π (k + 1))) t) =
        propagatedPolicyResidual tail (fun k ↦ π (k + 1)) := by
      funext t
      exact ih _ htail t
    rw [he]
    rfl

/-- Pair every true stage with the frequency model from the same sample data. -/
noncomputable def pairedEmpiricalStages {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) :
    List (EnvironmentStage State Action × EnvironmentStage State Action) :=
  List.ofFn (fun h ↦ (E h, empiricalStage E N hN data h))

/-- Same-data empirical specialization: every nonstationary policy admits the
exact finite perturbation identity, without a sampling/event assumption. -/
theorem empiricalTrajectoryValue_difference_eq_residual {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (π : ℕ → StationaryPolicy State Action) (s : State) :
    DecisionStage.trajectoryValue (EnvironmentStage.controlled (empiricalStages E N hN data) π) s -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π) s =
      propagatedPolicyResidual (pairedEmpiricalStages E N hN data) π s := by
  have hr : ∀ p ∈ pairedEmpiricalStages E N hN data, p.2.reward = p.1.reward := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    rfl
  have ht := trajectoryValue_difference_eq_propagatedResidual (pairedEmpiricalStages E N hN data) π hr s
  simpa only [pairedEmpiricalStages, List.map_ofFn, Function.comp_def, empiricalStages] using ht

end StatisticalRL.FiniteHorizonGenerative
