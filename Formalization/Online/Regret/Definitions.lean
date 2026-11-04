import Formalization.Online.SourceOptimism.GreedySequentialTrajectoryOptimism

/-! Actual-path quantities for the corrected zero-count, fixed-tie UCBVI planner. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Analysis charge matching the positive-count source bonus and assigning a
finite charge `cap` to the corrected zero-count branch. This is an analytic
bookkeeping quantity; it does not redefine the printed bonus at `N=0`. -/
noncomputable def onlineRegretAnalysisCharge
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (s : State) (a : Action) : ℝ :=
  if hN : 0 < (stage.observations s a).length then
    c₁ * Real.sqrt
      ((onlineObservedPlanningRow stage s a).variance next * L /
        (stage.observations s a).length) +
      c₂ * cap * L / (stage.observations s a).length
  else cap

/-- Value of the capped table along one realized state sequence, before the
transition at index `n`. -/
noncomputable def onlineCappedEpisodeValueAlongPath
    {H : ℕ} (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (cap L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  onlineCappedBackwardValue cap L c₁ c₂ ((List.ofFn stage).drop n) (state n)

/-- Source-shaped summand for the one-episode telescope. Outside the active
range it is totalized to zero solely so it can be summed over `range H`. -/
noncomputable def onlineCappedEpisodeTelescopeSummand
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    let tailValue := onlineCappedBackwardValue (H : ℝ) L c₁ c₂
      ((List.ofFn stage).drop (n + 1))
    (stage h).environment.reward (state n) (action n) +
      onlineRegretAnalysisCharge (H : ℝ) L c₁ c₂ (stage h) tailValue
        (state n) (action n) +
      ((onlineObservedPlanningRow (stage h) (state n) (action n)).expectation tailValue -
        ((stage h).environment.transition (state n) (action n)).expectation tailValue) +
      (((stage h).environment.transition (state n) (action n)).expectation tailValue -
        tailValue (state (n + 1)))
  else 0

/-- The deterministic policy whose value is used in the source's T₄ term.
It is obtained from the same completed-history capped greedy planner that
generates the online actions. The modulo branch only totalizes the policy past
the finite horizon; `controlled (List.ofFn E)` observes indices below H. -/
noncomputable def onlineCappedEpisodePolicy
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (L c₁ c₂ : ℝ) : ℕ → StationaryPolicy State Action :=
  fun n s => EnvironmentStage.pointMass
    (onlineCappedGreedyPlanner E L c₁ c₂ (history.take (k * H))
      ⟨n % H, Nat.mod_lt n hH⟩ s)

/-- Actual true trajectory value of that episode's selected policy. This is
the finite-trajectory expectation, not a realized reward sum. -/
noncomputable def onlineCappedEpisodePolicyValue
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (initial : State) (L c₁ c₂ : ℝ) : ℝ :=
  DecisionStage.trajectoryValue
    (EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k L c₁ c₂)) initial

/-- Source-shaped episode terms, all evaluated on one actual completed
history. T₁ uses the empirical row on the same data and is therefore left as
an arbitrary data-dependent quantity; this definition makes no centering
claim. T₄ compares realized rewards with the actual selected-policy trajectory
value. -/
noncomputable def onlineCappedEpisodeT1
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    let tail := onlineCappedBackwardValue (H : ℝ) L c₁ c₂
      ((List.ofFn stage).drop (n + 1))
    (onlineObservedPlanningRow (stage h) (state n) (action n)).expectation tail -
      ((stage h).environment.transition (state n) (action n)).expectation tail
  else 0

noncomputable def onlineCappedEpisodeT2
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    onlineRegretAnalysisCharge (H : ℝ) L c₁ c₂ (stage h)
      (onlineCappedBackwardValue (H : ℝ) L c₁ c₂
        ((List.ofFn stage).drop (n + 1))) (state n) (action n)
  else 0

noncomputable def onlineCappedEpisodeT3
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    let tail := onlineCappedBackwardValue (H : ℝ) L c₁ c₂
      ((List.ofFn stage).drop (n + 1))
    ((stage h).environment.transition (state n) (action n)).expectation tail -
      tail (state (n + 1))
  else 0

noncomputable def onlineCappedEpisodeReward
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (n : ℕ) : ℝ :=
  if hn : n < H then (E ⟨n, hn⟩).reward (state n) (action n) else 0

/-- The source's T₄ contribution for one actual episode: the realized reward
sum minus the expected return of the same completed-history greedy policy. -/
noncomputable def onlineCappedEpisodeT4
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (initial : State) (state : ℕ → State) (action : ℕ → Action)
    (L c₁ c₂ : ℝ) : ℝ :=
  (∑ h : Fin H, (E h).reward (state h.val) (action h.val)) -
    onlineCappedEpisodePolicyValue H hH E history k initial L c₁ c₂

noncomputable def onlineActualEpisodeRegret
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) : ℝ :=
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
        (initial k) - onlineCappedEpisodePolicyValue H hH E history k.val
          (initial k) (Real.log (1 / δ')) c₁ c₂

noncomputable def onlineActualEpisodeRegretTerms
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    ((∑ n ∈ Finset.range H,
        onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ')) c₁ c₂ n), (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ')) c₁ c₂ n), (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ')) c₁ c₂ n), ((∑ n ∈ Finset.range H, onlineCappedEpisodeReward H E state action n) -
        onlineCappedEpisodePolicyValue H hH E history k.val
          (initial k) (Real.log (1 / δ')) c₁ c₂))

noncomputable def onlineFixedOptimalContinuation
    (H : ℕ) (E : Fin H → EnvironmentStage State Action) (n : ℕ) : State → ℝ :=
  DecisionStage.trajectoryValue ((EnvironmentStage.greedyStages (List.ofFn E)).drop (n + 1))

noncomputable def onlineEpisodeFixedOptimalW1
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    let v := onlineFixedOptimalContinuation H E n
    (onlineObservedPlanningRow (stage h) (state n) (action n)).expectation v -
      ((stage h).environment.transition (state n) (action n)).expectation v
  else 0

noncomputable def onlineEpisodeFixedOptimalW2
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < H then
    let h : Fin H := ⟨n, hn⟩
    let tail := onlineCappedBackwardValue (H : ℝ) L c₁ c₂
      ((List.ofFn stage).drop (n + 1))
    let v := onlineFixedOptimalContinuation H E n
    (onlineObservedPlanningRow (stage h) (state n) (action n)).expectation (fun s ↦ tail s - v s) -
      ((stage h).environment.transition (state n) (action n)).expectation (fun s ↦ tail s - v s)
  else 0

noncomputable def onlineActualEpisodeW1
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) : ℝ :=
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    ∑ n ∈ Finset.range H, onlineEpisodeFixedOptimalW1 H E stage state action n

noncomputable def onlineActualEpisodeW2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) : ℝ :=
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    ∑ n ∈ Finset.range H, onlineEpisodeFixedOptimalW2 H E stage state action (Real.log (1 / δ')) c₁ c₂ n

/-- The actual-path four-term decomposition event, on the joint source
initial-state and adaptive transition experiment. -/
noncomputable def onlineActualRegretDecompositionEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ' c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.2)}

end StatisticalRL.OnlineRL
