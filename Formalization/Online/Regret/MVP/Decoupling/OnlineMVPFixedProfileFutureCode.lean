import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPProfileBatchBridge

/-! Concrete corrected fixed-profile suffix code for the finite MVP family.
The suffix is built from the actual capped-backward recursion and profile-
selected finite-stack batches.  It uses the deployed terminal-zero convention
(C17 correction).  The result is deterministic/pathwise; probability
transport and the source's power-of-two trigger interpretation (C13) remain
separate. -/

namespace StatisticalRL.OnlineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpFutureStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpFutureActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The selected batch in a row's expanded successor stack at fixed profile
level `j`.  The source-valid profile cap ensures its indices are below K; a
total stream makes the definition available before that range proof is used. -/
def onlineMVPFixedProfileBatch
    {H : ℕ} (stream : OnlineMDPRow State Action H → ℕ → State)
    (row : OnlineMDPRow State Action H) (j : ℕ) : List State :=
  List.ofFn (fun i : Fin (onlineMVPProfileBatchSize j) =>
    stream row (onlineMVPProfileBatchStart j + i.val))

/-- A fixed-profile stage uses the source known-reward environment and the
expanded-stack batch selected by the same profile entry for every row. -/
noncomputable def onlineMVPFixedProfileStage
    {H K : ℕ} (E : Fin H → EnvironmentStage State Action)
    (stream : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ)
    (k : Fin K) (h : Fin H) : OnlineObservedPlanningStage State Action where
  environment := E h
  observations s a :=
    onlineMVPFixedProfileBatch stream (h, (s, a)) (profile k (h, (s, a)))

/-- Full length-H fixed-profile stage data for one episode. -/
noncomputable def onlineMVPFixedProfileStages
    {H K : ℕ} (E : Fin H → EnvironmentStage State Action)
    (stream : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ) (k : Fin K) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (onlineMVPFixedProfileStage E stream profile k)

/-- The corrected next-stage family at `h` is obtained by running the actual
zero-terminal capped recursion on each fixed-profile suffix and adjoining
zero, exactly as in Assumption X's finite-family interface. -/
noncomputable def onlineMVPFixedProfileFutureFamily
    {H K : ℕ} (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (stream : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ) (h : ℕ) :
    Finset (State → ℝ) :=
  onlineMVPZeroTerminalFutureCode cap L c₁ c₂
    (fun code k => onlineMVPFixedProfileStages E code.2 profile k)
    (profile, stream) h

theorem onlineMVPFixedProfileFutureFamily_eq_actual_definition
    {H K : ℕ} (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (stream : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ) (h : ℕ) :
    onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E stream profile h =
      onlineMVPZeroTerminalValueFamily cap L c₁ c₂
        (fun k => onlineMVPFixedProfileStages E stream profile k) (h + 1) := rfl

end StatisticalRL.OnlineRL
