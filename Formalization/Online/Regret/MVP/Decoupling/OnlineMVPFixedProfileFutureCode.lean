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

/-- If two expanded stacks agree at every row of every future stage `h' > h`,
then the entire corrected next-stage value family is identical. Thus the code
depends on the fixed profile and future expanded rows only; no current/past
stage sample appears in its output. -/
theorem onlineMVPFixedProfileFutureFamily_congr_future
    {H K : ℕ} (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (stream₁ stream₂ : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ)
    (h : ℕ) (hh : h < H)
    (hfuture : ∀ (r : OnlineMDPRow State Action H) (i : ℕ),
      h < r.1.val → stream₁ r i = stream₂ r i) :
    onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E stream₁ profile h =
      onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E stream₂ profile h := by
  classical
  rw [onlineMVPFixedProfileFutureFamily_eq_actual_definition,
    onlineMVPFixedProfileFutureFamily_eq_actual_definition]
  unfold onlineMVPZeroTerminalValueFamily
  apply congrArg (insert (fun _ : State => (0 : ℝ)))
  apply Finset.image_congr
  intro k hk
  have hstage : ∀ j : Fin H, h < j.val →
      onlineMVPFixedProfileStage E stream₁ profile k j =
        onlineMVPFixedProfileStage E stream₂ profile k j := by
    intro j hj
    cases j with
    | mk j hjH =>
      simp only [onlineMVPFixedProfileStage, OnlineObservedPlanningStage.mk.injEq]
      constructor
      · trivial
      · funext s a
        unfold onlineMVPFixedProfileBatch
        apply congrArg List.ofFn
        funext i
        exact hfuture (⟨j, hjH⟩, (s, a)) (onlineMVPProfileBatchStart
          (profile k (⟨j, hjH⟩, (s, a))) + i.val) (by simpa using hj)
  have hdrop :
      (onlineMVPFixedProfileStages E stream₁ profile k).drop (h + 1) =
        (onlineMVPFixedProfileStages E stream₂ profile k).drop (h + 1) := by
    apply List.ext_getElem?'
    intro i hi
    have hlen₁ : (onlineMVPFixedProfileStages E stream₁ profile k).length = H := by
      simp [onlineMVPFixedProfileStages]
    have hlen₂ : (onlineMVPFixedProfileStages E stream₂ profile k).length = H := by
      simp [onlineMVPFixedProfileStages]
    have hi' : i < H - (h + 1) := by simpa [hlen₁, hlen₂] using hi
    have hidx : h + 1 + i < H := by omega
    simp only [onlineMVPFixedProfileStages, List.getElem?_drop,
      List.getElem?_ofFn]
    have hnext : h < h + 1 + i := by omega
    have hstage' := hstage ⟨h + 1 + i, hidx⟩ hnext
    simp [hidx, hstage']
  simpa [onlineCappedBackwardValueAt, hdrop]

/-- At the terminal boundary after the last stage, the family is the singleton
zero, independently of stack data; this uses the deployed terminal-zero rule
(C17). -/
theorem onlineMVPFixedProfileFutureFamily_terminal
    {H K : ℕ} (hH : 0 < H) (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (stream : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ) :
    onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E stream profile (H - 1) = {0} := by
  rw [onlineMVPFixedProfileFutureFamily_eq_actual_definition]
  apply onlineMVPZeroTerminalValueFamily_terminal_eq_singleton
  intro k
  simp [onlineMVPFixedProfileStages, Nat.sub_add_cancel hH]

end StatisticalRL.OnlineRL
