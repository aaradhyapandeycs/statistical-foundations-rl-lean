import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFutureProfileFamily

/-! Batch-restricted congruence for the future-code family. The canonical
filler is irrelevant because bounded source-profile batches read only valid
coordinates of the finite expanded stack. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpFutureBatchStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance mvpFutureBatchStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpFutureBatchActionDecidable : DecidableEq Action := Classical.decEq Action

/-- If every selected future row batch agrees, then the fixed-profile suffix
stage lists agree. No equality at unused or out-of-range stack coordinates is
required. -/
theorem onlineMVPFixedProfileFutureFamily_congr_batches
    {H K : ℕ} (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (stream₁ stream₂ : OnlineMDPRow State Action H → ℕ → State)
    (profile : Fin K → OnlineMDPRow State Action H → ℕ)
    (h : ℕ) (hh : h < H)
    (hbatch : ∀ (k : Fin K) (j : Fin H) (s : State) (a : Action),
      h < j.val →
      onlineMVPFixedProfileBatch stream₁ (j, (s, a))
          (profile k (j, (s, a))) =
        onlineMVPFixedProfileBatch stream₂ (j, (s, a))
          (profile k (j, (s, a)))) :
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
        exact hbatch k ⟨j, hjH⟩ s a hj
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
    have hj : h < h + 1 + i := by omega
    have hstage' := hstage ⟨h + 1 + i, hidx⟩ hj
    simp [hidx, hstage']
  simpa [onlineCappedBackwardValueAt, hdrop]

/-- For an actual bounded source profile, the canonical future-code filler
and the actual finite stack produce identical selected future batches. Every
coordinate used is below K by the profile-level cap. -/
theorem onlineMVPActualFutureCodeBatch_eq_stack
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (j : Fin H) (s : State) (a : Action)
    (hh : h < j) :
    onlineMVPFixedProfileBatch
        (onlineMVPFutureCodeStream hH E h
          (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
        (j, (s, a)) (onlineMVPProfileToNat p k (j, (s, a))) =
      onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
        (j, (s, a)) (onlineMVPProfileToNat p k (j, (s, a))) := by
  rw [onlineMVPFutureCodeStream_profileBatch_eq_code hH hK E p h
    (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data)
    k (j, (s, a)) hh]
  unfold onlineMVPFixedProfileBatch
  congr 1
  funext i
  have hi := onlineMVPProfileBatchIndex_lt_K hK p k (j, (s, a)) i
  simp [StatisticalRL.OnlineRL.MVPUniformSource.futureData,
    onlineFiniteStackExtend, hi]

/-- The actual pre-episode optimistic value belongs to the same fixed finite
profile/future-code family for every reset vector and every expanded stack.
The family uses a canonical filler, but only valid finite-stack coordinates
are read, so no fallback-equality premise is needed. -/
theorem onlineMVPActualPreEpisodeValue_mem_sourceProfileFamily_noFallback
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (cap L c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineCappedBackwardValueAt cap L c₁ c₂
      (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1) ∈
    onlineMVPSourceProfileFutureFamily hH cap L c₁ c₂ E
      (sourceMVPActualProfileTable
        (fun e j => (onlineMVPActualStackRowAt hH initial fallback planner data
          (e * H + j.val)).2)) h
      (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let rows : EpisodeRowTable H (State × Action) :=
    fun e j => (onlineMVPActualStackRowAt hH initial fallback planner data
      (e * H + j.val)).2
  have hprofile :
      onlineMVPActualPreEpisodeProfile hH initial fallback planner data =
        onlineMVPProfileToNat (sourceMVPActualProfileTable rows) :=
    onlineMVPActualPreEpisodeProfile_eq_profileToNat hH initial fallback planner data
  have hmem : onlineCappedBackwardValueAt cap L c₁ c₂
      (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1) ∈
      onlineMVPZeroTerminalValueFamily cap L c₁ c₂
        (fun k' => onlineMVPActualPreEpisodeStages hH E initial fallback planner data k')
        (h.val + 1) := by
    unfold onlineMVPZeroTerminalValueFamily
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  have hfixed := onlineMVPActualPreEpisodeFutureFamily_eq_fixedProfile
    hH cap L c₁ c₂ E initial fallback planner data k h.val
  have hfamily :
      onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E
        (onlineMVPFutureCodeStream hH E h
          (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) h.val =
      onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E
        (onlineFiniteStackExtend K fallback data)
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) h.val := by
    apply onlineMVPFixedProfileFutureFamily_congr_batches cap L c₁ c₂ E
      (onlineMVPFutureCodeStream hH E h
        (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
      (onlineFiniteStackExtend K fallback data)
      (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) h.val h.isLt
    intro k' j s a hj
    rw [hprofile]
    exact onlineMVPActualFutureCodeBatch_eq_stack hH hK E
      (sourceMVPActualProfileTable rows) h fallback
      data k' j s a (Fin.mk_lt_mk.mpr hj)
  rw [hfixed] at hmem
  rw [← hfamily] at hmem
  rw [hprofile] at hmem
  change onlineCappedBackwardValueAt cap L c₁ c₂
      (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1) ∈
    onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E
      (onlineMVPFutureCodeStream hH E h
        (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
      (onlineMVPProfileToNat (sourceMVPActualProfileTable rows)) h.val
  exact hmem

end StatisticalRL.OnlineRL
