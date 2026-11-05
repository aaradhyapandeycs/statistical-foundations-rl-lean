import Formalization.Online.Regret.MVP.Optimism.MVPBackwardOptimism
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualEpisodeFixedProfile
import Formalization.Online.Regret.MVP.MVPUniformSourceDefinitions
import Formalization.Online.Regret.MVP.MVPActualProfiles

/-! Actual-path consumer for the finite source-profile future family.  Each
family member is a corrected zero-terminal capped-backward value from a fixed
profile's strictly-future stack rows.  This file proves deterministic family
bounds and membership of actual pre-episode values; it does not transport a
probability event. -/

namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpFutureProfileStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance mvpFutureProfileStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpFutureProfileActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Convert the bounded finite source profile into the natural-valued profile
used by the actual batch and capped-backward constructors. -/
noncomputable def onlineMVPProfileToNat
    {H K : ℕ} (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K) :
    Fin K → OnlineMDPRow State Action H → ℕ := by
  let e : OnlineMDPRow State Action H ≃
      Fin (Fintype.card (Fin H × (State × Action))) := Fintype.equivFin _
  exact fun k r => (p.val k (e r)).val

/-- Every coordinate selected by a source-bounded profile level lies in the
finite expanded stack. -/
theorem onlineMVPProfileBatchIndex_lt_K_of_level_bound
    {K : ℕ} (hK : 2 ≤ K) (j : ℕ)
    (hj : j ≤ profileLevelCap K)
    (i : Fin (onlineMVPProfileBatchSize j)) :
    onlineMVPProfileBatchStart j + i.val < K := by
  by_cases hj0 : j = 0
  · subst j
    exact Fin.elim0 i
  · by_cases hj1 : j = 1
    · subst j
      simp [onlineMVPProfileBatchSize, onlineMVPProfileBatchStart] at i ⊢
      omega
    · have hj2 : 2 ≤ j := by omega
      have hlevel : j - 1 ≤ Nat.log2 (K - 1) := by
        dsimp [profileLevelCap] at hj
        omega
      have hstartSize : onlineMVPProfileBatchStart j +
          onlineMVPProfileBatchSize j = 2 ^ (j - 1) := by
        rw [onlineMVPProfileBatchStart, onlineMVPProfileBatchSize,
          if_neg (by omega : ¬ j < 2), if_neg (by omega : j ≠ 0),
          if_neg (by omega : j ≠ 1)]
        have hexp : j - 2 + 1 = j - 1 := by omega
        calc
          2 ^ (j - 2) + 2 ^ (j - 2) = 2 * 2 ^ (j - 2) := by rw [← two_mul]
          _ = 2 ^ (j - 2) * 2 := by ring
          _ = 2 ^ (j - 2 + 1) := by rw [pow_succ]
          _ = 2 ^ (j - 1) := by rw [hexp]
      have hpow : 2 ^ (j - 1) ≤ 2 ^ Nat.log2 (K - 1) :=
        Nat.pow_le_pow_right (by decide) hlevel
      have hlog : 2 ^ Nat.log2 (K - 1) ≤ K - 1 := by
        simpa only [Nat.log2_eq_log_two] using
          Nat.pow_log_le_self 2 (by omega : K - 1 ≠ 0)
      have hi : i.val < onlineMVPProfileBatchSize j := i.isLt
      calc
        onlineMVPProfileBatchStart j + i.val <
            onlineMVPProfileBatchStart j + onlineMVPProfileBatchSize j := by omega
        _ = 2 ^ (j - 1) := hstartSize
        _ ≤ 2 ^ Nat.log2 (K - 1) := hpow
        _ ≤ K - 1 := hlog
        _ < K := by omega

/-- The bounded profile type therefore makes every future-code batch read valid. -/
theorem onlineMVPProfileBatchIndex_lt_K
    {H K : ℕ} (hK : 2 ≤ K)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (onlineMVPProfileBatchSize (onlineMVPProfileToNat p k r))) :
    onlineMVPProfileBatchStart (onlineMVPProfileToNat p k r) + i.val < K := by
  apply onlineMVPProfileBatchIndex_lt_K_of_level_bound hK
  unfold onlineMVPProfileToNat
  have hlt := (p.val k (Fintype.equivFin _ r)).isLt
  omega

/-- Extend an Assumption-X future code to a total stack stream.  Only rows at
stages later than h read the code; all other coordinates use a fixed fallback. -/
noncomputable def onlineMVPFutureCodeStream
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K) :
    OnlineMDPRow State Action H → ℕ → State := by
  let fallback := Classical.choice (E ⟨0, hH⟩).state_nonempty
  exact fun r i =>
    if hrow : h < r.1 then
      if hi : i < K then
        code ⟨((r.1, r.2.1, r.2.2), ⟨i, hi⟩), by
          simp [StatisticalRL.OnlineRL.MVPUniformSource.futureIndices]
          exact hrow⟩
      else fallback
    else fallback

/-- On every source-selected profile batch coordinate, the totalized stream
is exactly the supplied future code. The level bound proves the coordinate is
inside the finite stack, so the fallback branch is never used. -/
theorem onlineMVPFutureCodeStream_eq_code_on_profileBatch
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K)
    (k : Fin K) (r : OnlineMDPRow State Action H) (hh : h < r.1)
    (i : Fin (onlineMVPProfileBatchSize (onlineMVPProfileToNat p k r))) :
    onlineMVPFutureCodeStream hH E h code r
        (onlineMVPProfileBatchStart (onlineMVPProfileToNat p k r) + i.val) =
      code ⟨((r.1, r.2.1, r.2.2),
        ⟨onlineMVPProfileBatchStart (onlineMVPProfileToNat p k r) + i.val,
          onlineMVPProfileBatchIndex_lt_K hK p k r i⟩), by
        simp [StatisticalRL.OnlineRL.MVPUniformSource.futureIndices, hh]⟩ := by
  have hi := onlineMVPProfileBatchIndex_lt_K hK p k r i
  simp [onlineMVPFutureCodeStream, hh, hi,
    StatisticalRL.OnlineRL.MVPUniformSource.futureIndices]

/-- The source-profile batch of a totalized future stream is the actual finite
code slice, with no fallback coordinates. -/
theorem onlineMVPFutureCodeStream_profileBatch_eq_code
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K)
    (k : Fin K) (r : OnlineMDPRow State Action H) (hh : h < r.1) :
    onlineMVPFixedProfileBatch (onlineMVPFutureCodeStream hH E h code) r
        (onlineMVPProfileToNat p k r) =
      List.ofFn (fun i : Fin (onlineMVPProfileBatchSize
          (onlineMVPProfileToNat p k r)) =>
        code ⟨((r.1, r.2.1, r.2.2),
          ⟨onlineMVPProfileBatchStart (onlineMVPProfileToNat p k r) + i.val,
            onlineMVPProfileBatchIndex_lt_K hK p k r i⟩), by
          simp [StatisticalRL.OnlineRL.MVPUniformSource.futureIndices, hh]⟩) := by
  unfold onlineMVPFixedProfileBatch
  congr 1
  funext i
  exact onlineMVPFutureCodeStream_eq_code_on_profileBatch hH hK E p h code k r hh i

/-- Future-code family for one bounded monotone source profile. -/
noncomputable def onlineMVPSourceProfileFutureFamily
    {H K : ℕ} (hH : 0 < H) (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K) : Finset (State → ℝ) :=
  onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E
    (onlineMVPFutureCodeStream hH E h code) (onlineMVPProfileToNat p) h.val

theorem onlineMVPSourceProfileFutureFamily_zero_mem
    {H K : ℕ} (hH : 0 < H) (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K) :
    (fun _ : State => 0) ∈
      onlineMVPSourceProfileFutureFamily hH cap L c₁ c₂ E p h code := by
  change (fun _ : State => 0) ∈ onlineMVPZeroTerminalValueFamily cap L c₁ c₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1)
  exact onlineMVPZeroTerminalValueFamily_zero_mem cap L c₁ c₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1)

theorem onlineMVPSourceProfileFutureFamily_card_le
    {H K : ℕ} (hH : 0 < H) (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K) :
    (onlineMVPSourceProfileFutureFamily hH cap L c₁ c₂ E p h code).card ≤ K + 1 := by
  change (onlineMVPZeroTerminalValueFamily cap L c₁ c₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1)).card ≤ K + 1
  exact onlineMVPZeroTerminalValueFamily_card_le cap L c₁ c₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1)

theorem onlineMVPSourceProfileFutureFamily_range
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (cap L c₁ c₂ : ℝ) (hcap : 0 ≤ cap) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (p : StatisticalRL.OnlineRL.MVPUniformSource.Profiles
      (State := State) (Action := Action) H K)
    (h : Fin H)
    (code : StatisticalRL.OnlineRL.MVPUniformSource.FutureCode
      (State := State) (Action := Action) h K)
    {v : State → ℝ}
    (hv : v ∈ onlineMVPSourceProfileFutureFamily hH cap L c₁ c₂ E p h code) :
    ∀ s, 0 ≤ v s ∧ v s ≤ cap := by
  change v ∈ onlineMVPZeroTerminalValueFamily cap L c₁ c₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1) at hv
  exact onlineMVPZeroTerminalValueFamily_range cap L c₁ c₂ hcap hL hc₁ hc₂
    (fun k => onlineMVPFixedProfileStages E (onlineMVPFutureCodeStream hH E h code)
      (onlineMVPProfileToNat p) k) (h.val + 1) hv

/-- The actual state/action row count before episode k is the source count in
the finite monotone-profile construction. -/
theorem onlineMVPActualPreEpisodeCount_eq_sourceVisitCount
    {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    (onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data (k.val * H)) r).length =
    sourceMVPVisitCount
      (fun e h => (onlineMVPActualStackRowAt hH initial fallback planner data
        (e * H + h.val)).2) k.val r.1 r.2 := by
  classical
  let history := onlineMVPActualStackHistory hH initial fallback planner data (k.val * H)
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  let rowAt : ℕ → OnlineMDPRow State Action H :=
    onlineMVPActualStackRowAt hH initial fallback planner data
  have hlen : history.length = k.val * H := by
    simpa [history, onlineMVPActualStackHistory] using
      onlineStackHistory_length choose stream (k.val * H)
  have hr : onlineTranscriptRowsConsistent choose history := by
    simpa [history, choose, stream, onlineMVPActualStackHistory] using
      onlineActualStackHistory_rows_consistent choose stream (k.val * H)
  have hrows : ∀ j : Fin history.length, rowAt j.val = (history.get j).1 := by
    intro j
    have hprefix : history.take j.val = onlineStackHistory choose stream j.val := by
      change (onlineStackHistory choose stream (k.val * H)).take j.val =
        onlineStackHistory choose stream j.val
      exact onlineStackHistory_take choose stream (k.val * H) j.val (by simpa [hlen] using j.isLt.le)
    have hchosen := hr j
    calc
      rowAt j.val = choose (onlineStackHistory choose stream j.val) := by
        rfl
      _ = choose (history.take j.val) := congrArg choose hprefix.symm
      _ = (history.get j).1 := hchosen.symm
  have hstage (j : ℕ) (hj : j < k.val * H) :
      (rowAt j).1.val = j % H := by
    exact onlineMVPActualStackRowAt_stage hH initial fallback planner data j
  have hobs := onlineObserved_stage_episode_count_eq history rowAt r.1 k.val hH
    (by simpa [hlen]) r rfl hrows hstage
  have htaken : history.take (k.val * H) = history := by
    simpa [hlen] using List.take_length history
  rw [htaken] at hobs
  have hproj : ∀ e, (rowAt (e * H + r.1.val) = r) ↔
      (rowAt (e * H + r.1.val)).2 = r.2 := by
    intro e
    constructor
    · intro he
      exact congrArg Prod.snd he
    · intro he
      apply Prod.ext
      · apply Fin.ext
        have hmod : (e * H + r.1.val) % H = r.1.val := by
          rw [Nat.add_comm, Nat.mul_comm e H, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt r.1.isLt
        change (onlineMVPActualStackRowAt hH initial fallback planner data
          (e * H + r.1.val)).1.val = r.1.val
        rw [onlineMVPActualStackRowAt_stage, hmod]
      · exact he
  have hobsActual : (onlineRowOutcomes history r).length =
      onlineVisitCount (fun e => onlineMVPActualStackRowAt hH initial fallback planner data
        (e * H + r.1.val)) k.val r := by
    simpa [rowAt] using hobs
  have hcard :
      ((Finset.range k.val).filter (fun e =>
        onlineMVPActualStackRowAt hH initial fallback planner data
          (e * H + r.1.val) = r)).card =
        ((Finset.range k.val).filter (fun e =>
          (fun e h => (onlineMVPActualStackRowAt hH initial fallback planner data
            (e * H + h.val)).2) e r.1 = r.2)).card := by
    apply Finset.card_bij' (fun e _ => e) (fun e _ => e)
    · intro e he
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      have hpr := (hproj e).1 he'.2
      exact ⟨he'.1, by simpa using hpr⟩
    · intro e he
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      have hpr := (hproj e).2 he'.2
      exact ⟨he'.1, by simpa using hpr⟩
    · intro e he
      rfl
    · intro e he
      rfl
  have hcount : sourceMVPVisitCount
      (fun e h => (onlineMVPActualStackRowAt hH initial fallback planner data
        (e * H + h.val)).2) k.val r.1 r.2 =
      onlineVisitCount (fun e => onlineMVPActualStackRowAt hH initial fallback planner data
        (e * H + r.1.val)) k.val r := by
    unfold sourceMVPVisitCount onlineVisitCount
    congr 1
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hrow⟩
      exact ⟨he, (hproj e).2 (by simpa using hrow)⟩
    · rintro ⟨he, hrow⟩
      exact ⟨he, (hproj e).1 (by simpa using hrow)⟩
  exact hobsActual.trans hcount.symm

/-- The actual pre-episode natural profile is the level-valued source profile
encoded by its canonical finite monotone table. -/
theorem onlineMVPActualPreEpisodeProfile_eq_profileToNat
    {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    onlineMVPActualPreEpisodeProfile hH initial fallback planner data =
      onlineMVPProfileToNat
        (sourceMVPActualProfileTable
          (fun e h => (onlineMVPActualStackRowAt hH initial fallback planner data
            (e * H + h.val)).2)) := by
  classical
  funext k r
  have hc := onlineMVPActualPreEpisodeCount_eq_sourceVisitCount hH initial fallback
    planner data k r
  let e : OnlineMDPRow State Action H ≃
      Fin (Fintype.card (Fin H × (State × Action))) := Fintype.equivFin _
  simp [onlineMVPActualPreEpisodeProfile, onlineMVPProfileToNat,
    sourceMVPActualProfileTable, sourceMVPActualProfile, hc, e]

/-- At the actual pre-episode profile, and using the actual future suffix of
the expanded stack, every realized episode value is in the source family. -/
theorem onlineMVPActualPreEpisodeValue_mem_sourceProfileFamily
    {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (cap L c₁ c₂ : ℝ) (fallback : State)
    (hfallback : fallback = Classical.choice (E ⟨0, hH⟩).state_nonempty)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (h : Fin H) :
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
  have hstream : ∀ (r : OnlineMDPRow State Action H) (i : ℕ),
      h.val < r.1.val →
      onlineMVPFutureCodeStream hH E h
          (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data) r i =
        onlineFiniteStackExtend K fallback data r i := by
    intro r i hir
    rw [hfallback]
    have hrow : h < r.1 := by
      exact Fin.mk_lt_mk.mpr hir
    simp [onlineMVPFutureCodeStream, StatisticalRL.OnlineRL.MVPUniformSource.futureData,
      onlineFiniteStackExtend, hrow]
  have hfuture := onlineMVPFixedProfileFutureFamily_congr_future
    cap L c₁ c₂ E
    (onlineMVPFutureCodeStream hH E h
      (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
    (onlineFiniteStackExtend K fallback data)
    (onlineMVPActualPreEpisodeProfile hH initial fallback planner data)
    h.val h.isLt hstream
  rw [hfixed] at hmem
  rw [← hfuture] at hmem
  rw [hprofile] at hmem
  change onlineCappedBackwardValueAt cap L c₁ c₂
      (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1) ∈
    onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E
      (onlineMVPFutureCodeStream hH E h
        (StatisticalRL.OnlineRL.MVPUniformSource.futureData h K data))
      (onlineMVPProfileToNat (sourceMVPActualProfileTable rows)) h.val
  exact hmem

end StatisticalRL.OnlineRL
