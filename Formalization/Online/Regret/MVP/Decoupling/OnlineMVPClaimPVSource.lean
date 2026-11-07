import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPClaimPVSlotIdentity
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankBoundsStackProbability
import Formalization.Online.Regret.MVP.Decoupling.DecouplingImageTransport
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Claim 5.1 (`claim:PV-l-UB`, `chapters/onlineRL.tex:4340–4353`, proved in the
book at `:4406–4476`) on the actual sequential MVP experiment: simultaneous
per-level, per-slot confidence bounds for the batch-row errors, with the
explicit batch row `P̂^{(l)}` read from the completed history. -/

namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile

universe u v

variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
noncomputable local instance claimPVSourceStateDecidable : DecidableEq State :=
  Classical.decEq State
noncomputable local instance claimPVSourceActionDecidable : DecidableEq Action :=
  Classical.decEq Action
local instance claimPVSourceStateMeasurable : MeasurableSpace State := ⊤

/-- Level `l = 1` (first-sample batch) is deterministic: each visit term is at
most `H`, and each stage row has at most one visit of pre-count one. -/
theorem claimPV_levelOne_bound {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (Phat : Fin H → Fin K → FiniteDistribution State) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let sa := fun (h : Fin H) (e : ℕ) =>
      onlineActualStageRowSequence H K hH initial fallback planner path h e
    let cnt := fun (h : Fin H) (k : Fin K) =>
      ((Finset.range k.val).filter (fun e => sa h e = sa h k.val)).card
    let U := fun (h : Fin H) (k : Fin K) =>
      onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
        (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))) (h.val + 1)
    claimPVSlotError E sa cnt Phat U 1 ≤
      (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) * H := by
  classical
  intro history sa cnt U
  let rows := mvpActualRankRows hH initial fallback planner data
  have hHr : (0 : ℝ) ≤ H := by positivity
  have hU : ∀ h k s, 0 ≤ U h k s ∧ U h k s ≤ (H : ℝ) := by
    intro h k s
    exact (onlineCappedBackwardAt_range (H : ℝ) L c₁ c₂ hHr hL hc₁ hc₂
      (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H)))
      (h.val + 1)).1 s
  have hterm : claimPVSlotError E sa cnt Phat U 1 ≤
      ∑ h : Fin H, ∑ k : Fin K, if cnt h k = 1 then (H : ℝ) else 0 := by
    unfold claimPVSlotError
    apply Finset.sum_le_sum
    intro h _
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · have h1 := (Phat h k).expectation_le_const (fun s => (hU h k s).2)
      have h2 := ((E h).transition (sa h k.val).1 (sa h k.val).2).expectation_nonneg
        (fun s => (hU h k s).1)
      linarith
    · exact le_rfl
  have hrow : ∀ h : Fin H,
      (∑ k : Fin K, if cnt h k = 1 then (H : ℝ) else 0) ≤
        (Fintype.card (State × Action) : ℝ) * H := by
    intro h
    have hcount : ∀ k : Fin K,
        cnt h k = onlineVisitCount (rows h) k.val (rows h k.val) := fun k =>
      claimPV_count_eq hH E initial fallback planner data path htranscript h k
    have hreg := mvp_slotSum_eq_rowLookupSum (rows h) K 1 (fun _ : Fin K => (H : ℝ))
      (fun _ w => w) (fun _ => rfl)
    calc
      (∑ k : Fin K, if cnt h k = 1 then (H : ℝ) else 0) =
          ∑ k : Fin K, if onlineVisitCount (rows h) k.val (rows h k.val) = 1
            then (H : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hcount k]
      _ = ∑ r : State × Action,
          mvp_visitValueLookup (rows h) K r 1 (fun _ : Fin K => (H : ℝ)) := hreg
      _ ≤ ∑ _r : State × Action, (H : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hex : ∃ k : Fin K, rows h k.val = r ∧ onlineVisitCount (rows h) k.val r = 1
        · obtain ⟨k, hk⟩ := hex
          rw [mvp_visitValueLookup_hit (rows h) K r 1 _ k hk]
        · rw [mvp_visitValueLookup_zero (rows h) K r 1 _ (fun k hk => hex ⟨k, hk⟩)]
          exact hHr
      _ = (Fintype.card (State × Action) : ℝ) * H := by
        simp [Finset.sum_const, Finset.card_univ]
  calc
    claimPVSlotError E sa cnt Phat U 1 ≤
        ∑ h : Fin H, ∑ k : Fin K, if cnt h k = 1 then (H : ℝ) else 0 := hterm
    _ ≤ ∑ _h : Fin H, (Fintype.card (State × Action) : ℝ) * H :=
        Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) * H := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

/-- The Claim 5.1 event on one sequential sample, for confidence parameter
`δp` and log factor `I`. The batch row of level `l` is read explicitly from the
completed history (Option B); see `claimPVPathBatch`. -/
noncomputable def claimPVEvent (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δp c₁ c₂ I : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
  {sample |
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let U := fun (h : Fin H) (k : Fin K) =>
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δp)) c₁ c₂
        (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))) (h.val + 1)
    let sa := fun (h : Fin H) (e : ℕ) =>
      onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h e
    let cnt := fun (h : Fin H) (k : Fin K) =>
      ((Finset.range k.val).filter (fun e => sa h e = sa h k.val)).card
    let Phat := fun (l : ℕ) (h : Fin H) (k : Fin K) =>
      FiniteDistribution.empiricalRow (2^(l-2)) (by positivity)
        (fun q : Fin (2^(l-2)) => (onlineRowOutcomes history (h, sa h k.val)).getD
          ((if l = 1 then 0 else 2^(l-2)) + q.val) fallback)
    let d := (Fintype.card State : ℝ) * Fintype.card Action * H
    let x := Real.log K / Real.log 2
    ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ x → ∀ j : ℕ, 1 ≤ j → j ≤ 2^(l-1) →
      (∑ h : Fin H, ∑ k : Fin K,
        if cnt h k = 2^(l-1) + j - 1 then
          (Phat l h k).expectation (U h k) -
            ((E h).transition (sa h k.val).1 (sa h k.val).2).expectation (U h k)
        else 0) ≤
      Real.sqrt (d * I / (2^l * x) * ∑ h : Fin H, ∑ k : Fin K,
        if cnt h k = 2^(l-1) + j - 1 then
          ((E h).transition (sa h k.val).1 (sa h k.val).2).variance (U h k)
        else 0) +
      d * (H : ℝ) * I / (2^l * x)}

/-- Source integer level range: `l ≤ log₂ K` (real) gives `l ≤ Nat.log2 K`. -/
theorem claimPV_level_le_log2 (K l : ℕ) (hK : 0 < K)
    (hl : (l : ℝ) ≤ Real.log K / Real.log 2) : l ≤ Nat.log2 K := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul : (l : ℝ) * Real.log 2 ≤ Real.log K := (le_div_iff₀ hlog2).1 hl
  have hpow : Real.log ((2 : ℝ)^l) ≤ Real.log K := by
    rw [Real.log_pow]; exact hmul
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hle : (2 : ℝ)^l ≤ K := (Real.log_le_log_iff (by positivity) hKr).1 hpow
  have hleN : 2^l ≤ K := by exact_mod_cast hle
  exact (Nat.le_log2 (Nat.pos_iff_ne_zero.mp hK)).2 hleN

/-- Radius monotonicity from the stack slot (`1/(16·2^jL)`) to the source
level `l = jL+2` (`1/2^l = 1/(4·2^jL)`). -/
theorem claimPV_scalar_high (d I x H V e : ℝ) (jL : ℕ) (hd0 : 0 ≤ d) (hI0 : 0 ≤ I)
    (hx : 0 < x) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (h : e ≤ Real.sqrt (d * I * ((1:ℝ) / (16 * (2:ℝ)^jL * x)) * V) +
      (d * H * I) * ((1:ℝ) / (16 * (2:ℝ)^jL * x))) :
    e ≤ Real.sqrt (d * I / (2^(jL + 2) * x) * V) + d * H * I / (2^(jL + 2) * x) := by
  have hp : (0:ℝ) < 2^jL := by positivity
  have hden : (2:ℝ)^(jL + 2) * x ≤ 16 * (2:ℝ)^jL * x := by
    rw [pow_add]
    have : (0:ℝ) ≤ (2:ℝ)^jL * x := by positivity
    nlinarith
  have hdenpos : 0 < (2:ℝ)^(jL + 2) * x := by positivity
  have hc1 : d * I * ((1:ℝ) / (16 * (2:ℝ)^jL * x)) ≤ d * I / (2^(jL + 2) * x) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) hdenpos hden
  have hc2 : (d * H * I) * ((1:ℝ) / (16 * (2:ℝ)^jL * x)) ≤ d * H * I / (2^(jL + 2) * x) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) hdenpos hden
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hc1 hV)
  linarith

/-- The deterministic level-one radius dominates `d·H` once `I ≥ 2x`. -/
theorem claimPV_scalar_one (d I x H V e : ℝ) (hd0 : 0 ≤ d) (hH : 0 ≤ H) (hx : 0 < x)
    (hIx : 2 * x ≤ I) (h : e ≤ d * H) :
    e ≤ Real.sqrt (d * I / (2^1 * x) * V) + d * H * I / (2^1 * x) := by
  have hdH : d * H ≤ d * H * I / (2^1 * x) := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ d * H := by positivity
    nlinarith
  have hsq := Real.sqrt_nonneg (d * I / (2^1 * x) * V)
  linarith

/-- `ι ≥ 2 log₂ K` under the reciprocal allocation. -/
theorem claimPV_iota_ge (x a L : ℝ) (hx1 : 1 ≤ x) (ha : 1 / 2 ≤ a) (hL : 1 ≤ L) :
    2 * x ≤ 40000 * x^3 * a * L := by
  have hx3 : x ≤ x^3 := by
    have h0 : 0 ≤ x * (x - 1) * (x + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hA1 : 0 ≤ x^3 := by positivity
  calc 2 * x ≤ 40000 * x^3 * (1/2) * 1 := by nlinarith
    _ ≤ 40000 * x^3 * a * 1 := by gcongr
    _ ≤ 40000 * x^3 * a * L := by
      have : 0 ≤ 40000 * x^3 * a := by
        have : 0 ≤ a := by linarith
        positivity
      nlinarith

/-- Pointwise Claim 5.1 on the actual value-family event and transcript
equality (`K ≥ 2`). -/
theorem claimPVEvent_mem_of_transcript {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath.{u, 0} State (K * H))
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E (Real.log (1 / onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K)) c₁ c₂))
    (htranscript :
      let L := Real.log (1 / onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K)
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂)) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) data (K * H)) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1 / δp)
    (initial, path) ∈ claimPVEvent H K hH E fallback δp c₁ c₂ I := by
  intro δp I
  let L := Real.log (1 / δp)
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  have hS : 0 < Fintype.card State :=
    Fintype.card_pos_iff.mpr ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
  have hA : 0 < Fintype.card Action :=
    Fintype.card_pos_iff.mpr ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
  have hdomain := mvp_correctedAllocation_domain_and_log δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδ1 hS hA hH (by omega)
  have hL1 : 1 ≤ L := hdomain.2.2
  have hL0 : 0 ≤ L := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hx1 : (1 : ℝ) ≤ Real.log K / Real.log 2 := by
    rw [le_div_iff₀ hlog2, one_mul]
    exact Real.log_le_log (by norm_num) hKr
  have hd' : (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) =
      (Fintype.card State : ℝ) * Fintype.card Action * H := by
    simp only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul]
    ring
  have hI' : 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card (Fin H × (State × Action)) : ℝ)) * L = I := by
    have harg : (3 * (Fintype.card (Fin H × (State × Action)) : ℝ)) =
        3 * (Fintype.card State : ℝ) * Fintype.card Action * H := by
      simp only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul]
      ring
    rw [harg]
  have hI0 : 0 ≤ I := by
    have h3 : (1 : ℝ) ≤ 3 * (Fintype.card State : ℝ) * Fintype.card Action * H := by
      have : (1 : ℝ) ≤ (Fintype.card State : ℝ) * Fintype.card Action * H := by
        have h1 : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast hS
        have h2 : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast hA
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hH
        exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
      linarith
    have := Real.log_nonneg h3
    change 0 ≤ 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * L
    positivity
  unfold claimPVEvent
  rw [Set.mem_setOf_eq]
  intro planner' history U sa cnt Phat d x l hl1 hlx j hj1 hj2
  have hd0 : 0 ≤ d := by positivity
  have hxpos : 0 < x := by linarith
  rcases Nat.lt_or_ge l 2 with hl | hl
  · -- level l = 1: deterministic
    have hl' : l = 1 := by omega
    subst hl'
    have hj : j = 1 := by simp at hj2; omega
    subst hj
    have hone := claimPV_levelOne_bound hH E L c₁ c₂ hL0 hc₁ hc₂ initial fallback planner data
      path htranscript (Phat 1)
    have hone' : claimPVSlotError E sa cnt (Phat 1) U 1 ≤
        (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) * H := hone
    rw [hd'] at hone'
    have hIx : 2 * x ≤ I := by
      have hy : (3 : ℝ) ≤ 3 * (Fintype.card State : ℝ) * Fintype.card Action * H := by
        have h1 : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast hS
        have h2 : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast hA
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hH
        have : (1 : ℝ) ≤ (Fintype.card State : ℝ) * Fintype.card Action * H :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
        linarith
      have hlogpos : (1 : ℝ) / 2 ≤
          Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) := by
        have hb := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) <
          3 * (Fintype.card State : ℝ) * Fintype.card Action * H)
        have hinv : (3 * (Fintype.card State : ℝ) * Fintype.card Action * H)⁻¹ ≤ 1 / 3 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          simpa using hy
        linarith
      exact claimPV_iota_ge x _ L hx1 hlogpos hL1
    exact claimPV_scalar_one d I x H _ _ hd0 (by positivity) hxpos hIx hone'
  · -- level l = jL + 2 ≥ 2: stack slot jL, i = j - 1
    obtain ⟨jL, rfl⟩ : ∃ jL, l = jL + 2 := ⟨l - 2, by omega⟩
    have hlog := claimPV_level_le_log2 K (jL + 2) (by omega) hlx
    have hjL : jL < Nat.log2 K := by omega
    have hpow : 2^(jL + 2 - 1) = 2 * 2^jL := by
      rw [show jL + 2 - 1 = jL + 1 by omega, pow_succ]; ring
    have hi : j - 1 < 2 * 2^jL := by rw [hpow] at hj2; omega
    have hu : 2^(jL + 2 - 1) + j - 1 = 2 * 2^jL + (j - 1) := by rw [hpow]; omega
    have hslot := claimPV_slot_bound hH hK E δ L c₁ c₂ initial fallback data path rfl hgood
      htranscript jL hjL (j - 1) hi
    have hslot' : claimPVSlotError E sa cnt (Phat (jL + 2)) U (2 * 2^jL + (j - 1)) ≤
        Real.sqrt ((Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) *
          (40000 * (Real.log K / Real.log 2)^3 *
            Real.log (3 * (Fintype.card (Fin H × (State × Action)) : ℝ)) * L) *
          ((1:ℝ) / (16 * (2:ℝ)^jL * (Real.log K / Real.log 2))) *
          claimPVSlotVariance E sa cnt U (2 * 2^jL + (j - 1))) +
        ((Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action) * H *
          (40000 * (Real.log K / Real.log 2)^3 *
            Real.log (3 * (Fintype.card (Fin H × (State × Action)) : ℝ)) * L)) *
          ((1:ℝ) / (16 * (2:ℝ)^jL * (Real.log K / Real.log 2))) := hslot
    rw [hd', hI'] at hslot'
    change claimPVSlotError E sa cnt (Phat (jL + 2)) U (2^(jL + 2 - 1) + j - 1) ≤
      Real.sqrt (d * I / (2^(jL + 2) * x) *
        claimPVSlotVariance E sa cnt U (2^(jL + 2 - 1) + j - 1)) +
      d * H * I / (2^(jL + 2) * x)
    rw [hu]
    change claimPVSlotError E sa cnt (Phat (jL + 2)) U (2 * 2^jL + (j - 1)) ≤
      Real.sqrt (d * I * ((1:ℝ) / (16 * (2:ℝ)^jL * x)) *
        claimPVSlotVariance E sa cnt U (2 * 2^jL + (j - 1))) +
      (d * H * I) * ((1:ℝ) / (16 * (2:ℝ)^jL * x)) at hslot'
    have hV0 : 0 ≤ claimPVSlotVariance E sa cnt U (2 * 2^jL + (j - 1)) := by
      unfold claimPVSlotVariance
      apply Finset.sum_nonneg; intro h _
      apply Finset.sum_nonneg; intro k _
      split_ifs
      · exact FiniteDistribution.variance_nonneg _ _
      · exact le_rfl
    exact claimPV_scalar_high d I x H _ _ jL hd0 hI0 hxpos (by positivity) hV0 hslot'

/-- Claim 5.1 confidence on the actual sequential law, with the reciprocal
allocation `δp = onlineSourceOptimismDeltaPrime δ S A H K`. -/
theorem claimPV_eventConfidence (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hbudget : (Fintype.card State : ℝ) * Fintype.card Action * H *
      (Real.log K / Real.log 2) ≤ (K : ℝ)) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1 / δp)
    1 - δp < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂)
      (K * H)).rowMeasure.real (claimPVEvent H K hH E fallback δp c₁ c₂ I) := by
  intro δp I
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂
  have hS : 0 < Fintype.card State :=
    Fintype.card_pos_iff.mpr ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
  have hA : 0 < Fintype.card Action :=
    Fintype.card_pos_iff.mpr ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
  have hdomain := mvp_correctedAllocation_domain_and_log δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδ1 hS hA hH hK
  have hδp : 0 < δp := hdomain.1
  rcases (show K = 1 ∨ 2 ≤ K by omega) with hK1 | hK2
  · -- K = 1: no level satisfies `1 ≤ l ≤ log₂ K = 0`
    have hEvent : claimPVEvent H K hH E fallback δp c₁ c₂ I = Set.univ := by
      apply Set.eq_univ_of_forall
      intro sample
      unfold claimPVEvent
      rw [Set.mem_setOf_eq]
      intro planner' history U sa cnt Phat d x l hl1 hlx
      exfalso
      have hx0 : x = 0 := by
        change Real.log K / Real.log 2 = 0
        rw [hK1]
        simp
      have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
      linarith
    haveI : IsProbabilityMeasure
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure := by
      infer_instance
    change 1 - δp < (onlineSequentialEpisodeLaw H K hH E ρ fallback planner
      (K * H)).rowMeasure.real (claimPVEvent H K hH E fallback δp c₁ c₂ I)
    rw [hEvent, probReal_univ]
    linarith
  · let valueFamily := mvpActualValueSourceFamily (K := K) hH E (Real.log (1 / δp)) c₁ c₂
    let squareFamily := mvpActualNormalizedSquareSourceFamily (K := K) hH E
      (Real.log (1 / δp)) c₁ c₂
    let good : Set (Samples State Action H K) :=
      mvpQuarterStrongSourceUniformEvent hK2 E δ valueFamily ∩
        mvpQuarterStrongSourceUniformEvent hK2 E δ squareFamily
    let R : Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) :=
      Set.univ ×ˢ good
    have hbudget' : (K : ℝ) ≥
        (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K := by
      have hrowcard : (Fintype.card (Fin H × (State × Action)) : ℝ) =
          (Fintype.card State : ℝ) * Fintype.card Action * H := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        ring
      rw [hrowcard]
      simpa [logTwoReal] using hbudget
    have hquarter := mvp_actualProfileFamilies_quarterStrong_intersection
      E hH hK2 δ c₁ c₂ hδ hδ1 hc₁ hc₂ hbudget'
    have hgoodP : 1 - δp / 2 ≤ (samplingLaw E K).real good := hquarter.1
    have hlaw : onlineMDPStackLaw E K = samplingLaw E K := by
      dsimp [onlineMDPStackLaw, onlineStackProductLaw, samplingLaw,
        SampleIndex, OnlineMDPRow, onlineMDPSuccessorRowLaw]
    have hR : 1 - δp / 2 ≤ (onlineMDPInitialStackLaw E ρ K).real R := by
      have hlift : (onlineMDPInitialStackLaw E ρ K).real R = (samplingLaw E K).real good := by
        dsimp [R, onlineMDPInitialStackLaw]
        rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
        change (onlineMDPStackLaw E K).real good = (samplingLaw E K).real good
        rw [hlaw]
      rw [hlift]
      exact hgoodP
    have himage := onlineStack_rank_event_to_sequential_image_conditional
      H K hH E ρ fallback planner (K * H) le_rfl R
      (claimPVEvent H K hH E fallback δp c₁ c₂ I) δp hδp hR
      (by
        intro stack sample hobs hmem
        have hreset : stack.1 = sample.1 := congrArg Prod.fst hobs
        have htranscript :
            onlineSequentialPathHistory
              (onlineEpisodicChoose H K hH sample.1 fallback planner)
              (K * H) [] sample.2 =
            onlineMVPActualStackHistory hH sample.1 fallback planner stack.2 (K * H) := by
          have hsnd := (congrArg Prod.snd hobs).symm
          rw [hreset] at hsnd
          simpa [onlineMVPActualStackHistory] using hsnd
        have hgoodv : stack.2 ∈ mvpQuarterStrongSourceUniformEvent hK2 E δ valueFamily :=
          (Set.mem_prod.mp hmem).2.1
        exact claimPVEvent_mem_of_transcript hH hK2 E δ c₁ c₂ hδ hδ1 (by linarith)
          (by nlinarith) sample.1 fallback stack.2 sample.2 hgoodv htranscript)
    exact himage

end StatisticalRL.OnlineRL
