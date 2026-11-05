import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankRadius

/-! Consume the normalized-square half of the actual profile event and apply
the already-proved squared rank-error endpoint. This is a stack-data
consumer; it does not yet assert a W3/W4 event or the sequential-law theorem. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile
open StatisticalRL.OnlineRL.MVPUniformSource
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpRankSquareStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpRankSquareStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpRankSquareActionDecidable : DecidableEq Action := Classical.decEq Action

theorem mvp_actualRankSquareSlotRadiusCondition_of_squareEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hL : L = Real.log (1 / onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K))
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualNormalizedSquareSourceFamily hH E L c₁ c₂)) :
    let rows := mvpActualRankRows hH initial fallback planner data
    let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
    mvp_rankSlotRadiusCondition rows K (fun h k => mvp_normalizedSquare (H : ℝ) (V h k))
      (mvpActualRankTransition E) (mvpActualRankInitial E hH)
      (mvpActualRankFirst (by omega) data) (mvpActualRankBatch data)
      ((Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action))
      (H : ℝ)
      (40000 * (Real.log K / Real.log 2)^3 *
        Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
  let rows := mvpActualRankRows hH initial fallback planner data
  let p := mvpActualRankTransition E
  let q0 := mvpActualRankInitial E hH
  let q1 := mvpActualRankFirst (by omega) data
  let qb := mvpActualRankBatch data
  let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
  let I := 40000 * (Real.log K / Real.log 2)^3 *
    Real.log (3 * Fintype.card (Fin H × (State × Action))) * L
  change mvp_rankSlotRadiusCondition rows K (fun h k => mvp_normalizedSquare (H : ℝ) (V h k))
    p q0 q1 qb d (H : ℝ) I
  intro j hj i hi
  let jf : Fin (Nat.log2 K) := ⟨j, hj⟩
  let ifin : Fin (2 * 2 ^ j) := ⟨i, hi⟩
  let ell : mvpUniformLevel K := ⟨j, hj⟩
  let test := mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data L c₁ c₂ jf ifin
  have hslot := mvpActualAdaptiveSquareSlot_bound_of_quarterEvent
    hH hK E δ L c₁ c₂ initial fallback planner data hgood ell jf ifin
  have hbatch (h : Fin H) (r : State × Action) :
      qb h r jf = FiniteDistribution.empiricalRow (2 ^ j)
        (by positivity) (fun q : Fin (2 ^ j) =>
          data ((h, r), mvpBatchIndex K (2 ^ j)
            (by
              have hf := mvpUniformBatchSize_fits hK ell
              simpa [ell, mvpUniformBatchSize] using hf) q)) := by
    change FiniteDistribution.empiricalRow (2 ^ j) (by positivity) _ = _
    congr 1
  have hrows (h : Fin H) : rows h = mvpActualAdaptiveStageRows hH initial fallback planner data h := rfl
  have hvalues (h : Fin H) : V h = mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h := rfl
  have htest (h : Fin H) (r : State × Action) :
      test h r.1 r.2 = mvp_visitValueLookup (rows h) K r
        (2 * 2 ^ j + i) (fun k => mvp_normalizedSquare (H : ℝ) (V h k)) := by
    change mvp_normalizedSquare (H : ℝ)
        (mvp_visitValueLookup (mvpActualAdaptiveStageRows hH initial fallback planner data h)
          K r (2 * 2 ^ j + i)
          (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)) = _
    rw [← hrows h, ← hvalues h]
    exact mvp_visitValueLookup_map (rows h) K r (2 * 2 ^ j + i) (V h)
      (mvp_normalizedSquare (H : ℝ)) (mvp_normalizedSquare_zero (H : ℝ))
  have hsum :
      (∑ h : Fin H, ∑ r : State × Action,
        mvp_rankErrorAt (rows h) K r (fun k => mvp_normalizedSquare (H : ℝ) (V h k))
          (p h r) (q0 h r) (q1 h r) (qb h r) (2 * 2 ^ j + i)) =
      ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((qb h (s, a) jf).expectation (test h s a) -
          (p h (s, a)).expectation (test h s a)) 0 := by
    calc
      _ = ∑ h : Fin H, ∑ r : State × Action,
          max ((qb h r jf).expectation (test h r.1 r.2) -
            (p h r).expectation (test h r.1 r.2)) 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro r hr
        change mvp_rankPositiveError K (p h r) (q0 h r) (q1 h r) (qb h r)
          (2 * 2 ^ j + i)
          (mvp_visitValueLookup (rows h) K r (2 * 2 ^ j + i)
            (fun k => mvp_normalizedSquare (H : ℝ) (V h k))) = _
        rw [mvp_rankPositiveError_lookup_at_slot (rows h) K r
          (fun k => mvp_normalizedSquare (H : ℝ) (V h k))
          (p h r) (q0 h r) (q1 h r) (qb h r) jf i hi]
        simp [mvp_rowPositiveError]
        rw [← htest h r]
      _ = _ := by simp [Fintype.sum_prod_type]
  rw [hsum]
  have hlogK : Real.log (K : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < K by omega)))
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hpow : ((2 : ℝ) ^ j) ≠ 0 := by positivity
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hcoef : d * I * (Real.log 2)^3 =
      -(Real.log (K : ℝ))^3 * (H : ℝ) * Fintype.card State * Fintype.card Action *
        Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action * 3) *
        Real.log δp * 40000 := by
    dsimp [d, I, δp]
    simp only [Fintype.card_fin, Fintype.card_prod]
    push_cast
    rw [hL]
    simp only [one_div, Real.log_inv]
    have harg :
        3 * ((H : ℝ) * ((Fintype.card State : ℝ) * Fintype.card Action)) =
          ((H : ℝ) * ((Fintype.card State : ℝ) * Fintype.card Action)) * 3 := by ring
    rw [harg]
    field_simp [hlog2, hlogK]
    <;> ring
  have hvar :
      (∑ h : Fin H, ∑ r : State × Action,
        (p h r).variance
          (mvp_visitValueLookup (rows h) K r (2 * 2 ^ j + i)
            (fun k => mvp_normalizedSquare (H : ℝ) (V h k)))) =
      ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        ((E h).transition s a).variance
          (mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
            L c₁ c₂ jf ifin h s a) := by
    have hmap (h : Fin H) (r : State × Action) :
        mvp_visitValueLookup (rows h) K r (2 * 2 ^ j + i)
            (fun k => mvp_normalizedSquare (H : ℝ) (V h k)) =
          mvp_normalizedSquare (H : ℝ)
            (mvp_visitValueLookup (rows h) K r (2 * 2 ^ j + i) (V h)) :=
      (mvp_visitValueLookup_map (rows h) K r (2 * 2 ^ j + i) (V h)
        (mvp_normalizedSquare (H : ℝ)) (mvp_normalizedSquare_zero (H : ℝ))).symm
    simp_rw [hmap]
    simp [jf, ifin, p, hrows, hvalues, mvpActualRankTransition,
      mvpActualAdaptiveSquareSlotTest, mvpActualAdaptiveValueSlotTest,
      Fintype.sum_prod_type]
  rw [← hvar] at hslot
  convert hslot using 1 <;>
    simp [jf, ifin, test, p, qb, mvpActualRankTransition, hbatch,
      mvpActualAdaptiveSquareSlotTest, ell, mvpUniformBatchSize, mvpBatchIndex,
      Fintype.card_prod, Fintype.card_fin, mvpActualRankRows,
      mvpActualAdaptiveStageRows, mvpActualRankValues,
      mvpActualAdaptiveValueTable, hL]
  congr 1
  · congr 1
    field_simp [hlogK, hlog2, hpow]
    rw [hcoef]
    ring
  · field_simp [hlogK, hlog2, hpow]
    rw [hcoef]
    <;> ring

/-- Consume both source profile events to bound the actual linear and squared
rank-error totals for the same bounded backward-value table. -/
theorem mvp_actualRankLinearAndSquareBounds_of_quarterEvents
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hL : L = Real.log (1 / onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K))
    (hgoodV : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E L c₁ c₂))
    (hgoodSq : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualNormalizedSquareSourceFamily hH E L c₁ c₂)) :
    let rows := mvpActualRankRows hH initial fallback planner data
    let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
    let p := mvpActualRankTransition E
    let q0 := mvpActualRankInitial E hH
    let q1 := mvpActualRankFirst (by omega) data
    let qb := mvpActualRankBatch data
    let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L
    let T := ∑ h : Fin H, ∑ k : Fin K,
      (p h (rows h k.val)).variance (V h k)
    mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I ∧
    mvp_rankErrorTotal rows K (fun h k s => V h k s ^ 2) p q0 q1 qb ≤
      Real.sqrt (d * H^2 * I * T) + d * H^2 * I := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
  let rows := mvpActualRankRows hH initial fallback planner data
  let p := mvpActualRankTransition E
  let q0 := mvpActualRankInitial E hH
  let q1 := mvpActualRankFirst (by omega) data
  let qb := mvpActualRankBatch data
  let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
  let I := 40000 * (Real.log K / Real.log 2)^3 *
    Real.log (3 * Fintype.card (Fin H × (State × Action))) * L
  let T := ∑ h : Fin H, ∑ k : Fin K,
    (p h (rows h k.val)).variance (V h k)
  change mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I ∧
    mvp_rankErrorTotal rows K (fun h k s => V h k s ^ 2) p q0 q1 qb ≤
      Real.sqrt (d * H^2 * I * T) + d * H^2 * I
  constructor
  · exact mvp_actualRankLinearBound_of_valueEvent hH hK E δ L c₁ c₂
      initial fallback planner data hgoodV hδ hδ1 hL hc₁ hc₂
  · have hslot := mvp_actualRankSquareSlotRadiusCondition_of_squareEvent
      hH hK E δ L c₁ c₂ initial fallback planner data hL hgoodSq
    have hV : ∀ h k s, 0 ≤ V h k s ∧ V h k s ≤ H := by
      intro h k s
      dsimp [V, mvpActualRankValues]
      have hstate : 0 < Fintype.card State := by
        apply Fintype.card_pos_iff.mpr
        exact ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
      have haction : 0 < Fintype.card Action := by
        apply Fintype.card_pos_iff.mpr
        exact ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
      have hδp := mvp_correctedAllocation_domain_and_log δ
        (Fintype.card State) (Fintype.card Action) H K hδ hδ1 hstate haction hH (by omega)
      have hL0 : 0 ≤ L := by rw [hL]; linarith [hδp.2.2]
      exact (onlineCappedBackwardAt_range (H : ℝ) L c₁ c₂ (by positivity)
        hL0 hc₁ hc₂ (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k)
        (h.val + 1)).1 s
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hstate : 0 < Fintype.card State := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
    have haction : 0 < Fintype.card Action := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
    have hI : 4 ≤ I := by
      have hd : 1 ≤ Fintype.card (Fin H × (State × Action)) := by
        apply Fintype.card_pos_iff.mpr
        exact ⟨(⟨0, hH⟩, (Classical.choice (E ⟨0, hH⟩).state_nonempty,
          Classical.choice (E ⟨0, hH⟩).action_nonempty))⟩
      have hδp := mvp_correctedAllocation_domain_and_log δ
        (Fintype.card State) (Fintype.card Action) H K hδ hδ1 hstate haction hH (by omega)
      have hI' := mvp_sourceIota_ge_20000
        (Fintype.card (Fin H × (State × Action))) K
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)
        hd hK hδp.1 hδp.2.1
      dsimp [I]
      rw [hL]
      nlinarith [hI']
    exact mvp_rankErrorTotal_square_bound rows K hK V p q0 q1 qb
      (H : ℝ) I (by exact_mod_cast hH) hI hV hslot

end StatisticalRL.OnlineRL
