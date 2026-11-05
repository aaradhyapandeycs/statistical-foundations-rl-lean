import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualAdaptiveSlotEvent
import Formalization.Online.Regret.MVP.Decoupling.MVPRankErrorSourceBounds

/-! Consume the simultaneous profile event at all actual positive visit ranks,
then apply the finite rank-sum endpoints. This remains a stack-data pathwise
consumer; the sequential-law transfer is a separate result. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile
open StatisticalRL.OnlineRL.MVPUniformSource
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpRankRadiusStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpRankRadiusStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpRankRadiusActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def mvpActualRankRows {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → ℕ → State × Action :=
  fun h k => (onlineMVPActualStackRowAt hH initial fallback planner data
    (k * H + h.val)).2

noncomputable def mvpActualRankValues {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) : Fin H → Fin K → State → ℝ :=
  fun h k s => onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
    (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1) s

noncomputable def mvpActualRankTransition {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) :
    Fin H → (State × Action) → FiniteDistribution State :=
  fun h r => (E h).transition r.1 r.2

noncomputable def mvpActualRankInitial {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 0 < H) :
    Fin H → (State × Action) → FiniteDistribution State := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  exact fun _ _ => onlineUniformInitialRow

noncomputable def mvpActualRankFirst {H K : ℕ}
    (hK : 0 < K)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → (State × Action) → FiniteDistribution State :=
  fun h r => FiniteDistribution.empiricalRow 1 (by omega)
    (fun _ : Fin 1 => data ((h, r), ⟨0, hK⟩))

noncomputable def mvpActualRankBatch {H K : ℕ}
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → (State × Action) → Fin (Nat.log2 K) → FiniteDistribution State :=
  fun h r j => MVPUniformSource.batchRow data j h r.1 r.2

/-- The actual data-dependent value table satisfies every dyadic source-slot
radius condition on the simultaneous value-family event. The condition is
then consumed without an assumed radius certificate by the rank aggregator. -/
theorem mvp_actualRankSlotRadiusCondition_of_valueEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hL : L = Real.log (1 / onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K))
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E L c₁ c₂)) :
    let rows := mvpActualRankRows hH initial fallback planner data
    let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
    mvp_rankSlotRadiusCondition rows K V
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
  change mvp_rankSlotRadiusCondition rows K V p q0 q1 qb d (H : ℝ) I
  intro j hj i hi
  let jf : Fin (Nat.log2 K) := ⟨j, hj⟩
  let ifin : Fin (2 * 2 ^ j) := ⟨i, hi⟩
  let ell : mvpUniformLevel K := ⟨j, hj⟩
  let test := mvpActualAdaptiveValueSlotTest hH E initial fallback planner data L c₁ c₂ jf ifin
  have hslot := mvpActualAdaptiveValueSlot_bound_of_quarterEvent
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
  have htest (h : Fin H) (r : State × Action) :
      test h r.1 r.2 = mvp_visitValueLookup (rows h) K r
        (2 * 2 ^ j + i) (V h) := by
    rfl
  have hsum :
      (∑ h : Fin H, ∑ r : State × Action,
        mvp_rankErrorAt (rows h) K r (V h) (p h r) (q0 h r) (q1 h r) (qb h r)
          (2 * 2 ^ j + i)) =
      ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((qb h (s, a) jf).expectation (test h s a) - (p h (s, a)).expectation (test h s a)) 0 := by
    calc
      _ = ∑ h : Fin H, ∑ r : State × Action,
          max ((qb h r jf).expectation (test h r.1 r.2) -
            (p h r).expectation (test h r.1 r.2)) 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro r hr
        change mvp_rankPositiveError K (p h r) (q0 h r) (q1 h r) (qb h r)
          (2 * 2 ^ j + i) (mvp_visitValueLookup (rows h) K r (2 * 2 ^ j + i) (V h)) = _
        rw [mvp_rankPositiveError_lookup_at_slot (rows h) K r (V h)
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
  have hrows (h : Fin H) : rows h = mvpActualAdaptiveStageRows hH initial fallback planner data h := rfl
  have hvalues (h : Fin H) : V h = mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h := rfl
  have hvar :
      (∑ h : Fin H, ∑ r : State × Action,
        (p h r).variance (mvp_visitValueLookup (rows h) K r
          (2 * 2 ^ j + i) (V h))) =
      ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        ((E h).transition s a).variance
          (mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
            L c₁ c₂ jf ifin h s a) := by
    simp [jf, ifin, p, hrows, hvalues, mvpActualRankTransition,
      mvpActualAdaptiveValueSlotTest, Fintype.sum_prod_type]
  rw [← hvar] at hslot
  convert hslot using 1 <;> simp [jf, ifin, test, p, qb, mvpActualRankTransition, hbatch,
    mvpActualAdaptiveValueSlotTest, ell, mvpUniformBatchSize, mvpBatchIndex,
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

/-- On the original-value event, the sum of actual rank errors is bounded by
the proved rank aggregation endpoint. -/
theorem mvp_actualRankLinearBound_of_valueEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E L c₁ c₂))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : L = Real.log (1 / onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K))
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let rows := mvpActualRankRows hH initial fallback planner data
    let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
    let p := mvpActualRankTransition E
    let q0 := mvpActualRankInitial E hH
    let q1 := mvpActualRankFirst (by omega) data
    let qb := mvpActualRankBatch data
    let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * Fintype.card (Fin H × (State × Action))) * L
    let T := ∑ h : Fin H, ∑ k : Fin K,
      (p h (rows h k.val)).variance (V h k)
    mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I := by
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
  let T := ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k)
  change mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I
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
    have hδp := mvp_correctedAllocation_domain_and_log δ (Fintype.card State)
      (Fintype.card Action) H K hδ hδ1 hstate haction hH (by omega)
    have hI' := mvp_sourceIota_ge_20000 (Fintype.card (Fin H × (State × Action))) K
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)
      hd hK hδp.1 hδp.2.1
    dsimp [I]
    rw [hL]
    nlinarith [hI']
  have hV : ∀ h k s, 0 ≤ V h k s ∧ V h k s ≤ (H : ℝ) := by
    intro h k s
    have hδp := mvp_correctedAllocation_domain_and_log δ (Fintype.card State)
      (Fintype.card Action) H K hδ hδ1 hstate haction hH (by omega)
    have harg : 1 < 1 / onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K := by
      apply (lt_div_iff₀ hδp.1).2
      nlinarith [hδp.2.1]
    letI : Nonempty Action := (E h).action_nonempty
    have hrange := onlineCappedBackwardAt_range (H : ℝ) L c₁ c₂ (by positivity)
      (by rw [hL]; exact le_of_lt (Real.log_pos harg))
      hc₁ hc₂ (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k)
      (h.val + 1)
    simpa [V, mvpActualRankValues] using hrange.1 s
  exact mvp_rankErrorTotal_linear_bound rows K hK V p q0 q1 qb (H : ℝ) I
    (by positivity) hI hV (mvp_actualRankSlotRadiusCondition_of_valueEvent
      hH hK E δ L c₁ c₂ initial fallback planner data hL hgood)

end StatisticalRL.OnlineRL
