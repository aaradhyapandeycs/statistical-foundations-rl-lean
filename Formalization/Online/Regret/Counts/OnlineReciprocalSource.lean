import Formalization.Online.Regret.Counts.OnlineReciprocalSourceDefinitions
import Formalization.Online.Regret.T2.OnlineT2SharpLog
import Formalization.Online.Regret.W1.OnlineW1ActualRowRank
import Mathlib.NumberTheory.Harmonic.Bounds

namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- The zero-indexed rank profile is exactly one first-visit term plus the
harmonic sum over the remaining visits. -/
theorem onlineReciprocal_maxOne_rank_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, onlineReciprocalMaxOneCount n) =
      if N = 0 then 0 else 1 + (harmonic (N - 1) : ℝ) := by
  cases N with
  | zero => simp [onlineReciprocalMaxOneCount]
  | succ m =>
      have hshift :
          (∑ n ∈ Finset.range m, onlineReciprocalMaxOneCount (n + 1)) =
            (harmonic m : ℝ) := by
        calc
          _ = ∑ n ∈ Finset.range m, (((n + 1 : ℕ) : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [onlineReciprocalMaxOneCount]
          _ = _ := by
            simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      calc
        _ = (∑ n ∈ Finset.range m, onlineReciprocalMaxOneCount (n + 1)) +
            onlineReciprocalMaxOneCount 0 :=
          Finset.sum_range_succ' _ _
        _ = 1 + (harmonic m : ℝ) := by
          rw [hshift]
          simp [onlineReciprocalMaxOneCount, add_comm]

/-- Scalar comparison needed after the exact first-visit/harmonic decomposition. -/
theorem onlineReciprocal_two_add_log_pred_le_twice_log₂ (K : ℕ) (hK : 2 ≤ K) :
    2 + Real.log (K - 1 : ℝ) ≤ 2 * (Real.log K / Real.log 2) := by
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hKm1pos : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htwole : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hKlog : Real.log 2 ≤ Real.log K :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKreal
  have hratio : (K : ℝ) - 1 ≤ ((K : ℝ) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((K : ℝ) - 2)]
  have hlogratio := Real.log_le_log hKm1pos hratio
  have hlogdiv : Real.log ((K : ℝ) / 2) = Real.log K - Real.log 2 := by
    rw [Real.log_div hKpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_pow, hlogdiv] at hlogratio
  rw [← mul_div_assoc]
  apply (le_div_iff₀ htwo).2
  have hlogmul := mul_le_mul_of_nonneg_right hlogratio (le_of_lt htwo)
  have hprod := mul_nonneg (sub_nonneg.mpr htwole) (sub_nonneg.mpr hKlog)
  have hstep₁ :
      (2 + Real.log (K - 1 : ℝ)) * Real.log 2 ≤
        2 * Real.log 2 + 2 * (Real.log K - Real.log 2) * Real.log 2 := by
    calc
      _ = Real.log (K - 1 : ℝ) * Real.log 2 + 2 * Real.log 2 := by ring
      _ ≤ 2 * (Real.log K - Real.log 2) * Real.log 2 + 2 * Real.log 2 :=
        add_le_add_left hlogmul (2 * Real.log 2)
      _ = 2 * Real.log 2 + 2 * (Real.log K - Real.log 2) * Real.log 2 := by ring
  have hstep₂ :
      2 * Real.log 2 + 2 * (Real.log K - Real.log 2) * Real.log 2 ≤
        2 * Real.log K := by
    nlinarith [hprod]
  exact hstep₁.trans hstep₂

/-- Positive-indexed max-one reciprocals for a fixed row have the source's
factor-two logarithmic budget, including the first-visit unit term. -/
theorem onlineVisitCount_maxOne_row_le {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (hK : 2 ≤ K) (r : Row) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r then
        onlineReciprocalMaxOneCount (onlineVisitCount rowAt j r)
      else 0) ≤ 2 * (Real.log K / Real.log 2) := by
  classical
  rw [onlineVisitCount_sum_by_rank rowAt K r onlineReciprocalMaxOneCount]
  let N := onlineVisitCount rowAt K r
  change (∑ n ∈ Finset.range N, onlineReciprocalMaxOneCount n) ≤ _
  rw [onlineReciprocal_maxOne_rank_sum]
  have hNle : N ≤ K := by
    dsimp [N]
    unfold onlineVisitCount
    have hc := Finset.card_filter_le (Finset.range K) (fun j => rowAt j = r)
    simp only [Finset.card_range] at hc
    convert hc using 2 <;> ext j <;> simp
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKlog : Real.log 2 ≤ Real.log K := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast hK
  have hlogKnonneg : 0 ≤ Real.log K := le_trans (le_of_lt htwo) hKlog
  have hratio_nonneg : 0 ≤ Real.log K / Real.log 2 :=
    div_nonneg hlogKnonneg (le_of_lt htwo)
  have hratio_ge_one : 1 ≤ Real.log K / Real.log 2 :=
    (le_div_iff₀ htwo).2 (by simpa using hKlog)
  by_cases hNzero : N = 0
  · rw [if_pos hNzero]
    exact mul_nonneg (by norm_num) hratio_nonneg
  · simp only [if_neg hNzero]
    have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
    by_cases hNone : N = 1
    · rw [hNone]
      simp
      linarith
    · have hNge2 : 2 ≤ N := by omega
      have hharm := harmonic_le_one_add_log (N - 1)
      have hNsubposNat : 0 < N - 1 := by omega
      have hNsubpos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hNsubposNat
      have hNsubleKsubNat : N - 1 ≤ K - 1 := Nat.sub_le_sub_right hNle 1
      have hNsubleKsub : ((N - 1 : ℕ) : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
        exact_mod_cast hNsubleKsubNat
      have hlogmono := Real.log_le_log hNsubpos hNsubleKsub
      have hKsubcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
      have hlogmono' : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log ((K : ℝ) - 1) := by
        rw [← hKsubcast]
        exact hlogmono
      have hbound : 1 + (harmonic (N - 1) : ℝ) ≤ 2 + Real.log (K - 1 : ℝ) := by
        have hharm' : (harmonic (N - 1) : ℝ) ≤
            1 + Real.log ((N - 1 : ℕ) : ℝ) := hharm
        linarith
      exact hbound.trans (onlineReciprocal_two_add_log_pred_le_twice_log₂ K hK)

/-- Finite-row aggregation of the exact max-one count charge. -/
theorem onlineVisitCount_allRows_maxOne_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (hK : 2 ≤ K) :
    (∑ j ∈ Finset.range K,
      onlineReciprocalMaxOneCount (onlineVisitCount rowAt j (rowAt j))) ≤
      (Fintype.card Row : ℝ) * (2 * (Real.log K / Real.log 2)) := by
  classical
  have heq :
      (∑ j ∈ Finset.range K,
        onlineReciprocalMaxOneCount (onlineVisitCount rowAt j (rowAt j))) =
      ∑ r : Row, ∑ j ∈ Finset.range K,
        if rowAt j = r then
          onlineReciprocalMaxOneCount (onlineVisitCount rowAt j r)
        else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [heq]
  calc
    _ ≤ ∑ _r : Row, (2 * (Real.log K / Real.log 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact onlineVisitCount_maxOne_row_le rowAt K hK r
    _ = _ := by simp

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance reciprocalSourceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance reciprocalSourceActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Actual sequential-path version of the printed Lemma 5.3 sum. The only
count bridge is the source strict-past observed-row count identity. -/
theorem onlineSequential_maxOne_reciprocal_count_budget
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      onlineReciprocalMaxOneCount
        ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length)) ≤
      2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H *
        (Real.log K / Real.log 2) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  change (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      onlineReciprocalMaxOneCount
        ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length)) ≤ _
  have hstage : ∀ h : Fin H, (∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      onlineReciprocalMaxOneCount
        ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length)) ≤
      (Fintype.card (State × Action) : ℝ) *
        (2 * (Real.log K / Real.log 2)) := by
    intro h
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    have hcount : ∀ k : Fin K,
        (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length =
          onlineVisitCount rows k.val (rows k.val) := by
      intro k
      exact onlineSequential_playedRow_count_eq_rank H K hH E initial fallback planner path k h
    have hreplace :
        (∑ k : Fin K,
          onlineReciprocalMaxOneCount
            ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length)) =
        ∑ k : Fin K, onlineReciprocalMaxOneCount
          (onlineVisitCount rows k.val (rows k.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcount k]
    rw [hreplace]
    have hsum :
        (∑ k : Fin K, onlineReciprocalMaxOneCount
          (onlineVisitCount rows k.val (rows k.val))) =
          ∑ j ∈ Finset.range K,
            onlineReciprocalMaxOneCount (onlineVisitCount rows j (rows j)) := by
      apply Finset.sum_bij (fun k _ => k.val)
      · intro k hk
        exact Finset.mem_range.mpr k.isLt
      · intro k hk l hl he
        exact Fin.ext he
      · intro j hj
        exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
      · intro k hk
        rfl
    rw [hsum]
    exact onlineVisitCount_allRows_maxOne_le rows K hK
  calc
    _ ≤ ∑ _h : Fin H,
        ((Fintype.card (State × Action) : ℝ) * (2 * (Real.log K / Real.log 2))) :=
      Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp [Fintype.card_prod]; ring

end StatisticalRL.OnlineRL
