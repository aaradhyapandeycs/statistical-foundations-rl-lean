import Formalization.Online.Regret.MVP.OnlineMVPOperationalCounters
import Formalization.Online.Regret.MVP.OnlineMVPAllRowsBudget

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineMVP_stageTagged_count_eq_body {H : ℕ} {Row : Type*}
    [DecidableEq Row] (rowAt : ℕ → Fin H × Row) (h : Fin H) (k : ℕ) (hH : 0 < H)
    (r : Fin H × Row) (hr : r.1 = h)
    (hstage : ∀ j, j < k * H → (rowAt j).1.val = j % H) :
    onlineVisitCount rowAt (k * H) r =
      onlineVisitCount (fun e => (rowAt (e * H + h.val)).2) k r.2 := by
  classical
  rw [onlineVisitCount_stage_episode_eq rowAt h k hH r hr hstage]
  unfold onlineVisitCount
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases heK : e < k
  · simp only [heK, true_and]
    have hi : e * H + h.val < k * H := by
      calc
        _ < e * H + H := Nat.add_lt_add_left h.isLt _
        _ = (e+1) * H := by rw [Nat.succ_mul]
        _ ≤ k * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt heK)
    have htag : (rowAt (e * H + h.val)).1 = h := by
      apply Fin.ext
      rw [hstage _ hi]
      simp [Nat.add_mod, Nat.mod_eq_of_lt h.isLt]
    constructor
    · intro heq
      exact congrArg Prod.snd heq
    · intro heq
      apply Prod.ext
      · exact htag.trans hr.symm
      · exact heq
  · simp [heK]

/-- The actual per-transition counter fold satisfies the displayed source
count budget on every stage-tagged completed history, independent of how
its state/action rows were chosen. -/
theorem onlineMVP_operationalHistory_reciprocal_budget
    {H : ℕ} {Row Outcome : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Outcome] [DecidableEq Outcome]
    (K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (rowAt : ℕ → Fin H × Row) (nextAt : ℕ → Outcome)
    (hstage : ∀ j, j < K * H → (rowAt j).1.val = j % H) :
    (∑ h : Fin H, ∑ k : Fin K,
      (((max ((onlineMVPCountTablesRun rowAt nextAt (k.val * H)).stored
        (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤
      4 * (Fintype.card Row : ℝ) * H * (Real.log K / Real.log 2) := by
  classical
  have hstageBound : ∀ h : Fin H,
      (∑ k : Fin K,
        (((max ((onlineMVPCountTablesRun rowAt nextAt (k.val * H)).stored
          (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤
      (Fintype.card Row : ℝ) * (4 * (Real.log K / Real.log 2)) := by
    intro h
    let rows : ℕ → Row := fun e => (rowAt (e * H + h.val)).2
    have heq : (∑ k : Fin K,
        (((max ((onlineMVPCountTablesRun rowAt nextAt (k.val * H)).stored
          (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) =
        ∑ k : Fin K, onlineMVPStoredReciprocal (onlineVisitCount rows k.val (rows k.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      let r := rowAt (k.val * H + h.val)
      have hidx : k.val * H + h.val < K * H := by
        calc
          _ < k.val * H + H := Nat.add_lt_add_left h.isLt _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
      have hr : r.1 = h := by
        apply Fin.ext
        dsimp [r]
        rw [hstage _ hidx]
        simp [Nat.add_mod, Nat.mod_eq_of_lt h.isLt]
      have hprefix : ∀ j, j < k.val * H → (rowAt j).1.val = j % H := by
        intro j hj
        apply hstage j
        exact lt_of_lt_of_le hj (Nat.mul_le_mul_right H k.isLt.le)
      have hinv := (onlineMVPCountTablesRun_row_invariant rowAt nextAt (k.val * H) r).2.2
      have hcount := onlineMVP_stageTagged_count_eq_body rowAt h k.val hH r hr hprefix
      rw [hinv, hcount]
      rfl
    rw [heq]
    have hsum : (∑ k : Fin K, onlineMVPStoredReciprocal (onlineVisitCount rows k.val (rows k.val))) =
        ∑ k ∈ Finset.range K, onlineMVPStoredReciprocal (onlineVisitCount rows k (rows k)) := by
      rw [Finset.sum_range]
    rw [hsum]
    exact onlineMVP_allRows_reciprocal_le rows K hK
  calc
    _ ≤ ∑ _h : Fin H, ((Fintype.card Row : ℝ) * (4 * (Real.log K / Real.log 2))) :=
      Finset.sum_le_sum (fun h _ => hstageBound h)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
/-- Source S·A·H form for arbitrary realized state/action rows. The outcome
sequence is used only by the operational per-successor counter fold. -/
theorem onlineMVP_operationalHistory_sourceCountBudget
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (rowAt : ℕ → Fin H × (State × Action)) (nextAt : ℕ → State)
    (hstage : ∀ j, j < K * H → (rowAt j).1.val = j % H) :
    (∑ h : Fin H, ∑ k : Fin K,
      (((max ((onlineMVPCountTablesRun rowAt nextAt (k.val * H)).stored
        (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤
      4 * (Fintype.card State : ℝ) * Fintype.card Action * H * (Real.log K / Real.log 2) := by
  have h := onlineMVP_operationalHistory_reciprocal_budget K hH hK rowAt nextAt hstage
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h

end StatisticalRL.OnlineRL
