import Mathlib.Algebra.BigOperators.Field
import Formalization.ModelFree.QLearningFinitePinskerCoarsening

/-! Finite core for the Chapter 7 robust-TV duality development.

This general robust-RL module supplies the canonical source clip and finite
event-TV bridge. It reuses the existing finite half-L1 TV API. The source
strong-duality and optimizer results remain open goals for separate modules. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Canonical source clip `[V]α`, shared by the robust-TV proof modules. -/
noncomputable def tvClipAbove (V : State → ℝ) (α : ℝ) : State → ℝ :=
  fun s ↦ min (V s) α

theorem tvClipAbove_eq_min (V : State → ℝ) (α : ℝ) (s : State) :
    tvClipAbove V α s = min (V s) α := rfl

/-- Clipping preserves an attained minimum when α is above it. -/
theorem tvClipAbove_minimum (V : State → ℝ) (α vmin : ℝ)
    (hlower : ∀ s, vmin ≤ V s) (hattained : ∃ s, V s = vmin)
    (hα : vmin ≤ α) :
    (∀ s, vmin ≤ tvClipAbove V α s) ∧ ∃ s, tvClipAbove V α s = vmin := by
  constructor
  · intro s
    exact le_min (hlower s) hα
  · obtain ⟨s, hs⟩ := hattained
    exact ⟨s, by simp [tvClipAbove, hs, min_eq_left hα]⟩

/-- Signed mass discrepancy on an event of the finite state space. -/
def eventTVMassDifference (p q : State → ℝ) (A : Finset State) : ℝ :=
  (∑ s ∈ A, p s) - (∑ s ∈ A, q s)

/-- Finite maximum of the source's absolute event-mass discrepancy. Since the
state space is finite and discrete, `Finset State` indexes every measurable
event. -/
noncomputable def eventTV (p q : State → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun A : Finset State ↦ |eventTVMassDifference p q A|)

/-- The source's event-supremum TV is attained by the positive-excess cell and
equals the half-L1 value. The pair of clauses says exactly that every event
discrepancy is bounded by this value and one event attains it, hence it is the
supremum over all events in the finite discrete measurable space. -/
theorem eventTV_isMaximum
    (p q : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    (∀ A : Finset State,
      |eventTVMassDifference p q A| ≤
        StatisticalRL.QLearning.qFiniteTotalVariation p q) ∧
    ∃ A : Finset State,
      |eventTVMassDifference p q A| =
        StatisticalRL.QLearning.qFiniteTotalVariation p q := by
  classical
  let T := StatisticalRL.QLearning.qFiniteTotalVariation p q
  let E := StatisticalRL.QLearning.qFinitePositiveDifferenceCell p q
  let d : State → ℝ := fun s ↦ p s - q s
  have hdZero : ∑ s, d s = 0 := by
    simp [d, Finset.sum_sub_distrib, hp1, hq1]
  have hposPoint (s : State) :
      max (d s) 0 = (|d s| + d s) / 2 := by
    by_cases h : 0 ≤ d s
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · have h' : d s ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', abs_of_nonpos h']
      ring
  have hnegPoint (s : State) :
      max (-d s) 0 = (|d s| - d s) / 2 := by
    by_cases h : 0 ≤ -d s
    · have hd' : d s ≤ 0 := neg_nonneg.mp h
      rw [max_eq_left h, abs_of_nonpos hd']
      ring
    · have h' : -d s ≤ 0 := le_of_not_ge h
      have hd' : 0 ≤ d s := neg_nonpos.mp h'
      rw [max_eq_right h', abs_of_nonneg hd']
      ring
  have hpositivePart : (∑ s, max (d s) 0) = T := by
    calc
      (∑ s, max (d s) 0) = ∑ s, ((|d s| + d s) / 2) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hposPoint s
      _ = ((∑ s, |d s|) + ∑ s, d s) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ = T := by
        rw [hdZero]
        dsimp [T, StatisticalRL.QLearning.qFiniteTotalVariation, d]
        ring
  have hnegativePart : (∑ s, max (-d s) 0) = T := by
    calc
      (∑ s, max (-d s) 0) = ∑ s, ((|d s| - d s) / 2) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hnegPoint s
      _ = ((∑ s, |d s|) - ∑ s, d s) / 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
      _ = T := by
        rw [hdZero]
        dsimp [T, StatisticalRL.QLearning.qFiniteTotalVariation, d]
        ring
  have hsumPos (A : Finset State) :
      (∑ s ∈ A, d s) ≤ T := by
    calc
      (∑ s ∈ A, d s) ≤ ∑ s ∈ A, max (d s) 0 :=
        Finset.sum_le_sum fun s _ ↦ le_max_left _ _
      _ ≤ ∑ s, max (d s) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun s _ _ ↦ le_max_right _ _)
      _ = T := hpositivePart
  have hsumNeg (A : Finset State) :
      (∑ s ∈ A, -d s) ≤ T := by
    calc
      (∑ s ∈ A, -d s) ≤ ∑ s ∈ A, max (-d s) 0 :=
        Finset.sum_le_sum fun s _ ↦ le_max_left _ _
      _ ≤ ∑ s, max (-d s) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun s _ _ ↦ le_max_right _ _)
      _ = T := hnegativePart
  have heventSum (A : Finset State) :
      eventTVMassDifference p q A = ∑ s ∈ A, d s := by
    dsimp [eventTVMassDifference]
    calc
      (∑ s ∈ A, p s) - (∑ s ∈ A, q s) = ∑ s ∈ A, (p s - q s) :=
        (Finset.sum_sub_distrib ..).symm
      _ = ∑ s ∈ A, d s := by
        apply Finset.sum_congr rfl
        intro s hs
        rfl
  have hbound : ∀ A : Finset State, |eventTVMassDifference p q A| ≤ T := by
    intro A
    have hup := hsumPos A
    have hlo := hsumNeg A
    have hsumNegEq : (∑ s ∈ A, -d s) = - (∑ s ∈ A, d s) :=
      Finset.sum_neg_distrib ..
    rw [hsumNegEq] at hlo
    have hlow : -T ≤ ∑ s ∈ A, d s := by linarith
    rw [heventSum A]
    rw [abs_le]
    exact ⟨hlow, hup⟩
  have hTnonneg : 0 ≤ T := by
    dsimp [T, StatisticalRL.QLearning.qFiniteTotalVariation]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ ↦ abs_nonneg _)
  have hEvalue : eventTVMassDifference p q E = T := by
    have h := StatisticalRL.QLearning.qFiniteTotalVariation_eq_positiveCell
      p q hp hq hp1 hq1
    dsimp [T, E, eventTVMassDifference,
      StatisticalRL.QLearning.qFinitePositiveDifferenceCell] at h ⊢
    exact h.symm
  refine ⟨hbound, ⟨E, ?_⟩⟩
  rw [hEvalue, abs_of_nonneg hTnonneg]

/-- Exact finite event-supremum/half-L1 identity in the source TV
normalization. -/
theorem eventTV_eq_finiteTotalVariation
    (p q : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    eventTV p q =
      StatisticalRL.QLearning.qFiniteTotalVariation p q := by
  classical
  obtain ⟨hbound, ⟨A, hA⟩⟩ := eventTV_isMaximum p q hp hq hp1 hq1
  unfold eventTV
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ fun A _ ↦ hbound A
  · rw [← hA]
    exact Finset.le_sup'
      (f := fun B : Finset State ↦ |eventTVMassDifference p q B|)
      (Finset.mem_univ A)

end StatisticalRL.RobustRL
