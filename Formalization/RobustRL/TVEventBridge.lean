import Mathlib.Algebra.BigOperators.Field
import Formalization.ModelFree.QLearningFinitePinskerCoarsening
import Formalization.RobustRL.TVCore

/-! TV proof source bridge for finite event-TV. Reuses the
landed finite half-L1 positive-cell identity, and proves that its value is the
attained maximum of event-mass discrepancies on a finite discrete carrier.
No support-inclusion premise is used: atoms of mass zero and equality atoms
are included in the argument without division. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Event

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Signed mass discrepancy on an event of the finite state space; the canonical definition is
`RobustRL.eventTVMassDifference`. -/
def eventMassDifference (p q : State → ℝ) (A : Finset State) : ℝ :=
  RobustRL.eventTVMassDifference p q A

/-- Finite maximum of the source's absolute event-mass discrepancy. Since the
state space is finite and discrete, `Finset State` indexes every measurable
event. -/
noncomputable def qFiniteEventTV (p q : State → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun A : Finset State ↦ |eventMassDifference p q A|)

/-- The source's event-supremum TV is attained by the positive-excess cell and
equals the half-L1 value. The pair of clauses says exactly that every event
discrepancy is bounded by this value and one event attains it, hence it is the
supremum over all events in the finite discrete measurable space. -/
theorem qFiniteEventTV_isMaximum
    (p q : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    (∀ A : Finset State,
      |eventMassDifference p q A| ≤
        StatisticalRL.QLearning.qFiniteTotalVariation p q) ∧
    ∃ A : Finset State,
      |eventMassDifference p q A| =
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
      eventMassDifference p q A = ∑ s ∈ A, d s := by
    dsimp [eventMassDifference]
    calc
      (∑ s ∈ A, p s) - (∑ s ∈ A, q s) = ∑ s ∈ A, (p s - q s) :=
        (Finset.sum_sub_distrib ..).symm
      _ = ∑ s ∈ A, d s := by
        apply Finset.sum_congr rfl
        intro s hs
        rfl
  have hbound : ∀ A : Finset State, |eventMassDifference p q A| ≤ T := by
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
  have hEvalue : eventMassDifference p q E = T := by
    have h := StatisticalRL.QLearning.qFiniteTotalVariation_eq_positiveCell
      p q hp hq hp1 hq1
    dsimp [T, E, eventMassDifference,
      StatisticalRL.QLearning.qFinitePositiveDifferenceCell] at h ⊢
    exact h.symm
  refine ⟨hbound, ⟨E, ?_⟩⟩
  rw [hEvalue, abs_of_nonneg hTnonneg]

/-- Exact finite event-supremum/half-L1 identity in the source TV
normalization. -/
theorem qFiniteEventTV_eq_halfL1
    (p q : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    qFiniteEventTV p q =
      StatisticalRL.QLearning.qFiniteTotalVariation p q := by
  classical
  obtain ⟨hbound, ⟨A, hA⟩⟩ := qFiniteEventTV_isMaximum p q hp hq hp1 hq1
  unfold qFiniteEventTV
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ fun A _ ↦ hbound A
  · rw [← hA]
    exact Finset.le_sup'
      (f := fun B : Finset State ↦ |eventMassDifference p q B|)
      (Finset.mem_univ A)

end StatisticalRL.RobustRL.TVProof.Event
