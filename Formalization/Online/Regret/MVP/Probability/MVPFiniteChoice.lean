import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! Enumerate every member of a sample-dependent finite family with a fixed
finite choice index, padding unused indices with the family's zero member. -/
namespace StatisticalRL.OnlineRL

noncomputable def mvpFiniteChoice {α : Type*} (s : Finset α) (fallback : α)
    (B : ℕ) (i : Fin B) : α := by
  classical
  let e := Fintype.equivFin {x // x ∈ s}
  exact if h : i.val < s.card then (e.symm ⟨i.val, by simpa using h⟩).val else fallback

theorem mvpFiniteChoice_mem {α : Type*} (s : Finset α) (fallback : α)
    (hf : fallback ∈ s) (B : ℕ) (i : Fin B) : mvpFiniteChoice s fallback B i ∈ s := by
  classical
  unfold mvpFiniteChoice
  split
  · exact Subtype.property _
  · exact hf

theorem mvpFiniteChoice_surjective_on_family {α : Type*} (s : Finset α) (fallback : α)
    (B : ℕ) (hcard : s.card ≤ B) (x : α) (hx : x ∈ s) :
    ∃ i : Fin B, mvpFiniteChoice s fallback B i = x := by
  classical
  let e := Fintype.equivFin {x // x ∈ s}
  let j := e ⟨x,hx⟩
  have hj : j.val < s.card := by simpa using j.isLt
  let i : Fin B := ⟨j.val, lt_of_lt_of_le hj hcard⟩
  refine ⟨i, ?_⟩
  unfold mvpFiniteChoice
  simp only [dif_pos (show i.val < s.card from hj)]
  change (e.symm j).val = x
  simp [j]
end StatisticalRL.OnlineRL
