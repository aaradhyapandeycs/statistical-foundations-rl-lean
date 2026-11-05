import Mathlib

/-! Rank and pair-count identities for the source offline sample split.

The statements retain the actual sample and do not assume a count lower bound
or a transition-model certificate. -/

namespace StatisticalRL.OfflineRL.RankedPair

variable {Row : Type*} [DecidableEq Row] {n : ℕ}

/-- Number of indices `j` with `j < m` (as naturals) whose label is `r`: the
visit count of `r` in the length-`m` prefix. -/
def prefixVisitCount (l : Fin n → Row) (m : ℕ) (r : Row) : ℕ :=
  (Finset.univ.filter fun j : Fin n => j.val < m ∧ l j = r).card

/-- Strict-past visits of index `i`: earlier indices with the same label. -/
def pastVisits (l : Fin n → Row) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n => j.val < i.val ∧ l j = l i

/-- Strict-past visit rank of `i`. -/
def visitRank (l : Fin n → Row) (i : Fin n) : ℕ :=
  (pastVisits l i).card

/-- Exact cardinality identity: the rank of `i` is the visit count of its own
label in the prefix strictly before `i`. -/
theorem visitRank_eq_prefixVisitCount (l : Fin n → Row) (i : Fin n) :
    visitRank l i = prefixVisitCount l i.val (l i) := rfl

/-- The rank is at most the position. -/
theorem visitRank_le_val (l : Fin n → Row) (i : Fin n) : visitRank l i ≤ i.val := by
  have hsub : pastVisits l i ⊆ Finset.Iio i := by
    intro j hj
    simp only [pastVisits, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Iio.2 (Fin.lt_def.2 hj.1)
  calc visitRank l i ≤ (Finset.Iio i).card := Finset.card_le_card hsub
    _ = i.val := Fin.card_Iio i

/-- The rank is below `n`. -/
theorem visitRank_lt (l : Fin n → Row) (i : Fin n) : visitRank l i < n :=
  lt_of_le_of_lt (visitRank_le_val l i) i.isLt

/-- The rank as an element of `Fin n`. -/
def visitRankFin (l : Fin n → Row) (i : Fin n) : Fin n :=
  ⟨visitRank l i, visitRank_lt l i⟩

/-- Ranks of equally-labelled indices are strictly increasing in position. -/
theorem visitRank_lt_of_lt (l : Fin n → Row) {i k : Fin n} (hik : i.val < k.val)
    (hl : l i = l k) : visitRank l i < visitRank l k := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, ?_, ?_⟩
  · intro j hj
    simp only [pastVisits, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨lt_trans hj.1 hik, hj.2.trans hl⟩
  · simp only [pastVisits, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hik, hl⟩
  · simp [pastVisits]

/-- The ranked pair `i ↦ (l i, rank i)` is injective. -/
theorem rankedPair_injective (l : Fin n → Row) :
    Function.Injective fun i : Fin n => (l i, visitRank l i) := by
  intro i k h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hl, hr⟩ := h
  rcases lt_trichotomy i.val k.val with hlt | heq | hgt
  · exact absurd hr (visitRank_lt_of_lt l hlt hl).ne
  · exact Fin.ext heq
  · exact absurd hr (visitRank_lt_of_lt l hgt hl.symm).ne'

/-- `Fin n`-valued form of the injection. -/
theorem rankedPairFin_injective (l : Fin n → Row) :
    Function.Injective fun i : Fin n => (l i, visitRankFin l i) := by
  intro i k h
  apply rankedPair_injective l
  simp only [Prod.mk.injEq, visitRankFin, Fin.mk.injEq] at h ⊢
  exact h

end StatisticalRL.OfflineRL.RankedPair
