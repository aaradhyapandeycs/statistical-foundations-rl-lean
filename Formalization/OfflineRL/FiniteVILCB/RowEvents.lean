import Formalization.OfflineRL.FiniteVILCB.Generic
import Formalization.OfflineRL.FiniteVILCB.IdealData
import Formalization.OfflineRL.BernsteinInfiniteFixedRow
import Formalization.Generative.FiniteHorizonEmpiricalContinuation

/-!
# Event E5: Bernstein bounds for every visited ideal row

Fix the trimmed counts `m` and the action tapes `α`. Under the next-state tape law, the ideal row
at `(h,s,a)` with `N = N^id_h(s,a) > 0` is the empirical row of the first `N` cells of the tape at
`(h,s,a)`, and the ideal `V̂_{h+1}` is a function of the tapes at stages `> h` only. Lemma 6.18
(`bernsteinInfinite_fixedRow`, applied to `V̂_{h+1}/H` with `γ = 0`) gives the row event with
probability `> 1 - 8δ'`; a union bound over the visited triples follows.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance rowDecS : DecidableEq S := Classical.decEq S
noncomputable local instance rowDecA : DecidableEq A := Classical.decEq A
local instance rowMS : MeasurableSpace S := ⊤
local instance rowMRow : MeasurableSpace (FiniteDistribution S) := ⊤

theorem FiniteDistribution.ext_prob {d d' : FiniteDistribution S} (h : d.prob = d'.prob) :
    d = d' :=
  FiniteDistribution.ext h

theorem expectation_div_const (d : FiniteDistribution S) (V : S → ℝ) (c : ℝ) :
    d.expectation (fun t ↦ V t / c) = d.expectation V / c := by
  simp only [FiniteDistribution.expectation, Finset.sum_div, mul_div_assoc]

theorem variance_div_const (d : FiniteDistribution S) (V : S → ℝ) (c : ℝ) :
    d.variance (fun t ↦ V t / c) = d.variance V / c ^ 2 := by
  unfold FiniteDistribution.variance
  rw [sub_div, ← expectation_div_const d (fun t ↦ V t ^ 2), expectation_div_const]
  congr 1
  · congr 1
    funext t
    ring
  · ring

section Ideal

variable {H n : ℕ}

/-- Ideal empirical rows. -/
noncomputable def idealRow (m : Fin H → S → ℕ) (α : ActTape S A H n) (β : NxtTape S A H n)
    (h : Fin H) (s : S) (a : A) : FiniteDistribution S :=
  normRow (idealNext m α β h s a)

/-- Ideal VI-LCB values. -/
noncomputable def idealV (cb ι : ℝ) (r : Fin H → S → A → ℝ) (m : Fin H → S → ℕ)
    (α : ActTape S A H n) (β : NxtTape S A H n) : ℕ → S → ℝ :=
  vhatGen cb ι r (idealCount m α) (idealRow m α β)

/-- The scaled row event used by the deterministic analysis. -/
def RowGood (H : ℕ) (L : ℝ) (N : ℕ) (q P : FiniteDistribution S) (V : S → ℝ) : Prop :=
  |q.expectation V - P.expectation V| ≤ Real.sqrt (4 * q.variance V * L / N) + 5 * H * L / N ∧
    q.variance V ≤ 2 * P.variance V + 5 * (H : ℝ) ^ 2 * L / (3 * N)

theorem idealCount_le (m : Fin H → S → ℕ) (α : ActTape S A H n) (h : Fin H) (s : S) (a : A) :
    idealCount m α h s a ≤ n := by
  unfold idealCount
  exact (Finset.card_le_univ _).trans (by simp)

theorem card_fin_lt {N : ℕ} (hN : N ≤ n) (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : Fin n ↦ i.val < N ∧ P i)).card =
      (Finset.univ.filter (fun i : Fin N ↦ P (Fin.castLE hN i))).card := by
  symm
  refine Finset.card_bij (fun i _ ↦ Fin.castLE hN i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨by simp, hi⟩
  · intro i _ i' _ he
    exact Fin.castLE_injective hN he
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k.val, hk.1⟩, by simpa using hk.2, rfl⟩

/-- First `N` cells of the next-state tape at `(h,s,a)`. -/
def tapeDraw {N : ℕ} (hN : N ≤ n) (h : Fin H) (s : S) (a : A) (β : NxtTape S A H n) :
    Fin N → S :=
  fun i ↦ β ((h, s, a), Fin.castLE hN i)

theorem idealRow_eq_empiricalRow (m : Fin H → S → ℕ) (α : ActTape S A H n) (β : NxtTape S A H n)
    (h : Fin H) (s : S) (a : A) (hpos : 0 < idealCount m α h s a) :
    idealRow m α β h s a = FiniteDistribution.empiricalRow (idealCount m α h s a) hpos
      (tapeDraw (idealCount_le m α h s a) h s a β) := by
  classical
  set N := idealCount m α h s a with hNdef
  have hN : N ≤ n := idealCount_le m α h s a
  have hcnt : ∀ s', idealNext m α β h s a s' =
      (Finset.univ.filter (fun i : Fin N ↦ tapeDraw hN h s a β i = s')).card := by
    intro s'
    unfold idealNext
    rw [← hNdef]
    rw [card_fin_lt hN (fun i ↦ β ((h, s, a), i) = s')]
    rfl
  have hsum : (∑ t, idealNext m α β h s a t) = N := by
    simp_rw [hcnt]
    rw [← Finset.card_eq_sum_card_fiberwise (f := tapeDraw hN h s a β)
      (fun _ _ ↦ Finset.mem_univ _)]
    simp
  apply FiniteDistribution.ext_prob
  funext s'
  simp only [idealRow, normRow, FiniteDistribution.empiricalRow]
  rw [hsum, if_neg (by omega), hcnt s']
  rw [Finset.sum_boole]
  rw [div_eq_inv_mul]

end Ideal

end StatisticalRL.FiniteVILCB
