import Formalization.OfflineRL.FiniteVILCB.Definitions
import Formalization.Generative.FiniteHorizonSamplingDefinitions

/-!
# Tape construction (analysis only)

Main trajectories built from independent action tapes and next-state tapes, the joined dataset,
and the ideal counts read from the first tape cells. These objects appear only in the proof of
Theorem 6.16 (restricted), never in the algorithm or the statement.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]

noncomputable local instance tapeDefDecS : DecidableEq S := Classical.decEq S
noncomputable local instance tapeDefDecA : DecidableEq A := Classical.decEq A

/-! ## Tapes (analysis only) -/

section Tapes

variable {H n : ℕ}

/-- Action tape cells `(h, s, j) ↦ A`. -/
abbrev ActTape (S A : Type*) (H n : ℕ) := Fin H × S × Fin n → A

/-- Next-state tapes: the finite-horizon generative sample array `((h,s,a), i) ↦ S`. -/
abbrev NxtTape (S A : Type*) (H n : ℕ) := FiniteHorizonGenerative.Samples S A H n

open Classical in
/-- Rank of `k` among the `k' < k` with `p k'`, as an element of `Fin n`. -/
noncomputable def rankFin (p : Fin n → Prop) (k : Fin n) : Fin n :=
  ⟨(Finset.univ.filter (fun k' : Fin n ↦ k' < k ∧ p k')).card, by
    classical
    calc (Finset.univ.filter (fun k' : Fin n ↦ k' < k ∧ p k')).card
        ≤ (Finset.univ.filter (fun k' : Fin n ↦ k' < k)).card :=
          Finset.card_le_card (Finset.monotone_filter_right _ (fun _ _ h ↦ h.1))
      _ = k.val := by rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
      _ < n := k.isLt⟩

/-- Actions of all main trajectories at stage `h` from their states `x`. -/
noncomputable def actVec (α : ActTape S A H n) (h : Fin H) (x : Fin n → S) (k : Fin n) : A :=
  α (h, x k, rankFin (fun k' ↦ x k' = x k) k)

/-- Next states of all main trajectories at stage `h`. -/
noncomputable def nxtVec (α : ActTape S A H n) (β : NxtTape S A H n) (h : Fin H) (x : Fin n → S)
    (k : Fin n) : S :=
  β ((h, x k, actVec α h x k),
    rankFin (fun k' ↦ x k' = x k ∧ actVec α h x k' = actVec α h x k) k)

/-- State vector of the main trajectories at stage `h` (stage-synchronous build). -/
noncomputable def stateVec (ι₀ : Fin n → S) (α : ActTape S A H n) (β : NxtTape S A H n) :
    ℕ → Fin n → S
  | 0 => ι₀
  | h + 1 => if hh : h < H then nxtVec α β ⟨h, hh⟩ (stateVec ι₀ α β h) else stateVec ι₀ α β h

/-- The main trajectories built from the tapes. -/
noncomputable def buildMain (ι₀ : Fin n → S) (α : ActTape S A H n) (β : NxtTape S A H n) :
    Fin n → Traj S A H :=
  fun k ↦ (fun i ↦ stateVec ι₀ α β i.val k,
    fun h ↦ actVec α h (stateVec ι₀ α β h.val) k)

/-- Joining auxiliary and main trajectories into one dataset of size `K`. -/
def joinData {K : ℕ} (aux : Fin (K / 2) → Traj S A H) (main : Fin (K - K / 2) → Traj S A H) :
    Fin K → Traj S A H :=
  fun k ↦ if hk : k.val < K / 2 then aux ⟨k.val, hk⟩ else main ⟨k.val - K / 2, by omega⟩

/-- Ideal counts `N^id_h(s,a) = #{j < m_h(s) : α(h,s,j) = a}`. -/
noncomputable def idealCount (m : Fin H → S → ℕ) (α : ActTape S A H n) (h : Fin H) (s : S)
    (a : A) : ℕ :=
  (Finset.univ.filter (fun j : Fin n ↦ j.val < m h s ∧ α (h, s, j) = a)).card

/-- Ideal next-state counts: the first `N^id_h(s,a)` cells of the next-state tape. -/
noncomputable def idealNext (m : Fin H → S → ℕ) (α : ActTape S A H n) (β : NxtTape S A H n)
    (h : Fin H) (s : S) (a : A) (s' : S) : ℕ :=
  (Finset.univ.filter (fun i : Fin n ↦ i.val < idealCount m α h s a ∧ β ((h, s, a), i) = s')).card

end Tapes

end StatisticalRL.FiniteVILCB
