import Formalization.OfflineRL.FiniteVILCB.TapeLaw

/-!
# Kept data equal ideal tape data on the trimming event

For the dataset `joinData aux (buildMain ι₀ α β)`, if every trimmed count `m_h(s)` (a function of
the auxiliary half only) is at most the number of main visits to `(h,s)` (event `E`), then the
kept counts and kept next-state counts equal the ideal counts read from the first cells of the
tapes. The tool is a rank bijection: visit ranks map a down-closed set of visits onto an initial
segment of tape cells.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]
set_option linter.unusedSectionVars false

noncomputable local instance idealDecS : DecidableEq S := Classical.decEq S
noncomputable local instance idealDecA : DecidableEq A := Classical.decEq A

section Rank

variable {n : ℕ}

open Classical in
theorem rankFin_val (p : Fin n → Prop) (k : Fin n) :
    (rankFin p k).val = (Finset.univ.filter (fun k' : Fin n ↦ k' < k ∧ p k')).card := rfl

theorem rankFin_lt_of_lt (p : Fin n → Prop) {k k' : Fin n} (hk : p k) (hlt : k < k') :
    (rankFin p k).val < (rankFin p k').val := by
  classical
  rw [rankFin_val, rankFin_val]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, hk⟩
    · simp
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1.trans hlt, hj.2⟩

/-- Visit ranks map a down-closed set of visits onto an initial segment of cells. -/
theorem card_filter_rank (T U : Finset (Fin n)) (p : Fin n → Prop) (hp : ∀ j, p j ↔ j ∈ T)
    (hU : U ⊆ T)
    (hdown : ∀ k ∈ U, ∀ k' ∈ T, k' < k → k' ∈ U) (F : Fin n → Prop) [DecidablePred F] :
    (U.filter (fun k ↦ F (rankFin p k))).card =
      (Finset.univ.filter (fun i : Fin n ↦ i.val < U.card ∧ F i)).card := by
  classical
  obtain rfl : p = (· ∈ T) := funext fun j ↦ propext (hp j)
  set r : Fin n → Fin n := fun k ↦ rankFin (· ∈ T) k with hr
  have hinj : Set.InjOn r U := by
    intro k hk k' hk' he
    rcases lt_trichotomy k k' with h | h | h
    · exact absurd (congrArg Fin.val he) (ne_of_lt (rankFin_lt_of_lt (· ∈ T) (hU hk) h))
    · exact h
    · exact absurd (congrArg Fin.val he) (ne_of_gt (rankFin_lt_of_lt (· ∈ T) (hU hk') h))
  have hlt : ∀ k ∈ U, (r k).val < U.card := by
    intro k hk
    simp only [hr]
    rw [rankFin_val]
    refine lt_of_le_of_lt (Finset.card_le_card (t := U.erase k) ?_) (Finset.card_erase_lt_of_mem hk)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.mpr ⟨ne_of_lt hj.1, hdown k hk j hj.2 hj.1⟩
  have himg : U.image r = Finset.univ.filter (fun i : Fin n ↦ i.val < U.card) := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt k hk
    · rw [Finset.card_image_of_injOn hinj]
      have hcard : U.card ≤ n := by simpa using Finset.card_le_univ U
      calc (Finset.univ.filter (fun i : Fin n ↦ i.val < U.card)).card
          = (Finset.univ.map Fin.valEmbedding |>.filter (· < U.card)).card := by
            rw [Finset.filter_map, Finset.card_map]
            rfl
        _ ≤ (Finset.range U.card).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter] at hi
            exact Finset.mem_range.mpr hi.2
        _ = U.card := Finset.card_range _
  have h1 : (U.filter (fun k ↦ F (r k))).card = ((U.image r).filter F).card := by
    rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
  show (U.filter (fun k ↦ F (r k))).card = _
  rw [h1, himg, Finset.filter_filter]

end Rank

section Join

variable {H K : ℕ}

/-- Global index of main trajectory `j`. -/
def mainIdx (j : Fin (K - K / 2)) : Fin K := ⟨K / 2 + j.val, by omega⟩

theorem mainIdx_lt_iff (j j' : Fin (K - K / 2)) : mainIdx j' < mainIdx j ↔ j' < j := by
  rw [Fin.lt_def, Fin.lt_def]
  simp [mainIdx]

theorem card_main_filter (P : Fin K → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun k : Fin K ↦ K / 2 ≤ k.val ∧ P k)).card =
      (Finset.univ.filter (fun j : Fin (K - K / 2) ↦ P (mainIdx j))).card := by
  symm
  refine Finset.card_bij (fun j _ ↦ mainIdx j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨by simp [mainIdx], hj⟩
  · intro j _ j' _ he
    have := congrArg Fin.val he
    simp only [mainIdx] at this
    exact Fin.ext (by omega)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨⟨k.val - K / 2, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : mainIdx (K := K) ⟨k.val - K / 2, by omega⟩ = k := Fin.ext (by simp [mainIdx]; omega)
      rw [this]
      exact hk.2
    · exact Fin.ext (by simp [mainIdx]; omega)

theorem card_aux_filter (P : Fin K → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun k : Fin K ↦ k.val < K / 2 ∧ P k)).card =
      (Finset.univ.filter (fun i : Fin (K / 2) ↦ P ⟨i.val, by omega⟩)).card := by
  symm
  refine Finset.card_bij (fun i _ ↦ (⟨i.val, by omega⟩ : Fin K)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro i _ i' _ he
    exact Fin.ext (by simpa using congrArg Fin.val he)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k.val, hk.1⟩, by simpa using hk.2, rfl⟩

theorem joinData_mainIdx (aux : Fin (K / 2) → Traj S A H) (main : Fin (K - K / 2) → Traj S A H)
    (j : Fin (K - K / 2)) : joinData aux main (mainIdx j) = main j := by
  simp only [joinData, mainIdx]
  rw [dif_neg (by omega)]
  congr 1
  exact Fin.ext (by simp)

theorem joinData_aux (aux : Fin (K / 2) → Traj S A H) (main : Fin (K - K / 2) → Traj S A H)
    (i : Fin (K / 2)) : joinData aux main ⟨i.val, by omega⟩ = aux i := by
  simp only [joinData]
  rw [dif_pos i.isLt]

/-- Trimmed counts computed from the auxiliary trajectories alone. -/
noncomputable def auxTrim (ι : ℝ) (aux : Fin (K / 2) → Traj S A H) (h : Fin H) (s : S) : ℕ :=
  trim ι (Finset.univ.filter (fun i : Fin (K / 2) ↦ (aux i).1 h.castSucc = s)).card

theorem trimCount_joinData (ι : ℝ) (aux : Fin (K / 2) → Traj S A H)
    (main : Fin (K - K / 2) → Traj S A H) :
    trimCount ι (joinData aux main) = auxTrim ι aux := by
  funext h s
  unfold trimCount auxTrim auxCount
  rw [card_aux_filter]
  apply congrArg
  apply congrArg
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, stAt]
  rw [joinData_aux]

end Join

section Ideal

variable {H K : ℕ}

/-- The trimming event `E`: every trimmed count is at most the number of main visits. -/
def TrimEvent (m : Fin H → S → ℕ) (ι₀ : Fin (K - K / 2) → S) (α : ActTape S A H (K - K / 2))
    (β : NxtTape S A H (K - K / 2)) : Prop :=
  ∀ h s, m h s ≤ (Finset.univ.filter (fun j ↦ stateVec ι₀ α β h.val j = s)).card

theorem mainRank_joinData (aux : Fin (K / 2) → Traj S A H) (main : Fin (K - K / 2) → Traj S A H)
    (h : Fin H) (j : Fin (K - K / 2)) :
    mainRank (joinData aux main) h (mainIdx j) =
      (rankFin (· ∈ Finset.univ.filter (fun j' ↦ (main j').1 h.castSucc = (main j).1 h.castSucc))
        j).val := by
  classical
  unfold mainRank
  rw [card_main_filter, rankFin_val]
  congr 1
  ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, stAt, joinData_mainIdx, mainIdx_lt_iff]

/-- **Kept data equal ideal data on `E`.** -/
theorem kept_eq_ideal (ι : ℝ) (aux : Fin (K / 2) → Traj S A H) (ι₀ : Fin (K - K / 2) → S)
    (α : ActTape S A H (K - K / 2)) (β : NxtTape S A H (K - K / 2))
    (hE : TrimEvent (auxTrim ι aux) ι₀ α β) (h : Fin H) (s : S) (a : A) :
    keptCount (trimCount ι (joinData aux (buildMain ι₀ α β))) (joinData aux (buildMain ι₀ α β))
        h s a = idealCount (auxTrim ι aux) α h s a ∧
    ∀ s', keptNext (trimCount ι (joinData aux (buildMain ι₀ α β)))
        (joinData aux (buildMain ι₀ α β)) h s a s' = idealNext (auxTrim ι aux) α β h s a s' := by
  classical
  rw [trimCount_joinData]
  set m := auxTrim ι aux with hm
  set x : Fin (K - K / 2) → S := stateVec ι₀ α β h.val with hx
  set acts : Fin (K - K / 2) → A := actVec α h x with hacts
  have hst : ∀ j, (buildMain ι₀ α β j).1 h.castSucc = x j := fun j ↦ rfl
  have hac : ∀ j, (buildMain ι₀ α β j).2 h = acts j := fun j ↦ rfl
  have hnx : ∀ j, (buildMain ι₀ α β j).1 h.succ = nxtVec α β h x j := by
    intro j
    show stateVec ι₀ α β (h.val + 1) j = _
    rw [stateVec_succ]
  let p : Fin (K - K / 2) → Prop := fun j' ↦ x j' = s
  let T : Finset (Fin (K - K / 2)) := Finset.univ.filter (fun j ↦ x j = s)
  have hT : ∀ j, p j ↔ j ∈ T := fun j ↦ by simp [T, p]
  let U : Finset (Fin (K - K / 2)) := T.filter (fun j ↦ (rankFin p j).val < m h s)
  have hrank1 : ∀ j, x j = s → rankFin (fun j' ↦ x j' = x j) j = rankFin p j := by
    intro j hj
    simp only [p]
    rw [hj]
  have hactsR : ∀ j, x j = s → acts j = α (h, s, rankFin p j) := by
    intro j hj
    rw [hacts]
    simp only [actVec]
    rw [hrank1 j hj, hj]
  have hmr : ∀ j, x j = s → mainRank (joinData aux (buildMain ι₀ α β)) h (mainIdx j) =
      (rankFin p j).val := by
    intro j hj
    rw [mainRank_joinData]
    congr 2
    funext j'
    simp [hst, hj, p]
  have hUsub : U ⊆ T := Finset.filter_subset _ _
  have hUdown : ∀ k ∈ U, ∀ k' ∈ T, k' < k → k' ∈ U := by
    intro k hk k' hk' hlt
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk', (rankFin_lt_of_lt p ((hT k').mpr hk') hlt).trans hk.2⟩
  have hUcard : U.card = m h s := by
    have hTT := card_filter_rank T T p hT subset_rfl (fun k _ k' hk' _ ↦ hk')
      (fun i ↦ i.val < m h s)
    have hU : U.card = (T.filter (fun k ↦ (rankFin p k).val < m h s)).card := rfl
    rw [hU, hTT]
    have hle : m h s ≤ T.card := hE h s
    have : (Finset.univ.filter (fun i : Fin (K - K / 2) ↦ i.val < T.card ∧ i.val < m h s)) =
        Finset.univ.filter (fun i : Fin (K - K / 2) ↦ i.val < m h s) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hi ↦ hi.2
      · exact fun hi ↦ ⟨lt_of_lt_of_le hi hle, hi⟩
    rw [this]
    have hmn : m h s ≤ K - K / 2 := hle.trans (by simpa using Finset.card_le_univ T)
    calc (Finset.univ.filter (fun i : Fin (K - K / 2) ↦ i.val < m h s)).card
        = ((Finset.univ.map Fin.valEmbedding).filter (· < m h s)).card := by
          rw [Finset.filter_map, Finset.card_map]
          rfl
      _ = (Finset.range (m h s)).card := by
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply, Finset.mem_range]
          constructor
          · rintro ⟨_, hi⟩
            exact hi
          · intro hi
            exact ⟨⟨⟨i, by omega⟩, rfl⟩, hi⟩
      _ = m h s := Finset.card_range _
  have hkeptCount : keptCount m (joinData aux (buildMain ι₀ α β)) h s a =
      (U.filter (fun j ↦ α (h, s, rankFin p j) = a)).card := by
    unfold keptCount
    rw [show (Finset.univ.filter (fun k : Fin K ↦ kept m (joinData aux (buildMain ι₀ α β)) h s k ∧
        acAt (joinData aux (buildMain ι₀ α β)) h k = a)) =
        Finset.univ.filter (fun k : Fin K ↦ K / 2 ≤ k.val ∧
          (stAt (joinData aux (buildMain ι₀ α β)) h k = s ∧
            mainRank (joinData aux (buildMain ι₀ α β)) h k < m h s ∧
            acAt (joinData aux (buildMain ι₀ α β)) h k = a)) by
      ext k; simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and]; tauto]
    rw [card_main_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, stAt, acAt, joinData_mainIdx, hst,
      hac, U, T]
    constructor
    · rintro ⟨hj, hr, ha⟩
      rw [hmr j hj] at hr
      exact ⟨⟨hj, hr⟩, by rw [← hactsR j hj]; exact ha⟩
    · rintro ⟨⟨hj, hr⟩, ha⟩
      exact ⟨hj, by rw [hmr j hj]; exact hr, by rw [hactsR j hj]; exact ha⟩
  have hcount : keptCount m (joinData aux (buildMain ι₀ α β)) h s a = idealCount m α h s a := by
    rw [hkeptCount]
    calc (U.filter (fun j ↦ α (h, s, rankFin p j) = a)).card
        = (Finset.univ.filter (fun i : Fin (K - K / 2) ↦ i.val < U.card ∧ α (h, s, i) = a)).card :=
          card_filter_rank T U p hT hUsub hUdown (fun i ↦ α (h, s, i) = a)
      _ = idealCount m α h s a := by
          rw [hUcard]
          unfold idealCount
          congr 1
  refine ⟨hcount, fun s' ↦ ?_⟩
  let p' : Fin (K - K / 2) → Prop := fun j' ↦ x j' = s ∧ acts j' = a
  let T' : Finset (Fin (K - K / 2)) := Finset.univ.filter (fun j ↦ x j = s ∧ acts j = a)
  have hT' : ∀ j, p' j ↔ j ∈ T' := fun j ↦ by simp [T', p']
  let U' : Finset (Fin (K - K / 2)) := U.filter (fun j ↦ acts j = a)
  have hU'sub : U' ⊆ T' := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjT := (hT j).mpr (hUsub hj.1)
    exact (hT' j).mp ⟨hjT, hj.2⟩
  have hU'down : ∀ k ∈ U', ∀ k' ∈ T', k' < k → k' ∈ U' := by
    intro k hk k' hk' hlt
    rw [Finset.mem_filter] at hk ⊢
    have hk'' := (hT' k').mpr hk'
    exact ⟨hUdown k hk.1 k' ((hT k').mp hk''.1) hlt, hk''.2⟩
  have hU'card : U'.card = idealCount m α h s a := by
    rw [← hcount, hkeptCount]
    congr 1
    ext j
    simp only [U', Finset.mem_filter]
    constructor
    · rintro ⟨hj, ha⟩
      exact ⟨hj, by rw [← hactsR j ((hT j).mpr (hUsub hj))]; exact ha⟩
    · rintro ⟨hj, ha⟩
      exact ⟨hj, by rw [hactsR j ((hT j).mpr (hUsub hj))]; exact ha⟩
  have hrank2 : ∀ j, x j = s → acts j = a →
      rankFin (fun j' ↦ x j' = x j ∧ acts j' = acts j) j = rankFin p' j := by
    intro j hj ha
    simp only [p']
    rw [hj, ha]
  have hnxR : ∀ j, x j = s → acts j = a → nxtVec α β h x j = β ((h, s, a), rankFin p' j) := by
    intro j hj ha
    simp only [nxtVec]
    rw [← hacts, hrank2 j hj ha, hj, ha]
  unfold keptNext
  rw [show (Finset.univ.filter (fun k : Fin K ↦ kept m (joinData aux (buildMain ι₀ α β)) h s k ∧
      acAt (joinData aux (buildMain ι₀ α β)) h k = a ∧
        nxAt (joinData aux (buildMain ι₀ α β)) h k = s')) =
      Finset.univ.filter (fun k : Fin K ↦ K / 2 ≤ k.val ∧
        (stAt (joinData aux (buildMain ι₀ α β)) h k = s ∧
          mainRank (joinData aux (buildMain ι₀ α β)) h k < m h s ∧
          acAt (joinData aux (buildMain ι₀ α β)) h k = a ∧
            nxAt (joinData aux (buildMain ι₀ α β)) h k = s')) by
    ext k; simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and]; tauto]
  rw [card_main_filter]
  calc _ = (U'.filter (fun j ↦ β ((h, s, a), rankFin p' j) = s')).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, stAt, acAt, nxAt,
          joinData_mainIdx, hst, hac, hnx, U', U, T]
        constructor
        · rintro ⟨hj, hr, ha, hn⟩
          rw [hmr j hj] at hr
          exact ⟨⟨⟨hj, hr⟩, ha⟩, by rw [← hnxR j hj ha]; exact hn⟩
        · rintro ⟨⟨⟨hj, hr⟩, ha⟩, hn⟩
          exact ⟨hj, by rw [hmr j hj]; exact hr, ha, by rw [hnxR j hj ha]; exact hn⟩
    _ = (Finset.univ.filter (fun i : Fin (K - K / 2) ↦
          i.val < U'.card ∧ β ((h, s, a), i) = s')).card :=
        card_filter_rank T' U' p' hT' hU'sub hU'down (fun i ↦ β ((h, s, a), i) = s')
    _ = idealNext m α β h s a s' := by
        rw [hU'card]
        unfold idealNext
        congr 1

end Ideal

end StatisticalRL.FiniteVILCB
