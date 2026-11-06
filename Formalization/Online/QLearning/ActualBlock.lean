import Formalization.Online.QLearning.EpisodeBlock
import Formalization.Online.QLearning.ActualEpisode
import Mathlib.Data.List.TakeDrop

/-! episode-stage decomposition for actual Q-learning
sequential paths. No probability or optimism conclusion is asserted. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The records before a queried stage inside an actual episode. -/
noncomputable def qLearningActualBlockBefore {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) :=
  ((qLearningActualSequentialHistory hH E bonus initial fallback path).drop (k.val*H)).take h.val

/-- The records after a queried stage inside the same actual episode. -/
noncomputable def qLearningActualBlockAfter {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) :=
  ((qLearningActualSequentialHistory hH E bonus initial fallback path).drop
    (k.val*H+h.val+1)).take (H-(h.val+1))

/-- Any actual chronological record j in an episode has its within-episode
stage j−kH. -/
lemma qLearningActualEpisodeRecord_stage {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (i : ℕ) (hi : i < H) :
    let history := qLearningActualSequentialHistory hH E bonus initial fallback path
    let j := k.val*H+i
    ∃ hj : j < history.length, (history.get ⟨j,hj⟩).1.1.val = i := by
  classical
  have hlen : (qLearningActualSequentialHistory hH E bonus initial fallback path).length = K*H := by
    simp [qLearningActualSequentialHistory, onlineSequentialPathHistory_length]
  have hk : (k.val+1)*H ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hlocal : k.val*H+i < (k.val+1)*H := by nlinarith
  have hj : k.val*H+i <
      (qLearningActualSequentialHistory hH E bonus initial fallback path).length := by
    rw [hlen]; omega
  refine ⟨hj, ?_⟩
  have hs := qLearningActualSequentialHistory_stage hH E bonus initial fallback path ⟨k.val*H+i,hj⟩
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hi] using hs

/-- No actual record before stage h in the episode can be the row tagged h. -/
theorem qLearningActualBlockBefore_noVisit {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    ∀ x ∈ qLearningActualBlockBefore hH E bonus initial fallback path k r.1, x.1 ≠ r := by
  classical
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < r.1.val := by
    have := hi
    simp only [qLearningActualBlockBefore, List.length_take, List.length_drop] at this
    omega
  obtain ⟨hj, hs⟩ := qLearningActualEpisodeRecord_stage hH E bonus initial fallback path k i
    (lt_trans hi' r.1.isLt)
  have helem : x = (qLearningActualSequentialHistory hH E bonus initial fallback path)[k.val*H+i] := by
    simpa [qLearningActualBlockBefore, List.getElem_take, List.getElem_drop, Nat.add_comm] using hxi.symm
  intro heq
  have hxstage : x.1.1.val = r.1.val := congrArg (fun row => row.1.val) heq
  rw [helem] at hxstage
  have hs' : (qLearningActualSequentialHistory hH E bonus initial fallback path)[k.val*H+i].1.1.val = i := by
    simpa [List.get_eq_getElem] using hs
  omega

/-- No actual record after stage h in the episode can be the row tagged h. -/
theorem qLearningActualBlockAfter_noVisit {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    ∀ x ∈ qLearningActualBlockAfter hH E bonus initial fallback path k r.1, x.1 ≠ r := by
  classical
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have hi' : r.1.val+1+i < H := by
    have := hi
    simp only [qLearningActualBlockAfter, List.length_take, List.length_drop] at this
    have hr := r.1.isLt
    omega
  obtain ⟨hj, hs⟩ := qLearningActualEpisodeRecord_stage hH E bonus initial fallback path k
    (r.1.val+1+i) hi'
  have helem : x = (qLearningActualSequentialHistory hH E bonus initial fallback path)[k.val*H+(r.1.val+1+i)] := by
    simpa [qLearningActualBlockAfter, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hxi.symm
  intro heq
  have hxstage : x.1.1.val = r.1.val := congrArg (fun row => row.1.val) heq
  rw [helem] at hxstage
  have hs' : (qLearningActualSequentialHistory hH E bonus initial fallback path)[k.val*H+(r.1.val+1+i)].1.1.val = r.1.val+1+i := by
    simpa [List.get_eq_getElem] using hs
  omega

/-- The actual queried-stage record exists before the episode ends. -/
noncomputable def qLearningActualBlockRecord {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) : OnlineMDPRow State Action H × State := by
  classical
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  have he := qLearningActualEpisodeRecord_stage hH E bonus initial fallback path k h.val h.isLt
  exact history.get ⟨k.val*H+h.val, he.choose⟩

/-- The actual episode's stage-ordered block decomposed at the queried stage. -/
noncomputable def qLearningActualBlock {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) :=
  qLearningActualBlockBefore hH E bonus initial fallback path k h ++
  [qLearningActualBlockRecord hH E bonus initial fallback path k h] ++
  qLearningActualBlockAfter hH E bonus initial fallback path k h

/-- Each actual episode block contributes at most its h-stage record to row r.
Its target is evaluated from the genuine table following its earlier stages. -/
theorem qLearningActualBlock_target {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    (qLearningLoggedVisitFold hH E bonus r
      (qLearningActualTableAt hH E bonus initial fallback path (k.val*H))
      (qLearningActualBlock hH E bonus initial fallback path k r.1)).2 =
      if (qLearningActualBlockRecord hH E bonus initial fallback path k r.1).1 = r then
        [qLearningVisitTarget hH E bonus
          (qLearningChronologicalFold hH E bonus
            (qLearningActualTableAt hH E bonus initial fallback path (k.val*H))
            (qLearningActualBlockBefore hH E bonus initial fallback path k r.1))
          (qLearningActualBlockRecord hH E bonus initial fallback path k r.1)]
      else [] := by
  classical
  unfold qLearningActualBlock
  exact qLearningLoggedVisitFold_singleMatch hH E bonus r _ _ _ _
    (qLearningActualBlockBefore_noVisit hH E bonus initial fallback path k r)
    (qLearningActualBlockAfter_noVisit hH E bonus initial fallback path k r)

end StatisticalRL.OnlineRL
