import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeCentering
import Mathlib.Algebra.BigOperators.Intervals

/-! Same-experiment suffix proof component: OnlineT4SuffixTelescope.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance suffixStateMeasurable : MeasurableSpace State := ⊤

theorem onlineSumFin_suffix_eq_Ico {H : ℕ} (f : Fin H → ℝ) (j : ℕ) :
    (∑ h ∈ Finset.univ.filter (fun h : Fin H => j ≤ h.val), f h) =
      ∑ n ∈ Finset.Ico j H, if hn : n < H then f ⟨n, hn⟩ else 0 := by
  have hf : (Finset.range H).filter (fun n => j ≤ n) = Finset.Ico j H := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact and_comm
  rw [← hf, Finset.sum_filter, Finset.sum_filter, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [dif_pos h.isLt]

theorem onlineFixedPolicy_suffix_return_noise_identity {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (state : ℕ → State) (j : ℕ) (hj : j ≤ H) :
    let D := onlineFixedPolicyStages E g
    (∑ n ∈ Finset.Ico j H,
      if hn : n < H then
        (E ⟨n, hn⟩).reward (state n) (g ⟨n, hn⟩ (state n)) else 0) -
      DecisionStage.trajectoryValue (D.drop j) (state j) =
    ∑ n ∈ Finset.Ico j H,
      if hn : n < H then
        DecisionStage.trajectoryValue (D.drop (n + 1)) (state (n + 1)) -
          ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).expectation
            (DecisionStage.trajectoryValue (D.drop (n + 1)))
      else 0 := by
  let D := onlineFixedPolicyStages E g
  let v : ℕ → ℝ := fun n => DecisionStage.trajectoryValue (D.drop n) (state n)
  let r : ℕ → ℝ := fun n => if hn : n < H then
    (E ⟨n, hn⟩).reward (state n) (g ⟨n, hn⟩ (state n)) else 0
  let z : ℕ → ℝ := fun n => if hn : n < H then
    DecisionStage.trajectoryValue (D.drop (n + 1)) (state (n + 1)) -
      ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).expectation
        (DecisionStage.trajectoryValue (D.drop (n + 1))) else 0
  have hp : ∀ n ∈ Finset.Ico j H, z n = r n + (v (n + 1) - v n) := by
    intro n hn
    have hn' : n < H := (Finset.mem_Ico.mp hn).2
    have hb : v n =
        (E ⟨n, hn'⟩).reward (state n) (g ⟨n, hn'⟩ (state n)) +
          ((E ⟨n, hn'⟩).transition (state n) (g ⟨n, hn'⟩ (state n))).expectation
            (DecisionStage.trajectoryValue (D.drop (n + 1))) :=
      onlineFixedPolicyValue_step E g ⟨n, hn'⟩ (state n)
    dsimp only [z, r, v] at *
    simp only [dif_pos hn']
    linarith only [hb]
  have hs : (∑ n ∈ Finset.Ico j H, z n) =
      (∑ n ∈ Finset.Ico j H, r n) + (v H - v j) := by
    calc
      _ = ∑ n ∈ Finset.Ico j H, (r n + (v (n + 1) - v n)) :=
        Finset.sum_congr rfl hp
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_Ico_sub _ hj]
  have hd : D.drop H = [] := List.drop_eq_nil_of_le (by simp [D, onlineFixedPolicyStages])
  have hz : v H = 0 := by simp only [v, hd, DecisionStage.trajectoryValue_nil]
  rw [hz, zero_sub] at hs
  change (∑ n ∈ Finset.Ico j H, r n) - v j = ∑ n ∈ Finset.Ico j H, z n
  linarith only [hs]

noncomputable def onlineT4SuffixEpisodeIncrement
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : ℕ) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h : Fin H => j ≤ h.val),
    onlineT4ActualStep H K hH E fallback planner k h sample

theorem onlineT4SuffixEpisodeIncrement_eq_return_sub_value
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : ℕ) (hj : j ≤ H) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let state := onlineT4EpisodeState H K sample.1 fallback history k.val
    let g := planner (history.take (k.val * H))
    let D := onlineFixedPolicyStages E g
    onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k sample =
      (∑ n ∈ Finset.Ico j H,
        if hn : n < H then
          (E ⟨n, hn⟩).reward (state n) (g ⟨n, hn⟩ (state n)) else 0) -
        DecisionStage.trajectoryValue (D.drop j) (state j) := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let g := planner (history.take (k.val * H))
  let D := onlineFixedPolicyStages E g
  dsimp only
  rw [onlineFixedPolicy_suffix_return_noise_identity E g state j hj]
  unfold onlineT4SuffixEpisodeIncrement
  rw [onlineSumFin_suffix_eq_Ico]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n < H := (Finset.mem_Ico.mp hn).2
  simp only [dif_pos hn']
  have hs := onlineT4ActualStep_eq_policy_noise H K hH E fallback planner k ⟨n, hn'⟩ sample
  have hv : onlineT4PolicyTailAtPrefix H hH E planner k.val ⟨n, hn'⟩ history =
      DecisionStage.trajectoryValue (D.drop (n + 1)) := by
    unfold onlineT4PolicyTailAtPrefix
    rw [onlineT4SelectedStages_eq_fixed]
  change onlineT4ActualStep H K hH E fallback planner k ⟨n, hn'⟩ sample =
      onlineT4PolicyTailAtPrefix H hH E planner k.val ⟨n, hn'⟩ history (state (n + 1)) -
        ((E ⟨n, hn'⟩).transition (state n)
          (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k ⟨n, hn'⟩)).expectation
          (onlineT4PolicyTailAtPrefix H hH E planner k.val ⟨n, hn'⟩ history) at hs
  rw [hv, onlineT4PlayedAction_eq_selected H K hH E sample.1 fallback planner sample.2 k ⟨n, hn'⟩] at hs
  exact hs

theorem onlineT4SuffixEpisodeIncrement_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : ℕ) (hj : j ≤ H) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k sample| ≤ (H : ℝ) := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let g := planner (history.take (k.val * H))
  let D := onlineFixedPolicyStages E g
  let R : ℝ := ∑ n ∈ Finset.Ico j H, if hn : n < H then
    (E ⟨n, hn⟩).reward (state n) (g ⟨n, hn⟩ (state n)) else 0
  have hlo : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro n hn
    simp only [dif_pos (Finset.mem_Ico.mp hn).2]
    exact (E ⟨n, (Finset.mem_Ico.mp hn).2⟩).reward_nonneg _ _
  have hhi : R ≤ (H : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.Ico j H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [dif_pos (Finset.mem_Ico.mp hn).2]
        exact (E ⟨n, (Finset.mem_Ico.mp hn).2⟩).reward_le_one _ _
      _ = ((H - j : ℕ) : ℝ) := by simp
      _ ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H j
  have hvlo := onlineFixedPolicyValue_nonneg E g j (state j)
  have hvhi := onlineFixedPolicyValue_le_horizon E g j (state j)
  rw [onlineT4SuffixEpisodeIncrement_eq_return_sub_value H K hH E fallback planner j hj k sample]
  change |R - DecisionStage.trajectoryValue (D.drop j) (state j)| ≤ (H : ℝ)
  rw [abs_le]
  constructor <;> linarith only [hlo,hhi,hvlo,hvhi]

end StatisticalRL.OnlineRL
