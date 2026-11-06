import Formalization.Online.QLearning.ActualRegretStep

namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

private theorem controlled_ofFn {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (π : ℕ → StationaryPolicy State Action) :
    EnvironmentStage.controlled (List.ofFn E) π =
      List.ofFn (fun h => (E h).withPolicy (π h.val)) := by
  induction H generalizing π with
  | zero => rfl
  | succ H ih =>
    rw [List.ofFn_succ, EnvironmentStage.controlled, ih, List.ofFn_succ]
    rfl

/-- Actual policy values are true returns in the same MDP, so optimality
holds at every suffix, independently of the optimism event. -/
theorem qLearning_greedyTruePolicyValue_le_optimal {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (n : ℕ) (s : State) :
    qLearningGreedyTruePolicyValue E table n s ≤
      EnvironmentStage.optimalValue ((List.ofFn E).drop n) s := by
  let g := qLearningChronologicalPolicy E table
  let π : ℕ → StationaryPolicy State Action := fun j x =>
    EnvironmentStage.pointMass (g ⟨j%H,Nat.mod_lt j hH⟩ x)
  have hfixed : EnvironmentStage.controlled (List.ofFn E) π = onlineFixedPolicyStages E g := by
    rw [controlled_ofFn]
    unfold onlineFixedPolicyStages
    congr 1
    funext h
    apply congrArg (E h).withPolicy
    funext x
    simp only [π,Nat.mod_eq_of_lt h.isLt]
  have hc := EnvironmentStage.trajectoryValue_le_optimal ((List.ofFn E).drop n)
    (fun j => π (n+j)) s
  rw [← EnvironmentStage.controlled_drop, hfixed] at hc
  exact hc

/-- The true optimal-policy difference lies in [0,H]; no confidence premise. -/
theorem qLearning_greedyPolicyOptimalityGap_mem_Icc {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (n : ℕ) (s : State) :
    qLearningGreedyPolicyOptimalityGap E table n s ∈ Set.Icc 0 (H:ℝ) := by
  have hlo := qLearning_greedyTruePolicyValue_le_optimal hH E table n s
  have hv := onlineFixedPolicyValue_nonneg E (qLearningChronologicalPolicy E table) n s
  have ho := onlineTrueOptimalValue_range_length ((List.ofFn E).drop n) s
  have hlen : (((List.ofFn E).drop n).length : ℝ) ≤ H := by
    have hn : ((List.ofFn E).drop n).length ≤ H := by simp
    exact_mod_cast hn
  change 0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop n) s -
    qLearningGreedyTruePolicyValue E table n s ∧
    EnvironmentStage.optimalValue ((List.ofFn E).drop n) s -
      qLearningGreedyTruePolicyValue E table n s ≤ H
  change 0 ≤ qLearningGreedyTruePolicyValue E table n s at hv
  exact ⟨sub_nonneg.mpr hlo, by linarith [ho.2]⟩

/-- Each actual transition residual is bounded by H, with the source sign. -/
theorem qLearning_greedyPolicyResidual_abs_le {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (r : OnlineMDPRow State Action H) (next : State) :
    |qLearningGreedyPolicyResidual E table r next| ≤ (H:ℝ) := by
  have hg := qLearning_greedyPolicyOptimalityGap_mem_Icc hH E table (r.1.val+1)
  have hmlo := (onlineMDPSuccessorRowLaw E r).expectation_nonneg (fun x => (hg x).1)
  have hmhi := (onlineMDPSuccessorRowLaw E r).expectation_le_const (fun x => (hg x).2)
  dsimp only [qLearningGreedyPolicyResidual]
  rw [abs_le]
  constructor <;> linarith [(hg next).1,(hg next).2]

/-- Source regret is bounded by optimistic estimated value minus the actual
selected policy's true trajectory value, on the single actual optimism event. -/
theorem qLearning_actual_regret_le_optimistic {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let table := fun k : Fin K => qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    (∑ k : Fin K, (EnvironmentStage.optimalValue (List.ofFn E) (initial k) -
      qLearningGreedyTruePolicyValue E (table k) 0 (initial k))) ≤
    (∑ k : Fin K, (qLearningChronologicalValue hH E (table k) 0 (initial k) -
      qLearningGreedyTruePolicyValue E (table k) 0 (initial k))) := by
  dsimp only
  apply Finset.sum_le_sum
  intro k hk
  have ho := hgood.2.2 k ⟨0,hH⟩ (initial k)
  exact sub_le_sub_right ho _

end StatisticalRL.OnlineRL
