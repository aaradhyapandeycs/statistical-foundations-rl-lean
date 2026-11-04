import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVariancePotential
import Formalization.Online.Regret.T4.OnlineRegretT4Telescope

/-! Actual-law variance and gap proof component: OnlineFixedPolicyVarianceTelescope.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineFixedPolicyVariancePotential_step {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (h : Fin H) (s : State) :
    let D := onlineFixedPolicyStages E g
    finiteTrajectoryVariancePotential (D.drop h.val) s =
      ((E h).transition s (g h s)).variance (DecisionStage.trajectoryValue (D.drop (h.val + 1))) +
      ((E h).transition s (g h s)).expectation (finiteTrajectoryVariancePotential (D.drop (h.val + 1))) := by
  let d : Fin H → DecisionStage State Action :=
    fun h => (E h).withPolicy (fun s => EnvironmentStage.pointMass (g h s))
  have hi : h.val < (List.ofFn d).length := by simpa using h.isLt
  have hdrop : (List.ofFn d).drop h.val = d h :: (List.ofFn d).drop (h.val + 1) := by
    simpa only [List.getElem_ofFn] using List.drop_eq_getElem_cons hi
  change finiteTrajectoryVariancePotential ((List.ofFn d).drop h.val) s = _
  rw [hdrop, finiteTrajectoryVariancePotential_cons]
  change (EnvironmentStage.pointMass (g h s)).expectation (fun a =>
    ((E h).transition s a).variance (DecisionStage.trajectoryValue ((List.ofFn d).drop (h.val + 1))) +
      ((E h).transition s a).expectation (finiteTrajectoryVariancePotential ((List.ofFn d).drop (h.val + 1)))) = _
  rw [EnvironmentStage.expectation_pointMass]
  rfl

theorem onlineFixedPolicy_variance_potential_noise_identity {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (state : ℕ → State) :
    let D := onlineFixedPolicyStages E g
    (∑ n ∈ Finset.range H, if hn : n < H then
      ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).variance
        (DecisionStage.trajectoryValue (D.drop (n + 1))) else 0) =
    finiteTrajectoryVariancePotential D (state 0) -
      ∑ n ∈ Finset.range H, if hn : n < H then
        ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).expectation
          (finiteTrajectoryVariancePotential (D.drop (n + 1))) -
            finiteTrajectoryVariancePotential (D.drop (n + 1)) (state (n + 1)) else 0 := by
  let D := onlineFixedPolicyStages E g
  let v : ℕ → ℝ := fun n => finiteTrajectoryVariancePotential (D.drop n) (state n)
  let r : ℕ → ℝ := fun n => if hn : n < H then
    ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).variance
      (DecisionStage.trajectoryValue (D.drop (n + 1))) else 0
  let z : ℕ → ℝ := fun n => if hn : n < H then
    ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).expectation
      (finiteTrajectoryVariancePotential (D.drop (n + 1))) -
        finiteTrajectoryVariancePotential (D.drop (n + 1)) (state (n + 1)) else 0
  have hpoint : ∀ n ∈ Finset.range H, r n + z n = v n - v (n + 1) := by
    intro n hn
    have hn' : n < H := Finset.mem_range.mp hn
    have hb := onlineFixedPolicyVariancePotential_step E g ⟨n, hn'⟩ (state n)
    have hb' : v n = r n +
        ((E ⟨n, hn'⟩).transition (state n) (g ⟨n, hn'⟩ (state n))).expectation
          (finiteTrajectoryVariancePotential (D.drop (n + 1))) := by
      simpa only [v, r, dif_pos hn', D] using hb
    simp only [r, z, dif_pos hn', v]
    dsimp only [v] at hb'
    linarith
  have hsum : (∑ n ∈ Finset.range H, r n) + (∑ n ∈ Finset.range H, z n) = v 0 - v H := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ n ∈ Finset.range H, (v n - v (n + 1)) := Finset.sum_congr rfl hpoint
      _ = v 0 - v H := Finset.sum_range_sub' v H
  have hdrop : D.drop H = [] := List.drop_eq_nil_of_le (by simp [D, onlineFixedPolicyStages])
  have hterminal : v H = 0 := by simp only [v, hdrop, finiteTrajectoryVariancePotential_nil]
  have hresult : (∑ n ∈ Finset.range H, r n) = v 0 - ∑ n ∈ Finset.range H, z n := by
    rw [hterminal, sub_zero] at hsum
    linarith
  simpa only [r, z, v, D, List.drop_zero] using hresult
end StatisticalRL.OnlineRL
