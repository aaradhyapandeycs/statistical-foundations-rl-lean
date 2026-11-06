import Formalization.Online.SourceOptimism.FixedPolicyDefinitions
import Formalization.Online.Regret.Telescope

/-! deterministic T4 return/noise identities. Source:
onlineRL.tex:3802–3818 and the T4 clause of lem:bound-T234 at 988–1005.
These declarations make no conditional-expectation or concentration claim. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The actual trajectory value obeys Bellman evaluation for that policy. -/
theorem onlineFixedPolicyValue_step {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (h : Fin H) (s : State) :
    DecisionStage.trajectoryValue ((onlineFixedPolicyStages E g).drop h.val) s =
      (E h).reward s (g h s) +
        ((E h).transition s (g h s)).expectation
          (DecisionStage.trajectoryValue ((onlineFixedPolicyStages E g).drop (h.val + 1))) := by
  let d : Fin H → DecisionStage State Action :=
    fun h => (E h).withPolicy (fun s => EnvironmentStage.pointMass (g h s))
  have hi : h.val < (List.ofFn d).length := by simpa using h.isLt
  have hdrop : (List.ofFn d).drop h.val =
      d h :: (List.ofFn d).drop (h.val + 1) := by
    simpa only [List.getElem_ofFn] using List.drop_eq_getElem_cons hi
  change DecisionStage.trajectoryValue ((List.ofFn d).drop h.val) s =
    (E h).reward s (g h s) + ((E h).transition s (g h s)).expectation
      (DecisionStage.trajectoryValue ((List.ofFn d).drop (h.val + 1)))
  rw [hdrop, DecisionStage.trajectoryValue_cons]
  change (EnvironmentStage.pointMass (g h s)).expectation
      (fun a => (E h).reward s a + ((E h).transition s a).expectation
        (DecisionStage.trajectoryValue ((List.ofFn d).drop (h.val + 1)))) = _
  rw [EnvironmentStage.expectation_pointMass]

theorem onlineFixedPolicyValue_nonneg {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (n : ℕ) (s : State) :
    0 ≤ DecisionStage.trajectoryValue ((onlineFixedPolicyStages E g).drop n) s := by
  rw [DecisionStage.trajectoryValue_eq_backwardValue]
  exact DecisionStage.backwardValue_nonneg _ _

theorem onlineFixedPolicyValue_le_horizon {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (n : ℕ) (s : State) :
    DecisionStage.trajectoryValue ((onlineFixedPolicyStages E g).drop n) s ≤ (H : ℝ) := by
  have hlen : ((onlineFixedPolicyStages E g).drop n).length ≤ H := by
    simpa only [onlineFixedPolicyStages, List.length_drop, List.length_ofFn] using Nat.sub_le H n
  calc
    _ = DecisionStage.backwardValue ((onlineFixedPolicyStages E g).drop n) s :=
      DecisionStage.trajectoryValue_eq_backwardValue _ _
    _ ≤ (((onlineFixedPolicyStages E g).drop n).length : ℝ) :=
      DecisionStage.backwardValue_le_length _ _
    _ ≤ (H : ℝ) := by exact_mod_cast hlen

/-- Realized reward minus the same policy's expected return is exactly the
sum of fresh-state residuals, with the source T4 sign. Every value is the true
trajectory expectation for the same policy and environment. -/
theorem onlineFixedPolicy_return_noise_identity {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action)
    (state : ℕ → State) :
    let D := onlineFixedPolicyStages E g
    (∑ n ∈ Finset.range H,
      if hn : n < H then
        (E ⟨n, hn⟩).reward (state n) (g ⟨n, hn⟩ (state n)) else 0) -
      DecisionStage.trajectoryValue D (state 0) =
    ∑ n ∈ Finset.range H,
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
  have hpoint : ∀ n ∈ Finset.range H, r n - z n = v n - v (n + 1) := by
    intro n hn
    have hn' : n < H := Finset.mem_range.mp hn
    have hb := onlineFixedPolicyValue_step E g ⟨n, hn'⟩ (state n)
    have hb' : v n =
        (E ⟨n, hn'⟩).reward (state n) (g ⟨n, hn'⟩ (state n)) +
          ((E ⟨n, hn'⟩).transition (state n) (g ⟨n, hn'⟩ (state n))).expectation
            (DecisionStage.trajectoryValue (D.drop (n + 1))) := hb
    simp only [r, z, dif_pos hn', v]
    dsimp only [v] at hb'
    linarith
  have hsum : (∑ n ∈ Finset.range H, r n) - (∑ n ∈ Finset.range H, z n) = v 0 - v H := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ n ∈ Finset.range H, (v n - v (n + 1)) := Finset.sum_congr rfl hpoint
      _ = v 0 - v H := Finset.sum_range_sub' v H
  have hdrop : D.drop H = [] := List.drop_eq_nil_of_le (by simp [D, onlineFixedPolicyStages])
  have hterminal : v H = 0 := by simp only [v, hdrop, DecisionStage.trajectoryValue_nil]
  have hresult : (∑ n ∈ Finset.range H, r n) - v 0 = ∑ n ∈ Finset.range H, z n := by
    rw [hterminal, sub_zero] at hsum
    linarith
  simpa only [r, z, v, D, List.drop_zero] using hresult

end StatisticalRL.OnlineRL
