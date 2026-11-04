import Formalization.Online.Regret.MVP.Model.OnlineMVPCommittedModel
import Formalization.Online.SourceOptimism.ObservedBackwardOptimismComposition

/-! Deterministic optimism for the retained-batch MVP planning table.
The statistical certificate is an explicit intermediate premise; the actual
expanded-law batch event and its history pullback must discharge it. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
noncomputable local instance mvpOptStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpOptActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineMVPPlanningStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State) (upto : ℕ) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (onlineMVPActualPlanningStage E rowAt nextAt upto)

theorem onlineMVPPlanningStages_length {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State) (upto : ℕ) :
    (onlineMVPPlanningStages E rowAt nextAt upto).length = H := by
  simp [onlineMVPPlanningStages]

theorem onlineMVPPlanningStages_environments {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State) (upto : ℕ) :
    onlinePlanningEnvironments (onlineMVPPlanningStages E rowAt nextAt upto) = List.ofFn E := by
  simp only [onlinePlanningEnvironments, onlineMVPPlanningStages, List.map_ofFn]
  congr 1

/-- The retained-batch row certificate is stated for the actual true suffix
and actual pre-episode committed batch, uniformly over optimistic U. -/
def onlineMVPObservedBatchCertificates {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K : ℕ)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State)
    (δ c₁ c₂ : ℝ) : Prop :=
  ∀ k : Fin K, ∀ h : Fin H, ∀ s a,
    let stage := onlineMVPActualPlanningStage E rowAt nextAt (k.val*H) h
    3 ≤ (stage.observations s a).length → ∀ U : State → ℝ,
    (∀ x, EnvironmentStage.optimalValue ((List.ofFn E).drop (h.val+1)) x ≤ U x ∧ U x ≤ H) →
    ((E h).transition s a).expectation (EnvironmentStage.optimalValue ((List.ofFn E).drop (h.val+1))) ≤
      (onlineObservedPlanningRow stage s a).expectation U +
      c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance U *
        (Real.log (1/δ)/(stage.observations s a).length)) +
      c₂ * H * (Real.log (1/δ)/(stage.observations s a).length)

/-- The true environment suffix of the retained-batch table is unchanged. -/
theorem onlineMVPPlanningStages_suffix_environments {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State) (upto n : ℕ) :
    onlinePlanningEnvironments ((onlineMVPPlanningStages E rowAt nextAt upto).drop n) =
      (List.ofFn E).drop n := by
  change ((onlineMVPPlanningStages E rowAt nextAt upto).drop n).map (fun stage => stage.environment) = _
  rw [List.map_drop]
  change (onlinePlanningEnvironments (onlineMVPPlanningStages E rowAt nextAt upto)).drop n = _
  rw [onlineMVPPlanningStages_environments]

/-- Actual retained-batch certificates supply the existing deterministic
backward induction; no claim is made here about their probability. -/
theorem onlineMVPBatchCertificates_imply_optimism {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State)
    (δ c₁ c₂ : ℝ) (hL : 1 ≤ Real.log (1/δ)) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hevent : onlineMVPObservedBatchCertificates E K rowAt nextAt δ c₁ c₂)
    (k : Fin K) (h : Fin H) :
    (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
        (onlineMVPPlanningStages E rowAt nextAt (k.val*H)) h.val s) ∧
    (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
        (onlineMVPPlanningStages E rowAt nextAt (k.val*H)) h.val s a) := by
  let stages := onlineMVPPlanningStages E rowAt nextAt (k.val*H)
  have hcert : onlineChronologicalBonusCertificates (H : ℝ) (Real.log (1/δ)) c₁ c₂ stages := by
    apply onlineChronologicalCertificates_of_suffixHeads
    intro n stage tail hdrop
    have hlength := congrArg List.length hdrop
    have hstages : stages.length = H := by simp [stages, onlineMVPPlanningStages_length]
    simp only [List.length_drop, hstages, List.length_cons] at hlength
    have hn : n < H := by omega
    let j : Fin H := ⟨n,hn⟩
    have hcanonical : stages.drop j.val =
        onlineMVPActualPlanningStage E rowAt nextAt (k.val*H) j :: stages.drop (j.val+1) := by
      have hi : j.val < stages.length := by simpa [stages, onlineMVPPlanningStages_length] using j.isLt
      simpa [stages, onlineMVPPlanningStages, List.getElem_ofFn] using List.drop_eq_getElem_cons hi
    rw [hdrop] at hcanonical
    have hs := (List.cons.inj hcanonical).1
    have ht := (List.cons.inj hcanonical).2
    subst stage
    subst tail
    have henv : onlinePlanningEnvironments (stages.drop (j.val+1)) =
        (List.ofFn E).drop (j.val+1) := by
      exact onlineMVPPlanningStages_suffix_environments E rowAt nextAt (k.val*H) (n+1)
    intro s a hnrow U hU
    have hc := hevent k j s a hnrow U (by simpa only [henv] using hU)
    simpa only [onlinePlanningHeadCertificate, onlineMVPActualPlanningStage, henv] using hc
  have hsuffix := onlineChronologicalCertificates_drop (H : ℝ) (Real.log (1/δ)) c₁ c₂ stages hcert h.val
  have hlen : ((stages.drop h.val).length : ℝ) ≤ H := by
    exact_mod_cast (show (stages.drop h.val).length ≤ H by simp [stages, onlineMVPPlanningStages_length])
  have hb := onlineCappedBackward_dominates_trueOptimal (H : ℝ) (Real.log (1/δ)) c₁ c₂
    (Nat.cast_nonneg _) hL hc₁ hc₂ (stages.drop h.val) hlen hsuffix
  rw [onlineMVPPlanningStages_suffix_environments] at hb
  exact hb
end StatisticalRL.OnlineRL
