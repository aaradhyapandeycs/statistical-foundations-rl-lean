import Formalization.ModelFree.QLearningLowerBoundDefinitions
import Formalization.ModelFree.QLearningIterateBounds

/-!
# Time-varying versions of the Step-5 auxiliary objects (definitions only)

The case-(ii) definitions (`qLbAuxIterate`, `qLbXi`, `qLbCommon`, `qLbChain2`, `qLbRun` in
`QLearningLowerBound{Definitions,Pathwise,Moderate}.lean`) hard-code a constant rate. These are the
same objects of the proof of `thm:LB-example-Q-generative`
(`chapters/generative_model_model_free.tex:3316–3420`, `eqn:Qhat-schumann`, `eqn:defn-xi-t`,
`eq:vt-2-Q-lower`) for a learning-rate schedule `η : ℕ → ℝ`, where round `t+1` uses `η (t+1)`
exactly as `qLearningIterate` does. `ξ` and the common part `C` are written recursively; the
closed form `ξ_t(a) = ∑_k η_k ∏_{j=k+1}^t (1-η_j) γ (P_k(1∣1,a) - p) V̂_{k-1}` is not needed.
-/

namespace StatisticalRL.QLearning

/-- The auxiliary sequence `Q̂_t(a)` of `eqn:Qhat-schumann` with schedule `η`, initialized at
`Q⋆(1,a) = 1/(1-γp)`, driven by the state-1 samples. -/
noncomputable def qLbvAuxIterate (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) :
    ℕ → Bool → ℝ
  | 0 => fun _ ↦ 1 / (1 - γ * qHardP γ)
  | t + 1 => fun a ↦ (1 - η (t + 1)) * qLbvAuxIterate γ η samples t a +
      η (t + 1) * (1 + γ * qLbStay samples 1 (t + 1) a *
        max (qLbvAuxIterate γ η samples t false) (qLbvAuxIterate γ η samples t true))

/-- `V̂_t = max_a Q̂_t(a)`. -/
noncomputable def qLbvAuxValue (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4)
    (t : ℕ) : ℝ :=
  max (qLbvAuxIterate γ η samples t false) (qLbvAuxIterate γ η samples t true)

/-- `ξ_0(a) = 0`, `ξ_{t+1}(a) = (1-η_{t+1}) ξ_t(a) + η_{t+1} γ (P_{t+1}(1∣1,a) - p) V̂_t`. -/
noncomputable def qLbvXi (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) :
    ℕ → Bool → ℝ
  | 0 => fun _ ↦ 0
  | t + 1 => fun a ↦ (1 - η (t + 1)) * qLbvXi γ η samples t a +
      η (t + 1) * γ * (qLbStay samples 1 (t + 1) a - qHardP γ) * qLbvAuxValue γ η samples t

/-- `ξ_{t,max} = max_a ξ_t(a)`. -/
noncomputable def qLbvXiMax (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4)
    (t : ℕ) : ℝ :=
  max (qLbvXi γ η samples t false) (qLbvXi γ η samples t true)

/-- The common part `C_t`: `C_0 = 0`, `C_{t+1} = (1-η_{t+1}) C_t + η_{t+1} γ p (V̂_t - V⋆(1))`. -/
noncomputable def qLbvCommon (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η (t + 1)) * qLbvCommon γ η samples t +
      η (t + 1) * γ * qHardP γ * (qLbvAuxValue γ η samples t - 1 / (1 - γ * qHardP γ))

/-- The state-2 value chain `v_t` of `eq:vt-2-Q-lower` with schedule `η`, `v_0 = 0`. -/
noncomputable def qLbvChain2 (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η (t + 1)) * qLbvChain2 γ η samples t +
      η (t + 1) * (1 + γ * qLbStay samples 2 (t + 1) false * qLbvChain2 γ η samples t)

/-- Synchronous Q-learning on `qLbMDP` from `Q₀ = 0` with schedule `η`. -/
noncomputable def qLbvRun (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) : Fin 4 → Bool → ℝ :=
  qLearningIterate (qLbMDP γ hγ hγ1) η samples (fun _ _ ↦ 0) t

end StatisticalRL.QLearning
