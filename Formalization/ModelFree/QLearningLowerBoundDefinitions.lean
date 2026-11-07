import Formalization.ModelFree.QLearningHardMDPDefinitions

/-!
# The Q-learning lower-bound instance with two actions everywhere (definitions only)

`chapters/generative_model_model_free.tex:2723–2788` (`M_hard`, `p = (4γ-1)/(3γ)`) and the
auxiliary objects of Step 5 (`eqn:Qhat-schumann`, lines 3316–3324; `eqn:defn-xi-t`,
lines 3405–3411).

The source lets action sets vary by state (`A₁ = {1,2}`, all other `A_s = {1}`). To obtain an MDP
with `S = 4` states and `A = 2` actions at every state, action `false` is the source's action `1`
at every state, action `true` at state 1 is the source's action `2`, and action `true` at states
0, 2 and 3 is a *dominated dummy action*: reward 0 and a deterministic move to the absorbing
zero-reward state 0. Its Q-values stay 0 under Q-learning from `Q₀ = 0`, so every source
recursion is unchanged. (Duplicating the single source action at state 2 would not be harmless:
Q-learning would then take a maximum of two independently sampled copies. Hence the copied-action
encoding `qHardMDP` of Lemma 4.14 (`QLearningHardMDPDefinitions.lean`) is fine for optimal values
but unsuitable for the Q-learning dynamics; see `docs/SOURCE-ISSUES.md` C31(5). The values of
`qLbMDP` are `qLbMDP_optimal_values` in `QLearningLowerBoundValues.lean`.)
-/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Transition rows: the source rows of `M_hard` (`qHardRow`) for action `false` and at state 1,
and a deterministic move to state 0 for the dummy action `true` at states 0, 2, 3. -/
noncomputable def qLbRow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Fin 4) (a : Bool) :
    FiniteDistribution (Fin 4) where
  prob t := if s ≠ 1 ∧ a = true then (if t = 0 then 1 else 0) else (qHardRow p hp0 hp1 s).prob t
  prob_nonneg := by
    intro t
    split
    · split <;> norm_num
    · exact (qHardRow p hp0 hp1 s).prob_nonneg t
  sum_prob := by
    split
    · simp
    · exact (qHardRow p hp0 hp1 s).sum_prob

/-- The lower-bound MDP for `1/4 < γ < 1`: `M_hard` of the source, with dominated dummy actions
at states 0, 2, 3. Rewards: 0 at state 0 and for the dummy action, 1 otherwise. -/
noncomputable def qLbMDP (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    DiscountedMDP (Fin 4) Bool where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨false⟩
  transition s a := qLbRow (qHardP γ)
    (by unfold qHardP; apply div_nonneg <;> linarith)
    (by unfold qHardP; rw [div_le_one (by linarith)]; linarith) s a
  reward s a := if s = 0 ∨ (s ≠ 1 ∧ a = true) then 0 else 1
  reward_nonneg := by intro s a; split <;> norm_num
  reward_le_one := by intro s a; split <;> norm_num
  discount := γ
  discount_nonneg := by linarith
  discount_lt_one := hγ1

/-- The empirical transition indicator `P_k(s ∣ s, a) = 1{s_k(s,a) = s}` of the source
(Step 2, lines 2858–2866), for a sample stream `samples k s a = s_k(s,a)`. -/
noncomputable def qLbStay (samples : ℕ → Fin 4 → Bool → Fin 4) (s : Fin 4) (k : ℕ) (a : Bool) :
    ℝ :=
  if samples k s a = s then 1 else 0

/-- The auxiliary sequence `Q̂_t(a)` of `eqn:Qhat-schumann` (lines 3316–3324): constant learning
rate `η`, initialized at `Q⋆(1,a) = 1/(1-γp)`, driven by the state-1 samples, with
`V̂_{t-1} = max_a Q̂_{t-1}(a)`. -/
noncomputable def qLbAuxIterate (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) :
    ℕ → Bool → ℝ
  | 0 => fun _ ↦ 1 / (1 - γ * qHardP γ)
  | t + 1 => fun a ↦ (1 - η) * qLbAuxIterate γ η samples t a +
      η * (1 + γ * qLbStay samples 1 (t + 1) a *
        max (qLbAuxIterate γ η samples t false) (qLbAuxIterate γ η samples t true))

/-- `V̂_t = max_a Q̂_t(a)`. -/
noncomputable def qLbAuxValue (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) : ℝ :=
  max (qLbAuxIterate γ η samples t false) (qLbAuxIterate γ η samples t true)

/-- `ξ_t(a) = ∑_{k=1}^t η(1-η)^{t-k} γ (P_k(1∣1,a) - p) V̂_{k-1}` (`eqn:defn-xi-t`). -/
noncomputable def qLbXi (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    ℝ :=
  ∑ k ∈ Finset.Icc 1 t, η * (1 - η) ^ (t - k) * γ *
    (qLbStay samples 1 k a - qHardP γ) * qLbAuxValue γ η samples (k - 1)

/-- `ξ_{t,max} = max_a ξ_t(a)`. -/
noncomputable def qLbXiMax (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) : ℝ :=
  max (qLbXi γ η samples t false) (qLbXi γ η samples t true)

end StatisticalRL.QLearning
