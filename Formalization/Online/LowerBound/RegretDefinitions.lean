import Formalization.Online.LowerBound.BanditDefinitions
import Formalization.MDP.PointMassDefinitions

/-!
# Online learners, episode laws and expected regret

Definitions for `thm:minimax-lower-online` (`chapters/onlineRL.tex:2443–2456`).

* An episode of a horizon-`H` MDP is recorded as `(s₁, ((a₁, s₂), …, (a_H, s_{H+1})))`
  (`OnlineEpisode`), 0-based in Lean: entry `h < H` holds the action at step `h` and the next state.
  Including the final state `s_{H+1}` gives the learner at least the source's information.
* `OnlineLearner State Action H` is an online learning algorithm: before episode `k` (0-based) it
  selects a nonstationary randomized Markov policy `policy σ k τ : ℕ → StationaryPolicy`
  (the step-`h` decision rule is `policy σ k τ h`), a function of the trajectories `τ` of the
  episodes before `k` ("each `π^k` may depend arbitrarily on the trajectories collected before
  episode `k`", `:2453–2455`) and of an internal random seed `σ` drawn once from the finite law
  `seedLaw`. A learner without internal randomization is the case of a one-point seed type.
* `episodePathLaw E π s₁` is the law of the path of one episode started at `s₁`: at step `h` the
  action is drawn from `π h` at the current state and the next state from the transition of
  `E h`; it is the adaptive interaction law `AdaptiveKL.interactionLaw` with these kernels.
  `episodeLaw E ρ π` draws `s₁ ∼ ρ` first.
* `onlineHistoryLaw E ρ L σ K` is the joint law of the first `K` episodes for the seed `σ`: episode
  `k` is drawn from `episodeLaw E ρ (policy σ k τ)` given the previous episodes `τ`, so each
  episode starts at `s₁^k ∼ ρ` independently of the past (`:2445–2452`).
* `policySuboptimality E ρ π = V⋆_1(ρ) − V^π_1(ρ)` uses the project's backward-induction optimal
  value and the actual trajectory value of the nonstationary policy.
* `onlineExpectedRegret E ρ L K = E[∑_{k=1}^K (V⋆_1(ρ) − V^{π^k}_1(ρ))]`, the expectation over the seed
  and the history law.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL EnvironmentStage DecisionStage

/-- One episode: the initial state and the `H` action/next-state pairs. -/
abbrev OnlineEpisode (State Action : Type*) (H : ℕ) := State × (Fin H → Action × State)

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The current state after the first `t` steps of a path started at `s₁`. -/
def pathCurrentState (s₁ : State) : (t : ℕ) → (Fin t → Action × State) → State
  | 0, _ => s₁
  | t + 1, x => (x (Fin.last t)).2

/-- The transition row at step `t` from the current state (a point mass after the horizon, where it
is never used by the length-`H` path law). -/
noncomputable def stepRow {H : ℕ} (E : Fin H → EnvironmentStage State Action) (t : ℕ) (s : State)
    (a : Action) : FiniteDistribution State :=
  if ht : t < H then (E ⟨t, ht⟩).transition s a else EnvironmentStage.pointMass s

/-- The environment kernel of one episode started at `s₁`. -/
noncomputable def episodeEnv {H : ℕ} (E : Fin H → EnvironmentStage State Action) (s₁ : State) :
    (t : ℕ) → (Fin t → Action × State) → Action → FiniteDistribution State :=
  fun t x a => stepRow E t (pathCurrentState s₁ t x) a

/-- The action kernel of one episode started at `s₁` under the nonstationary Markov policy `π`. -/
def episodePolicy (π : ℕ → StationaryPolicy State Action) (s₁ : State) :
    (t : ℕ) → (Fin t → Action × State) → FiniteDistribution Action :=
  fun t x => π t (pathCurrentState s₁ t x)

/-- The law of the path `((a₁, s₂), …, (a_H, s_{H+1}))` of one episode started at `s₁`. -/
noncomputable def episodePathLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (π : ℕ → StationaryPolicy State Action) (s₁ : State) :
    FiniteDistribution (Fin H → Action × State) :=
  interactionLaw (episodePolicy π s₁) (episodeEnv E s₁) H

/-- The law of one episode: `s₁ ∼ ρ`, then the path law. -/
noncomputable def episodeLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (π : ℕ → StationaryPolicy State Action) :
    FiniteDistribution (OnlineEpisode State Action H) :=
  compLaw ρ (episodePathLaw E π)

/-- An online learning algorithm for horizon-`H` episodes: before episode `k` it selects the
nonstationary randomized Markov policy `policy σ k τ` from the previous episodes `τ` and an internal
random seed `σ ∼ seedLaw`. -/
structure OnlineLearner (State Action : Type*) [Fintype State] [Fintype Action] (H : ℕ) where
  Seed : Type
  [seedFintype : Fintype Seed]
  seedLaw : FiniteDistribution Seed
  policy : Seed → (k : ℕ) → (Fin k → OnlineEpisode State Action H) →
    ℕ → StationaryPolicy State Action

attribute [instance] OnlineLearner.seedFintype

/-- The joint law of the first `K` episodes for the seed `σ`. -/
noncomputable def onlineHistoryLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (L : OnlineLearner State Action H) (σ : L.Seed) (K : ℕ) :
    FiniteDistribution (Fin K → OnlineEpisode State Action H) :=
  seqLaw (fun k τ => episodeLaw E ρ (L.policy σ k τ)) K

/-- `V⋆_1(ρ) − V^π_1(ρ)` for the MDP with stages `E`. -/
noncomputable def policySuboptimality {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (π : ℕ → StationaryPolicy State Action) : ℝ :=
  ∑ s, ρ.prob s * (optimalValue (List.ofFn E) s - trajectoryValue (controlled (List.ofFn E) π) s)

/-- The expected regret `E_M[∑_{k=1}^K (V⋆_1(ρ) − V^{π^k}_1(ρ))]` of the learner `L` over `K` episodes
(`chapters/onlineRL.tex:2447–2449`). -/
noncomputable def onlineExpectedRegret {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (L : OnlineLearner State Action H) (K : ℕ) : ℝ :=
  ∑ σ, L.seedLaw.prob σ * ∑ τ, (onlineHistoryLaw E ρ L σ K).prob τ *
    ∑ k : Fin K, policySuboptimality E ρ (L.policy σ k (fun i => τ (Fin.castLE k.isLt.le i)))

end StatisticalRL.OnlineLowerBound
