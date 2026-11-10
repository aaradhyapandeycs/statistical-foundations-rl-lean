import Formalization.MultiAgent.LowerBound.Definitions
import Formalization.Generative.ModelBasedDefinitions

/-!
# Theorem 7.6 (plug-in Markov-game sample complexity): definitions

Source: `chapters/marl.tex`. Markov game :15–46, values :96–106, best response :119–126,
NE `eq:defn-Nash-E` :213–221, CCE `eq:defn-CCE` :230–238, gap `eq:defn-NE-gap` :327–342,
generative model :306–315, plug-in algorithm :355–380 (empirical game with the true reward :374,
planning oracle :377), Theorem 7.6 `thm:sample-complexity-plug-in-marl` :384–399.

Definitions only. Imports definition modules only (`Marl78Defs`, which imports `MarlPrinted78`,
and `Generative.ModelBasedDefinitions`).

* `gameStages G hS hA`: the generative model as `H` environment stages on the state space `Fin S`
  and the joint action space; stage `h : Fin H` samples `P_{h+1}(· | s, a)` (game step `h + 1`).
  The stage reward is `0`: rewards are known and never sampled (:374).
* `gameSamplingLaw`: `N` independent next states for every `(s, a, h)` (:358–366).
* `empiricalGame G N hN data`: the empirical game `(S, {A_i}, H, P̂, r)` (:367–374); at game steps
  `t ∈ [1, H]` the kernel is the empirical frequency of the stage-`t-1` samples, elsewhere it is the
  (unused) true kernel; the reward is the true reward.
* `IsCCE`, `IsNE`: the printed equilibrium notions (only at step `h = 1`, as printed).
* `CausalOracle`, `CausalProductOracle`: an oracle whose step-`h` output depends only on the
  rewards and kernels at steps `≥ h` (the restriction of C45).
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- Joint actions `a = (a_1, …, a_m)`. -/
abbrev JointAction (m : ℕ) (A : Fin m → ℕ) := (i : Fin m) → Fin (A i)

/-- The generative model of `G` as environment stages: stage `h` is game step `h + 1`. -/
noncomputable def gameStages (G : MarkovGame m S H A) (hS : 0 < S) (hA : ∀ i, 0 < A i) :
    Fin H → EnvironmentStage (Fin S) (JointAction m A) := fun h =>
  { state_nonempty := ⟨⟨0, hS⟩⟩
    action_nonempty := ⟨fun i => ⟨0, hA i⟩⟩
    transition := G.transition ((h : ℕ) + 1)
    reward := fun _ _ => 0
    reward_nonneg := fun _ _ => le_rfl
    reward_le_one := fun _ _ => zero_le_one }

/-- The sample space: one next state per `((h, s, a), j)`, `j < N`. -/
abbrev GameSamples (m S H : ℕ) (A : Fin m → ℕ) (N : ℕ) :=
  FiniteHorizonGenerative.Samples (Fin S) (JointAction m A) H N

/-- Law of the plug-in data: `N` independent draws from `P_h(· | s, a)` for every `(s, a, h)`. -/
noncomputable def gameSamplingLaw (G : MarkovGame m S H A) (hS : 0 < S) (hA : ∀ i, 0 < A i)
    (N : ℕ) : MeasureTheory.Measure (GameSamples m S H A N) :=
  FiniteHorizonGenerative.samplingLaw (gameStages G hS hA) N

/-- The empirical Markov game `(S, {A_i}, H, P̂, r)` (`marl.tex:367–374`). -/
noncomputable def empiricalGame (G : MarkovGame m S H A) (N : ℕ) (hN : 0 < N)
    (data : GameSamples m S H A N) : MarkovGame m S H A where
  transition t s a :=
    if ht : 1 ≤ t ∧ t ≤ H then
      FiniteDistribution.empiricalRow N hN (fun j => data ((⟨t - 1, by omega⟩, s, a), j))
    else G.transition t s a
  reward := G.reward

/-- Coarse correlated equilibrium, `eq:defn-CCE` (`marl.tex:230–238`). -/
def IsCCE (G : MarkovGame m S H A) (π : JointPolicy m S A) : Prop :=
  ∀ (s : Fin S) (i : Fin m), bestResponseValueJ G π i s ≤ valueJ G π i 1 H s

/-- Nash equilibrium of a product policy, `eq:defn-Nash-E` (`marl.tex:213–221`). -/
def IsNE (G : MarkovGame m S H A) (π : ProductPolicy m S A) : Prop :=
  ∀ (s : Fin S) (i : Fin m), value G π i 1 H s = bestResponseValue G π i s

/-- A causal planning oracle: its step-`h` output depends only on the rewards and kernels at the
steps `t ≥ h` (as for backward induction, `generative_model_model_based.tex:2549`). -/
def CausalOracle (O : MarkovGame m S H A → JointPolicy m S A) : Prop :=
  ∀ (G G' : MarkovGame m S H A) (h : ℕ),
    (∀ t, h ≤ t → G.transition t = G'.transition t ∧ ∀ i, G.reward i t = G'.reward i t) →
    O G h = O G' h

/-- A causal planning oracle returning product policies. -/
def CausalProductOracle (O : MarkovGame m S H A → ProductPolicy m S A) : Prop :=
  ∀ (G G' : MarkovGame m S H A) (h : ℕ),
    (∀ t, h ≤ t → G.transition t = G'.transition t ∧ ∀ i, G.reward i t = G'.reward i t) →
    ∀ i, O G i h = O G' i h

end StatisticalRL.Ch7Rest.Marl76
