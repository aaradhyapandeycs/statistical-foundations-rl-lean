import Formalization.Probability.FiniteMarkov.Definitions
import Formalization.ModelFree.QLearningSamplingDefinitions

/-! # Asynchronous Q-learning on a single Markovian trajectory: definitions only

Source: `sec:async-Q-generative-model`, `chapters/generative_model_model_free.tex:1887–1910`
(trajectory `eq:Markov-chain-behavior-asynQ` :1900–1903, pair chain :1906), update
`eqn:async-q-learning` :1928–1935 with `defn:empirical-Bellman-t` :1940–1946, Algorithm
`alg:async-q` :1977–2001. This module contains no proofs.

* The behaviour trajectory is `a_t ∼ π_b(·|s_t)`, `s_{t+1} ∼ P(·|s_t,a_t)` from a fixed `s₀`, so the
  pairs `X_t = (s_t,a_t)` form a Markov chain with kernel
  `pairKernel ((s,a),(s',a')) = P(s'|s,a) π_b(a'|s')` and initial law
  `initLaw (s,a) = 1{s = s₀} π_b(a|s₀)`.
* `pathLaw M πb s₀ T` is the law of `(X₀,…,X_T)` on `Fin (T+1) → S × A`, with mass
  `1{s₀' = s₀} π_b(a₀|s₀) ∏_{i<T} P(s_{i+1}|s_i,a_i) π_b(a_{i+1}|s_{i+1})`; the iterate `Q_T` only
  depends on these coordinates.
* `iterate M η Q₀ x t` is `Q_t`: for `t ≥ 1` only the entry `(s_{t-1},a_{t-1})` is updated,
  `Q_t(s_{t-1},a_{t-1}) = (1-η) Q_{t-1}(s_{t-1},a_{t-1}) + η (r(s_{t-1},a_{t-1}) +
  γ max_{a'} Q_{t-1}(s_t,a'))`, with the constant rate `η` of :2054–2058.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- The discrete σ-algebra on state–action pairs used for the path law (a local instance only). -/
def pairMeasurableSpace : MeasurableSpace (S × A) := ⊤

attribute [local instance] pairMeasurableSpace

/-- Pair-chain kernel `K((s,a),(s',a')) = P(s'|s,a) π_b(a'|s')` (:1906). -/
noncomputable def pairKernel (M : DiscountedMDP S A) (πb : StationaryPolicy S A)
    (x y : S × A) : ℝ :=
  (M.transition x.1 x.2).prob y.1 * (πb y.1).prob y.2

/-- `t`-step pair-chain transition matrix `K^t((s,a),·)`, the law of `(s_t,a_t)` given
`(s_0,a_0) = (s,a)` (`P^t(·|s,a)` of `defn-tmix`, :2034–2039). -/
noncomputable def pairPow (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (t : ℕ) :
    S × A → S × A → ℝ :=
  kpow (pairKernel M πb) t

/-- Law of `(s₀,a₀)`: `s₀` fixed and `a₀ ∼ π_b(·|s₀)`. -/
noncomputable def initLaw (πb : StationaryPolicy S A) (s₀ : S) (x : S × A) : ℝ :=
  if x.1 = s₀ then (πb s₀).prob x.2 else 0

/-- Law of the state–action path `(X₀,…,X_T)` of the behaviour trajectory started at `s₀`. -/
noncomputable def pathLaw (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (s₀ : S)
    (T : ℕ) : Measure (Fin (T + 1) → S × A) :=
  pathMeasure (initLaw πb s₀) (pairKernel M πb) T

/-- Asynchronous Q-learning iterates `Q_t` along the path `x` with constant rate `η`. -/
noncomputable def iterate (M : DiscountedMDP S A) (η : ℝ) (Q₀ : S → A → ℝ) {n : ℕ}
    (x : Fin (n + 1) → S × A) : ℕ → S → A → ℝ
  | 0 => Q₀
  | t + 1 => fun s a ↦
      if (s, a) = pathAt x t then
        (1 - η) * iterate M η Q₀ x t s a +
          η * (M.reward s a + M.discount * qLearningValue M (iterate M η Q₀ x t) (pathAt x (t + 1)).1)
      else iterate M η Q₀ x t s a

end StatisticalRL.AsyncQ
