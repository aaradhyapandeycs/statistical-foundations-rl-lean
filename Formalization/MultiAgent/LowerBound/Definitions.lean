import Formalization.MultiAgent.LowerBound.PrintedStatement
import Formalization.Probability.AdaptiveKLDefinitions

/-!
# Corrected Theorem 7.8: definitions

Source: `chapters/marl.tex`. Markov game model :15–54 (zero-sum convention :50–53), Markov and
product policies :71–91, values :96–106, best response `eq:defn-optimal-V` :119–126, generative
model :307–315 (adaptive queries), gap `eq:defn-NE-gap` :332–340 (applied to joint policies for CCE,
:346), plug-in estimator with the true reward :374, Theorem 7.8 (`thm:lower-marl`) :487–503 (stated
without citation or proof).

Definitions only.

* `JointPolicy`: a (possibly correlated) Markov joint policy `π_h(· | s) ∈ Δ(A_1 × ⋯ × A_m)`.
* `deviate π i π'`: the policy `π'_i × π_{-i}` of :119–126, with `π_{-i}` the marginal of `π` on the
  other players (:84–85). It is the law of `update a' i b` with `a' ∼ π_h(·|s)` and an independent
  `b ∼ π'_{i,h}(·|s)`, whose probability of `a` is `π'_{i,h}(a_i|s) · π_{-i,h}(a_{-i}|s)`.
* `valueJ`, `bestResponseValueJ`, `gapJ`: values, best-response values (real `iSup` over Markov
  deviations; the maximum exists) and the gap `max_s max_i (V^{⋆,π_{-i}}_{i,1}(s) − V^π_{i,1}(s))`.
* `Query m S H A = Fin H × Fin S × (joint actions)`: a generative-model call `(h, s, a)` at the game
  step `h + 1`; `genEnv G` returns `s' ∼ P_{h+1}(· | s, a)`. With `AdaptiveKL.interactionLaw` the
  learner chooses each query by an arbitrary randomized history-dependent rule.
* `zeroSumAdm`: rewards sum to `0` over players, player 1 (index `0`) has rewards in `[0,1]`, and all
  rewards lie in `[-1,1]` (for `m = 2` this is `r₂ = −r₁`, `r₁ ∈ [0,1]`, `marl.tex:50–53`; for
  `m ≥ 3` it is a disclosed choice, the source does not define `m`-player zero-sum).
* `constSumAdm`: rewards sum to `1` and all lie in `[0,1]` (normalised constant-sum variant).
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- A Markov joint (possibly correlated) policy `π_h(· | s)` over joint actions. -/
abbrev JointPolicy (m S : ℕ) (A : Fin m → ℕ) :=
  ℕ → Fin S → FiniteDistribution ((i : Fin m) → Fin (A i))

/-- The deviation `π'_i × π_{-i}` (`marl.tex:119–126`): the law of `update a' i b` with
`a' ∼ π_h(·|s)` and an independent `b ∼ π'_{i,h}(·|s)`. -/
noncomputable def deviate (π : JointPolicy m S A) (i : Fin m) (π' : PlayerPolicy S (A i)) :
    JointPolicy m S A := fun h s =>
  { prob := fun a => ∑ a', ∑ b, (π h s).prob a' * (π' h s).prob b *
      (if Function.update a' i b = a then 1 else 0)
    prob_nonneg := fun a => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg ((π h s).prob_nonneg a') ((π' h s).prob_nonneg b))
        (by split_ifs <;> norm_num)
    sum_prob := by
      rw [Finset.sum_comm]
      have h1 : ∀ a', ∑ a, ∑ b, (π h s).prob a' * (π' h s).prob b *
          (if Function.update a' i b = a then (1 : ℝ) else 0) = (π h s).prob a' := by
        intro a'
        rw [Finset.sum_comm]
        simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [← Finset.mul_sum, (π' h s).sum_prob, mul_one]
      simp_rw [h1]
      exact (π h s).sum_prob }

/-- `valueJ G π i h k s`: expected reward of player `i` over the `k` steps `h, …, h+k-1` from `s`
under the joint policy `π` (`marl.tex:101–106`); `V^π_{i,1}(s) = valueJ G π i 1 H s`. -/
noncomputable def valueJ (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m) :
    ℕ → ℕ → Fin S → ℝ
  | _, 0, _ => 0
  | h, k + 1, s => ∑ a, (π h s).prob a *
      (G.reward i h s a + (G.transition h s a).expectation (valueJ G π i (h + 1) k))

/-- Best-response value `V^{⋆,π_{-i}}_{i,1}(s)` (`marl.tex:119–126`) for a joint policy. -/
noncomputable def bestResponseValueJ (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (s : Fin S) : ℝ :=
  ⨆ π' : PlayerPolicy S (A i), valueJ G (deviate π i π') i 1 H s

/-- The gap `max_s max_i (V^{⋆,π_{-i}}_{i,1}(s) − V^π_{i,1}(s))` (`marl.tex:332–340`) of a joint
policy. -/
noncomputable def gapJ (G : MarkovGame m S H A) (π : JointPolicy m S A) : ℝ :=
  ⨆ s : Fin S, ⨆ i : Fin m, (bestResponseValueJ G π i s - valueJ G π i 1 H s)

/-- A generative-model query `(h, s, a)`: step `h + 1` of the game, state `s`, joint action `a`. -/
abbrev Query (m S H : ℕ) (A : Fin m → ℕ) := Fin H × Fin S × ((i : Fin m) → Fin (A i))

/-- The generative model of `G` (`marl.tex:307–311`): a query `(h, s, a)` returns
`s' ∼ P_{h+1}(· | s, a)`, independently of the past. -/
noncomputable def genEnv (G : MarkovGame m S H A) :
    (t : ℕ) → (Fin t → Query m S H A × Fin S) → Query m S H A → FiniteDistribution (Fin S) :=
  fun _ _ q => G.transition ((q.1 : ℕ) + 1) q.2.1 q.2.2

/-- Zero-sum admissibility: rewards sum to `0` over the players, player 1 (index `0`) has rewards
in `[0,1]`, every reward lies in `[-1,1]`. -/
def zeroSumAdm (G : MarkovGame m S H A) : Prop :=
  (∀ h s a, ∑ i, G.reward i h s a = 0) ∧
  (∀ (i : Fin m) h s a, (i : ℕ) = 0 → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) ∧
  (∀ i h s a, |G.reward i h s a| ≤ 1)

/-- Constant-sum normalised admissibility: rewards sum to `1` over the players and every reward lies
in `[0,1]` (the normalisation of `marl.tex:41–43` with the constant shift of the footnote at :53). -/
def constSumAdm (G : MarkovGame m S H A) : Prop :=
  (∀ h s a, ∑ i, G.reward i h s a = 1) ∧
  (∀ i h s a, 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1)

end StatisticalRL.Ch7Rest.Marl
