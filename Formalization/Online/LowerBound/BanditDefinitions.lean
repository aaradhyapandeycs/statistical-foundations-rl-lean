import Formalization.Online.LowerBound.FamilyDefinitions
import Formalization.Probability.AdaptiveKLDefinitions

/-!
# The bandit family of the online lower bound

Definitions for `lem:online-lb-testing` (Lemma 5.21, `chapters/onlineRL.tex:2709–2721`), with the
bandit collection `C_bandit` of `:2683–2704` and the trajectory law of `:4940–4985`.

* `banditRewardRow … i a` is the reward law `P_i(R | a)` of `eq:reward-distribution-Pi-bandit-lb-online`
  (`:4948–4954`): `R = 1` (`true`) with probability `1 − q_i(a)` and `R = 0` (`false`) with
  probability `q_i(a)`, where `q_i` is `onlineLBq` (`eqn:prob-astar-a-1`).
* `BanditLearner A` is an online bandit algorithm: at round `t` (0-based) it draws the arm from
  `policy σ t x`, a law depending only on the observed history `x = ((a_0,R_0),…,(a_{t-1},R_{t-1}))`
  (the source's `π^t(· | x_{t−1})`, `:4960–4970`), and on an internal random seed `σ` drawn once
  from the finite law `seedLaw`. A learner without internal randomization is the case of a
  one-point seed type.
* `compLaw P κ` is the joint law of `(w, z)` with `w ∼ P` and `z ∼ κ w`.
* `banditNextArmErrorProb L … i t` is `P_{B_i}(a_{t+1} ≠ i)`: the history `x_t` of `t` rounds follows
  the adaptive interaction law under `B_i` (`AdaptiveKL.interactionLaw`), and the next arm is drawn
  from `policy σ t x_t`; the probability is averaged over the seed.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL

/-- The joint law of `(w, z)` with `w ∼ P` and then `z ∼ κ w`. -/
noncomputable def compLaw {W Z : Type*} [Fintype W] [Fintype Z] (P : FiniteDistribution W)
    (κ : W → FiniteDistribution Z) : FiniteDistribution (W × Z) where
  prob x := P.prob x.1 * (κ x.1).prob x.2
  prob_nonneg x := mul_nonneg (P.prob_nonneg _) ((κ x.1).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
    exact P.sum_prob

/-- The Bernoulli reward law of arm `a` in the bandit instance `B_i` (`chapters/onlineRL.tex:2690–2704`,
`:4948–4954`): `P_i(R = 1 | a) = 1 − q_i(a)`, `P_i(R = 0 | a) = q_i(a)`. -/
noncomputable def banditRewardRow (H : ℕ) (ε : ℝ) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (i a : Fin A) : FiniteDistribution Bool where
  prob r := if r then 1 - onlineLBq H ε i a else onlineLBq H ε i a
  prob_nonneg r := by
    have h0 := onlineLBq_nonneg hH hε hεH i a
    have h1 := onlineLBq_le_one hH hε hεH i a
    cases r <;> simp <;> linarith
  sum_prob := by simp

/-- The environment of `B_i` as an adaptive-interaction kernel: the reward of the pulled arm `a` is
drawn from `banditRewardRow … i a`, independently of the round and the past. -/
noncomputable def banditEnv (H : ℕ) (ε : ℝ) (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    {A : ℕ} (i : Fin A) : (t : ℕ) → (Fin t → Fin A × Bool) → Fin A → FiniteDistribution Bool :=
  fun _ _ a => banditRewardRow H ε hH hε hεH i a

/-- An online bandit algorithm with `A` arms: the arm at round `t` is drawn from
`policy σ t x`, where `x` is the history of the previous rounds (arms and rewards) and `σ` is an
internal random seed drawn once from `seedLaw`. -/
structure BanditLearner (A : ℕ) where
  Seed : Type
  [seedFintype : Fintype Seed]
  seedLaw : FiniteDistribution Seed
  policy : Seed → (t : ℕ) → (Fin t → Fin A × Bool) → FiniteDistribution (Fin A)

attribute [instance] BanditLearner.seedFintype

/-- `P_{B_i}(a_{t+1} ≠ i)` for the learner `L`: the arm selected after observing the first `t`
rounds (0-based round index `t`) differs from `i`. -/
noncomputable def banditNextArmErrorProb {A : ℕ} (L : BanditLearner A) (H : ℕ) (ε : ℝ)
    (hH : 2 ≤ H) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2) (i : Fin A) (t : ℕ) : ℝ :=
  ∑ σ, L.seedLaw.prob σ *
    ∑ x, (compLaw (interactionLaw (L.policy σ) (banditEnv H ε hH hε hεH i) t)
      (L.policy σ t)).prob x * (if x.2 ≠ i then 1 else 0)

end StatisticalRL.OnlineLowerBound
