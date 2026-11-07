import Formalization.MDP.CoreDefinitions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean

/-!
# Printed Theorem 7.9 (FedSynQ) as a Lean proposition (definitions only)

Source: `chapters/federated_RL.tex`. Setup and sampling :19–29, FedSynQ
(Algorithm `alg:dist-syncq-local`) :35–90, Theorem 7.9
(`thm:dist-syncq-local`) :99–117.

This file only defines objects and the printed statement; it proves nothing.
The statement is refuted, under the literal reading, in `LargeStep79.lean`
(SOURCE-ISSUES C41).

Representation choices. Each departure can only make the printed claim *easier*
to satisfy, so a refutation of `Thm7_9_printed` is at least as strong as a
refutation of the literal text.
* The MDP is the project's `DiscountedMDP` (finite, nonempty state and action
  types, rewards in `[0,1]`, transitions probability vectors, `0 ≤ γ < 1`);
  `S = Fintype.card State`, `A = Fintype.card Action`. Restricting the class of
  MDPs only weakens the claim.
* The FedSynQ update (:47–49, :59–64) and output `Q_T = (1/K)∑ₖ Q_T^k` (:68)
  are defined deterministically from a sample path `s_t^k(s,a)`. The update is
  well defined for every real `η`; the algorithm's input requirement
  `0 < η < 1` (:51, :76) is *not* a hypothesis of the printed theorem, whose
  `η` is prescribed by (114).
* The probability space and the sample path are chosen *existentially* by the
  claimant, with no constraint on their law (the true independent generative
  sampling (:23–26) is one admissible choice). Likewise `Q⋆` is only required to
  be *some* solution of the Bellman optimality equation (the true optimal
  Q-function is one).
* Extra hypotheses (only weakening): `1 ≤ K`, `1 ≤ T`, `0 < γ` (the τ condition
  (106) divides by `γ`), and `τ ∣ T` (:70, "without loss of generality").
* The constants `c_T, c_η` are chosen before every other quantity (book
  convention for "constant"; the τ condition (106) already uses `η`, which
  depends on `c_η`). The printed text names them after `δ, ε, Q₀, τ`; the
  refutation's witness lets only `K` depend on the constants, so readings with
  constants depending on `δ, ε, Q₀, τ, T, γ, S, A` (but not on `K`) are refuted
  too, by inspection. With `K`-dependent constants the witness fails.
* Literal reading of `η`: under the reading that the theorem tacitly assumes the
  prescribed `η` is an admissible input `η ∈ (0,1)`, the refutation's witness is
  outside the theorem and the theorem is vacuous for large `K`, not false.
* `‖Q_T - Q⋆‖_∞ ≤ ε` is written entrywise.
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.Fed

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- `V(s) = max_a Q(s,a)` (`federated_RL.tex:41–43`), as a real `iSup` over the
finite nonempty action type. -/
noncomputable def greedyValue (Q : State → Action → ℝ) (s : State) : ℝ := ⨆ a, Q s a

/-- Local synchronous Q-learning update (`federated_RL.tex:47–49`) with sampled
next states `next s a = s_t^k(s,a)`. -/
noncomputable def localUpdate (M : DiscountedMDP State Action) (η : ℝ)
    (Q : State → Action → ℝ) (next : State → Action → State) : State → Action → ℝ :=
  fun s a ↦ (1 - η) * Q s a + η * (M.reward s a + M.discount * greedyValue Q (next s a))

/-- One FedSynQ iteration `t` (`federated_RL.tex:47–64`): local updates of all
`K` agents, then averaging when `t ≡ 0 (mod τ)`. -/
noncomputable def fedStep (M : DiscountedMDP State Action) (η : ℝ) (K τ t : ℕ)
    (Qs : Fin K → State → Action → ℝ) (next : Fin K → State → Action → State) :
    Fin K → State → Action → ℝ :=
  if t % τ = 0 then fun _ s a ↦ (1 / (K : ℝ)) * ∑ k, localUpdate M η (Qs k) (next k) s a
  else fun k ↦ localUpdate M η (Qs k) (next k)

/-- Local iterates `Q_t^k` of FedSynQ (Algorithm `alg:dist-syncq-local`,
`federated_RL.tex:72–90`) along a sample path `samples t k s a = s_t^k(s,a)`,
started from `Q_0^k = Q₀`. -/
noncomputable def fedRun (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ)
    (Q₀ : State → Action → ℝ) (samples : ℕ → Fin K → State → Action → State) :
    ℕ → Fin K → State → Action → ℝ
  | 0 => fun _ ↦ Q₀
  | t + 1 => fedStep M η K τ (t + 1) (fedRun M η K τ Q₀ samples t) (samples (t + 1))

/-- Output `Q_T = (1/K) ∑ₖ Q_T^k` (`federated_RL.tex:68`). -/
noncomputable def fedOutput (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ)
    (Q₀ : State → Action → ℝ) (samples : ℕ → Fin K → State → Action → State) (T : ℕ) :
    State → Action → ℝ :=
  fun s a ↦ (1 / (K : ℝ)) * ∑ k, fedRun M η K τ Q₀ samples T k s a

/-- `Q` solves the Bellman optimality equation of `M`. -/
def IsOptimalQ (M : DiscountedMDP State Action) (Q : State → Action → ℝ) : Prop :=
  ∀ s a, Q s a = M.reward s a + M.discount * (M.transition s a).expectation (greedyValue Q)

/-- Printed Theorem 7.9 at fixed constants `c_T, c_η` (`federated_RL.tex:99–117`). -/
def Thm7_9_at (c_T c_η : ℝ) : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] (M : DiscountedMDP State Action)
    (K τ T : ℕ) (δ ε η : ℝ) (Q₀ : State → Action → ℝ),
    1 ≤ K → 1 ≤ τ → 1 ≤ T → τ ∣ T → 0 < M.discount →
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) →
    -- (114): the prescribed learning rate
    η = c_η * K * (1 - M.discount) ^ 4 * ε ^ 2 /
      Real.log (Fintype.card State * Fintype.card Action * K * T / δ) →
    -- (106): the synchronization period
    (τ : ℝ) ≤ 1 + 1 / η * min ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)) →
    -- (112–113): the iteration count
    c_T / (K * (1 - M.discount) ^ 5 * ε ^ 2) *
        Real.log (Fintype.card State * Fintype.card Action * K * T /
          (δ * ε * (1 - M.discount) ^ 2)) ^ 3 ≤ T →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (samples : Ω → ℕ → Fin K → State → Action → State) (Qstar : State → Action → ℝ),
      IsOptimalQ M Qstar ∧
      1 - δ ≤ μ.real {ω | ∀ s a, |fedOutput M η K τ Q₀ (samples ω) T s a - Qstar s a| ≤ ε}

/-- Printed Theorem 7.9 (`thm:dist-syncq-local`, `federated_RL.tex:99–117`):
there exist constants `c_T, c_η > 0` for which the guarantee holds. (The
"sufficiently large `c_T` / small `c_η`" reading implies this one.) -/
def Thm7_9_printed : Prop :=
  ∃ c_T c_η : ℝ, 0 < c_T ∧ 0 < c_η ∧ Thm7_9_at c_T c_η

end StatisticalRL.Ch7Rest.Fed
