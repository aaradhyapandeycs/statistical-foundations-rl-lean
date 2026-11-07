import Formalization.MDP.CoreDefinitions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite adaptive (sequential) laws

Definitions for the finite adaptive-data KL chain rule (`Formalization/Probability/AdaptiveKL.lean`),
used by the online lower bound (`thm:minimax-lower-online`, `chapters/onlineRL.tex:2443–2456`; the
chain rule is invoked without a label at `:4991–5009`).

## Representation

* A history of length `t` is a tuple `Fin t → Z` (oldest entry at index `0`); a step kernel is a
  family `κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z`, the law of the next entry given the
  current history. `seqLaw κ T` is the joint law of the first `T` entries, built by
  `P_{T+1}(h) = P_T(Fin.init h) · κ_T(Fin.init h)(h (Fin.last T))`.
* An adaptive interaction has entries `Z = A × O` (action, observation). At step `t` the learner
  draws `a_t ~ π t h_t` (any history-dependent randomized rule) and the environment draws
  `o_t ~ e t h_t a_t`. `interactionKernel π e` is the resulting step kernel and
  `interactionLaw π e T = seqLaw (interactionKernel π e) T`.
* Internal randomization of the learner that is shared across steps (a seed) is not a separate
  field: it can be modelled by an initial step whose action is the seed and whose observation law is
  common to both environments, which contributes zero to the chain rule.

All laws are the project's real finite probability vectors `FiniteDistribution`, so zero-mass atoms
are allowed throughout.
-/

open scoped BigOperators

namespace StatisticalRL.AdaptiveKL

open StatisticalRL

variable {Z : Type*} [Fintype Z]

/-- Reindexing a sum over tuples of length `T + 1` as an iterated sum over the initial `T`-tuple
and the last entry. -/
theorem sum_tuple_succ {M : Type*} [AddCommMonoid M] (T : ℕ) (F : (Fin T → Z) → Z → M) :
    ∑ h : Fin (T + 1) → Z, F (Fin.init h) (h (Fin.last T)) = ∑ p : Fin T → Z, ∑ z, F p z := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 1) => Z))
    (fun x : Z × (Fin T → Z) => F x.2 x.1)
    (fun h => F (Fin.init h) (h (Fin.last T))) (fun x => by simp [Fin.snocEquiv])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The joint law of the first `T` entries of a sequential process with step kernels `κ`. -/
noncomputable def seqLaw (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) :
    (T : ℕ) → FiniteDistribution (Fin T → Z)
  | 0 =>
    { prob := fun _ => 1
      prob_nonneg := fun _ => zero_le_one
      sum_prob := by simp }
  | T + 1 =>
    { prob := fun h => (seqLaw κ T).prob (Fin.init h) * (κ T (Fin.init h)).prob (h (Fin.last T))
      prob_nonneg := fun h =>
        mul_nonneg ((seqLaw κ T).prob_nonneg _) ((κ T (Fin.init h)).prob_nonneg _)
      sum_prob := by
        rw [sum_tuple_succ T (fun p z => (seqLaw κ T).prob p * (κ T p).prob z)]
        simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
        exact (seqLaw κ T).sum_prob }

theorem seqLaw_zero_prob (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) (h : Fin 0 → Z) :
    (seqLaw κ 0).prob h = 1 := rfl

theorem seqLaw_succ_prob (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) (T : ℕ)
    (h : Fin (T + 1) → Z) :
    (seqLaw κ (T + 1)).prob h =
      (seqLaw κ T).prob (Fin.init h) * (κ T (Fin.init h)).prob (h (Fin.last T)) := rfl

variable {A O : Type*} [Fintype A] [Fintype O]

/-- One step of an adaptive interaction: the learner draws `a ~ π t h`, then the environment draws
`o ~ e t h a`; the entry is `(a, o)`. -/
noncomputable def interactionKernel (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O) (t : ℕ) (h : Fin t → A × O) :
    FiniteDistribution (A × O) where
  prob z := (π t h).prob z.1 * (e t h z.1).prob z.2
  prob_nonneg z := mul_nonneg ((π t h).prob_nonneg _) ((e t h z.1).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
    exact (π t h).sum_prob

/-- The law of the length-`T` history `((a_0,o_0),…,(a_{T-1},o_{T-1}))` of an adaptive interaction
between a learner `π` and an environment `e`. -/
noncomputable def interactionLaw (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O) (T : ℕ) :
    FiniteDistribution (Fin T → A × O) :=
  seqLaw (interactionKernel π e) T

/-- Expected number of steps `t < T` at which the feature `φ t h_t a_t` equals `x`, under the
interaction law: `E_P[N_T(x)]` with `N_T(x) = #{t < T : φ t h_t a_t = x}`. Here `h_t` is the length-`t`
prefix of the history and `a_t` the action component of its `t`-th entry. -/
noncomputable def expectedVisits {X : Type*} [DecidableEq X]
    (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O) (T : ℕ)
    (φ : (t : ℕ) → (Fin t → A × O) → A → X) (x : X) : ℝ :=
  ∑ h : Fin T → A × O, (interactionLaw π e T).prob h *
    ∑ t : Fin T, if φ t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1 = x then 1 else 0

open Classical in
/-- Expected number of steps `t < T` at which the predicate `M t h_t a_t` holds, under the
interaction law: `E_P[#{t < T : M t h_t a_t}]`. -/
noncomputable def expectedCount
    (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O) (T : ℕ)
    (M : (t : ℕ) → (Fin t → A × O) → A → Prop) : ℝ :=
  ∑ h : Fin T → A × O, (interactionLaw π e T).prob h *
    ∑ t : Fin T, if M t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1 then 1 else 0

end StatisticalRL.AdaptiveKL
