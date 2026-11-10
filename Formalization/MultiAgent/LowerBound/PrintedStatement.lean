import Formalization.MDP.CoreDefinitions
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Real.Archimedean

/-!
# Printed Theorem 7.8 as a Lean proposition (definitions only)

Source: `chapters/marl.tex`. Markov game model :15–54, value functions :96–143
(best-response value (124)), suboptimality gap :326–346, generative sampling
:307–311, Theorem 7.8 (`thm:lower-marl`) :487–503.

This file only defines objects and the printed statement; it proves nothing.
The statement is refuted in `MultiAgent/LowerBound/SingletonActionRefutation.lean` (SOURCE-ISSUES C40).

Representation choices. Each departure from the literal text can only make the
printed claim *easier* to satisfy, so a refutation of `Thm7_8_printed` is at
least as strong as a refutation of the literal text.
* States are `Fin S` and player `i` has actions `Fin (A i)` (:21–23); the joint
  action space is `(i : Fin m) → Fin (A i)` (:28–32). Transitions `P_h(·|s,a)`
  are finite probability vectors (:37–38). Steps are indexed by `ℕ`, the game
  uses steps `1, …, H`.
* "`m`-player zero-sum" is not defined in the source for `m ≥ 3`, and for
  `m = 2` it is defined only by violating the `[0,1]` reward normalization
  (:41–43, :50–54). The family of games is therefore only required to satisfy an
  *arbitrary* admissibility predicate `Adm` (which may encode any zero-sum
  convention and any reward normalization); the refutation holds for every `Adm`.
  The reward is an unconstrained real function in the structure.
* Policies are Markov policies `S × [H] → Δ(A_i)` (:124). The estimator in the
  infimum is only required to defeat *data-independent product* estimators
  `π̂ ≡ π₀` (a sub-class of all joint-policy estimators), and the probability
  space `(Ω, law θ)` of the data is existentially chosen by the claimant, with
  no constraint (the generative-model sampling law at sample size `N` is one
  admissible choice).
* `max_θ P_θ(E) ≥ 1/4` is weakened to `sup_θ P_θ(E) ≥ 1/4`, written without
  `iSup` junk as `∀ q < 1/4, ∃ θ, q < P_θ(E)`.
* The best-response value (124) is the real `iSup` over Markov deviations; the
  maximum in (124) exists (finite game, compact simplex), so `iSup` equals it.
  The gap (:332–340) is `⨆ s, ⨆ i, (V^{⋆,π₋ᵢ}_{i,1}(s) - V^π_{i,1}(s))`, a finite
  maximum since `S ≥ 1`, `m ≥ 2`.
* Ranges `S, H ≥ 1` and `A_i ≥ 1` are added as hypotheses (the source puts no
  range on them, :490); adding hypotheses only weakens the claim.
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.Marl

/-- A finite-horizon `m`-player Markov game with states `Fin S`, horizon `H`
and `A i` actions for player `i` (`marl.tex:15–48`). The reward is left
unconstrained; normalization and zero-sum conventions are imposed through the
admissibility predicate of `Thm7_8_printed`. -/
structure MarkovGame (m S H : ℕ) (A : Fin m → ℕ) where
  /-- `P_h(· | s, a)` for the joint action `a`. -/
  transition : ℕ → Fin S → ((i : Fin m) → Fin (A i)) → FiniteDistribution (Fin S)
  /-- `r_{i,h}(s, a)`. -/
  reward : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ

/-- A Markov policy of player `i`: `π_i : ℕ × S → Δ(A_i)` (`marl.tex:124`). -/
abbrev PlayerPolicy (S : ℕ) (n : ℕ) := ℕ → Fin S → FiniteDistribution (Fin n)

/-- A product Markov policy `π = π₁ × ⋯ × π_m`. -/
abbrev ProductPolicy (m S : ℕ) (A : Fin m → ℕ) := (i : Fin m) → PlayerPolicy S (A i)

/-- Probability of the joint action `a` at step `h`, state `s` under a product policy. -/
noncomputable def jointProb {m S : ℕ} {A : Fin m → ℕ} (π : ProductPolicy m S A) (h : ℕ)
    (s : Fin S) (a : (i : Fin m) → Fin (A i)) : ℝ :=
  ∏ i, (π i h s).prob (a i)

/-- `value G π i h k s` is the expected reward of player `i` collected over the
`k` steps `h, h+1, …, h+k-1` from state `s` (`marl.tex:101–106`); the source's
`V^π_{i,1}(s)` is `value G π i 1 H s`. -/
noncomputable def value {m S H : ℕ} {A : Fin m → ℕ} (G : MarkovGame m S H A)
    (π : ProductPolicy m S A) (i : Fin m) : ℕ → ℕ → Fin S → ℝ
  | _, 0, _ => 0
  | h, k + 1, s => ∑ a, jointProb π h s a *
      (G.reward i h s a + (G.transition h s a).expectation (value G π i (h + 1) k))

/-- Best-response value `V^{⋆,π₋ᵢ}_{i,1}(s)` (`marl.tex:122–126`): the supremum
over Markov deviations `π'_i` of player `i`. -/
noncomputable def bestResponseValue {m S H : ℕ} {A : Fin m → ℕ} (G : MarkovGame m S H A)
    (π : ProductPolicy m S A) (i : Fin m) (s : Fin S) : ℝ :=
  ⨆ π' : PlayerPolicy S (A i), value G (Function.update π i π') i 1 H s

/-- Suboptimality gap `NE-gap(π) = max_s max_i (V^{⋆,π₋ᵢ}_{i,1}(s) - V^π_{i,1}(s))`
(`marl.tex:332–340`). -/
noncomputable def gap {m S H : ℕ} {A : Fin m → ℕ} (G : MarkovGame m S H A)
    (π : ProductPolicy m S A) : ℝ :=
  ⨆ s : Fin S, ⨆ i : Fin m, (bestResponseValue G π i s - value G π i 1 H s)

/-- Core of printed Theorem 7.8 for one game size `(m, S, H, A)` and fixed
constants `c₁, c₂`: for every `0 < ε ≤ c₁H` and every total sample size `N`
below `c₂H⁴S max_i A_i / ε²` there is a family of admissible games such that no
(data-independent) estimator has `sup_θ P_θ(gap > ε) < 1/4`. -/
def Thm7_8_core (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop)
    (c₁ c₂ : ℝ) (m S H : ℕ) (A : Fin m → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ c₁ * H →
  ∀ N : ℕ, (N : ℝ) < c₂ * (H : ℝ) ^ 4 * S * ((Finset.univ.sup A : ℕ) : ℝ) / ε ^ 2 →
  ∃ (Θ : Type) (G : Θ → MarkovGame m S H A), (∀ θ, Adm m S H A (G θ)) ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (law : Θ → Measure Ω),
      ∀ π₀ : ProductPolicy m S A, ∀ q : ℝ, q < 1 / 4 →
        ∃ θ, q < (law θ).real {_ω | ε < gap (G θ) π₀}

/-- Printed Theorem 7.8, `thm:lower-marl`, `chapters/marl.tex:487–503`, with the
"zero-sum" (and reward-normalization) convention given by `Adm`: there are
constants `c₁, c₂ > 0` such that for all `m ≥ 2`, `S, H ≥ 1`, `A_i ≥ 1` the core
statement holds. -/
def Thm7_8_printed (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop) :
    Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (m S H : ℕ) (A : Fin m → ℕ), 2 ≤ m → 1 ≤ S → 1 ≤ H → (∀ i, 1 ≤ A i) →
      Thm7_8_core Adm c₁ c₂ m S H A

/-- A weaker reading of Theorem 7.8 in which the constants `c₁, c₂` may depend
on the game size `(m, S, H, A)`. It is implied by `Thm7_8_printed`. -/
def Thm7_8_printed_sizeDependentConstants
    (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop) : Prop :=
  ∀ (m S H : ℕ) (A : Fin m → ℕ), 2 ≤ m → 1 ≤ S → 1 ≤ H → (∀ i, 1 ≤ A i) →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ Thm7_8_core Adm c₁ c₂ m S H A

/-- The literal "`m`-player zero-sum" reading `∑ᵢ r_{i,h} = 0` with the reward
normalization `r_{i,h} ∈ [0,1]` of `marl.tex:41–43`. -/
def sumZeroNormalized (m S H : ℕ) (A : Fin m → ℕ) (G : MarkovGame m S H A) : Prop :=
  (∀ h s a, ∑ i, G.reward i h s a = 0) ∧ ∀ i h s a, 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1

/-- The "zero-sum with player-wise shifts" reading (footnote at `marl.tex:53`):
rewards sum to a constant at each step. -/
def sumConstant (m S H : ℕ) (A : Fin m → ℕ) (G : MarkovGame m S H A) : Prop :=
  ∀ h, ∃ c : ℝ, ∀ s a, ∑ i, G.reward i h s a = c

end StatisticalRL.Ch7Rest.Marl
