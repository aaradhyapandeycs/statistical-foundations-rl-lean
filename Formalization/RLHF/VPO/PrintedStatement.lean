import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 7.12 (online VPO): the printed step size and update (definitions only)

Source: `chapters/RLHF.tex`. Bradley–Terry model and `σ` :24–31, calibrated value
and VPO :92–135, linear rewards (Assumption `assump:linear`) :144–154, online VPO
(Algorithm `alg:online_RBMLE`) :182–203, Theorem 7.12 (`thm_online`) :208–215.

The regret bound of Theorem 7.12 is stated with `Õ(·)` and is not transcribed.
This file transcribes the two objects that the theorem relies on and that are
ill-defined (SOURCE-ISSUES C44): the prescribed regularization strength `α`
(:214) and the online VPO update (:194–198). It proves nothing; see
`RLHF/VPO/IllPosed.lean`.

Representation choices.
* `α = exp(-(2r_max + r_max/β)) · √(T / (κ · min{d log T, T}))` is transcribed
  with Lean's real division, so the source's division by zero at `T = 1`
  appears as Lean's junk value `x / 0 = 0`.
* The update (194–198) minimizes over policies `π`; by the reduction
  (:126–133) it is a minimization over policies `π_r` induced by real rewards,
  i.e. policies with full support when `π_ref` has full support. The objective
  involves `log π`, which is a real number exactly on full-support policies, so
  the argmin is taken over full-support policies (`IsPositivePolicy`).
* Boundary policies: over the closed simplex with `log 0 = -∞` and `σ(+∞) = 1`,
  the objective can equal `-∞` at a boundary policy, which then is an extended-real
  minimizer. Such a policy is induced by no real reward and no real `θ`, so the
  hypothesis `‖θ^{(t)}‖ ≤ r_max` (:209) fails for it. Either way Theorem 7.12 is
  ill-posed or vacuous, not false; its regret bound is neither transcribed nor
  refuted here.
* Prompts form a finite type `X` with distribution `ρ`, answers a finite type `Y`;
  the dataset is a list of comparisons `(x, y₊, y₋)`. The expectation over
  `x ∼ ρ, y ∼ π_cal(·|x)` is a finite sum.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

/-- The regularization strength `α` prescribed by Theorem 7.12
(`RLHF.tex:214`). -/
noncomputable def vpoAlpha (r_max β κ : ℝ) (d T : ℕ) : ℝ :=
  1 / Real.exp (2 * r_max + r_max / β) *
    Real.sqrt ((T : ℝ) / (κ * min ((d : ℝ) * Real.log T) (T : ℝ)))

/-- A conditional policy with full support: `π(·|x)` is a probability vector with
positive entries for every prompt `x`. -/
def IsPositivePolicy {X Y : Type} [Fintype Y] (π : X → Y → ℝ) : Prop :=
  (∀ x y, 0 < π x y) ∧ ∀ x, ∑ y, π x y = 1

/-- The online VPO objective (`RLHF.tex:194–198`) for a dataset `data` of
comparisons `(x, y₊, y₋)`:
`-∑ log σ(β log(π(y₊|x)/π_ref(y₊|x)) - β log(π(y₋|x)/π_ref(y₋|x)))
   + αβ E_{x∼ρ, y∼π_cal(·|x)}[log π(y|x) - log π_ref(y|x)]`. -/
noncomputable def vpoObjective {X Y : Type} [Fintype X] [Fintype Y] (ρ : X → ℝ)
    (π_ref π_cal : X → Y → ℝ) (α β : ℝ) (data : List (X × Y × Y)) (π : X → Y → ℝ) : ℝ :=
  -(data.map fun z ↦ Real.log (Real.sigmoid (β * Real.log (π z.1 z.2.1 / π_ref z.1 z.2.1) -
      β * Real.log (π z.1 z.2.2 / π_ref z.1 z.2.2)))).sum +
    α * β * ∑ x, ρ x * ∑ y, π_cal x y * (Real.log (π x y) - Real.log (π_ref x y))

/-- `π⋆` is a minimizer of the VPO objective over full-support policies. -/
def IsVPOMinimizer {X Y : Type} [Fintype X] [Fintype Y] (ρ : X → ℝ)
    (π_ref π_cal : X → Y → ℝ) (α β : ℝ) (data : List (X × Y × Y)) (πstar : X → Y → ℝ) :
    Prop :=
  IsPositivePolicy πstar ∧ ∀ π, IsPositivePolicy π →
    vpoObjective ρ π_ref π_cal α β data πstar ≤ vpoObjective ρ π_ref π_cal α β data π

/-- The online VPO update (`RLHF.tex:194–198`) is well defined: for every finite
instance with `α, β > 0` and every dataset, a minimizer exists. Theorem 7.12
presupposes this for its iterates `π^{(t)}`. -/
def VPOUpdate_exists_printed : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (α β : ℝ)
    (data : List (X × Y × Y)),
    0 < α → 0 < β → (∀ x, 0 ≤ ρ x) → ∑ x, ρ x = 1 →
    IsPositivePolicy π_ref → IsPositivePolicy π_cal →
    ∃ πstar, IsVPOMinimizer ρ π_ref π_cal α β data πstar

/-- Weaker: only the *first* online update `π^{(1)}` (iteration `t = 0`, empty
dataset, `RLHF.tex:188, 196`) is required to exist. Implied by
`VPOUpdate_exists_printed`. -/
def VPOFirstUpdate_exists_printed : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (α β : ℝ),
    0 < α → 0 < β → (∀ x, 0 ≤ ρ x) → ∑ x, ρ x = 1 →
    IsPositivePolicy π_ref → IsPositivePolicy π_cal →
    ∃ πstar, IsVPOMinimizer ρ π_ref π_cal α β [] πstar

end StatisticalRL.Ch7Rest.Rlhf
