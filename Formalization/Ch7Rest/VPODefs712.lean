import Formalization.Ch7Rest.RlhfPrinted712
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Corrected Theorem 7.12 (online VPO): definitions

Source: `chapters/RLHF.tex`. Bradley–Terry model :24–28, negative log-likelihood :31–39,
KL-regularized value :41–47, Gibbs closed form :52–59, calibrated value :92–96, `J⋆` as a
maximum :99–102, VPO objective :109–113, linear rewards (`assump:linear`) :146–153, online
procedure :158–177, Algorithm `alg:online_RBMLE` :182–203, Theorem 7.12 (`thm_online`) :208–215.

Definitions only (no proofs), for the statement index.

* Prompts `X` and answers `Y` are finite types; `ρ` is a probability vector on `X`.
* Features `φ : X → Y → ℝ^d` (`EuclideanSpace ℝ (Fin d)`), linear rewards `r_θ = ⟪φ, θ⟫`.
* `gibbsPolicy π_ref r β` is `π_r(y|x) ∝ π_ref(y|x) exp(r(x,y)/β)` (:52–59).
* `calValue` is `J(r, π; π_cal)` (:92–96) with `KL(p‖q) = ∑ p log(p/q)` (Lean's `log 0 = 0`
  gives the convention `0 log 0 = 0`); `optCalValue` is its supremum over all conditional
  policies with rows in the closed simplex (:99–102).
* One round produces `ω = (x, y₁, y₂, o) ∈ X × Y × Y × Bool`; `o = true` means `y₁ ≻ y₂`. The
  recorded comparison is `compRecord ω = (x, y₊, y₋)`.
* `vpoData h k` is the dataset of rounds `j < k` (0-indexed; round `j` is the source's round
  `j + 1`, so `vpoData h k` is `D^{(k)}`, :162, :196). The policy of 0-indexed round `k` is the
  source's `π^{(k+1)} = π_{θ}` with `θ = sel (D^{(k)})`.
* `vpoTrajWeight` is the law of the `T` rounds: `x ∼ ρ`, `y₁, y₂ ∼ π^{(t)}(·|x)` independently,
  `o` from the Bradley–Terry oracle with reward `r_{θ⋆}` (:190, :24–27).
* `vpoRegret` is `∑_{t=1}^{T} [J⋆(r⋆; π_cal) − J(r⋆, π^{(t)}; π_cal)]` (:211–213).
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset

section Defs

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

/-- Linear reward `r_θ(x,y) = ⟪φ(x,y), θ⟫` (`assump:linear`, `RLHF.tex:146–153`). -/
noncomputable def linReward (φ : X → Y → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (x : X) (y : Y) : ℝ :=
  inner ℝ (φ x y) θ

/-- Gibbs policy `π_r(y|x) = π_ref(y|x) exp(r(x,y)/β) / ∑_{y'} π_ref(y'|x) exp(r(x,y')/β)`
(`RLHF.tex:52–59`). -/
noncomputable def gibbsPolicy (π_ref r : X → Y → ℝ) (β : ℝ) (x : X) (y : Y) : ℝ :=
  π_ref x y * Real.exp (r x y / β) / ∑ y', π_ref x y' * Real.exp (r x y' / β)

/-- `π` is a conditional policy: every row is in the closed probability simplex. -/
def IsCondPolicy (π : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ π x y) ∧ ∀ x, ∑ y, π x y = 1

/-- `KL(p‖q) = ∑_y p(y) log(p(y)/q(y))` (with `0 log 0 = 0`). -/
noncomputable def klDiv (p q : Y → ℝ) : ℝ :=
  ∑ y, p y * Real.log (p y / q y)

/-- Calibrated value `J(r, π; π_cal) = E_{x∼ρ}[E_{y∼π(·|x)} r(x,y) − β KL(π(·|x)‖π_ref(·|x))]
− E_{x∼ρ, y∼π_cal(·|x)} r(x,y)` (`RLHF.tex:92–96`). -/
noncomputable def calValue (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ) (r π : X → Y → ℝ) :
    ℝ :=
  ∑ x, ρ x * (∑ y, π x y * r x y - β * klDiv (π x) (π_ref x)) -
    ∑ x, ρ x * ∑ y, π_cal x y * r x y

/-- `J⋆(r; π_cal) = max_π J(r, π; π_cal)` (`RLHF.tex:99–102`), as the supremum over all
conditional policies. -/
noncomputable def optCalValue (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ) (r : X → Y → ℝ) :
    ℝ :=
  sSup {v | ∃ π, IsCondPolicy π ∧ calValue ρ π_ref π_cal β r π = v}

/-- A ball-constrained VPO selection rule: for every dataset `D`, `sel D` lies in the ball
`‖θ‖ ≤ R` and its Gibbs policy minimizes the printed VPO objective (`RLHF.tex:194–198`,
`vpoObjective`) over the Gibbs policies `π_θ` with `‖θ‖ ≤ R`. -/
def IsBallSelection (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d))
    (α β R : ℝ) (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ D, ‖sel D‖ ≤ R ∧ ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R →
    vpoObjective ρ π_ref π_cal α β D (gibbsPolicy π_ref (linReward φ (sel D)) β) ≤
      vpoObjective ρ π_ref π_cal α β D (gibbsPolicy π_ref (linReward φ θ) β)

/-- The recorded comparison `(x, y₊, y₋)` of a round outcome `ω = (x, y₁, y₂, o)`. -/
def compRecord (ω : X × Y × Y × Bool) : X × Y × Y :=
  if ω.2.2.2 then (ω.1, ω.2.1, ω.2.2.1) else (ω.1, ω.2.2.1, ω.2.1)

/-- Bradley–Terry probability of the recorded preference: `σ(r(x,y₊) − r(x,y₋))`
(`RLHF.tex:24–28`). -/
noncomputable def prefProb (r : X → Y → ℝ) (ω : X × Y × Y × Bool) : ℝ :=
  Real.sigmoid (r (compRecord ω).1 (compRecord ω).2.1 - r (compRecord ω).1 (compRecord ω).2.2)

/-- Dataset of the rounds `j < k`, in order. -/
def vpoData {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) : List (X × Y × Y) :=
  ((List.finRange T).filter (fun j ↦ decide (j < k))).map (fun j ↦ compRecord (h j))

/-- Policy used in round `k` (0-indexed): the Gibbs policy of `sel (vpoData h k)`. -/
noncomputable def roundPolicy (π_ref : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d)) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) : X → Y → ℝ :=
  gibbsPolicy π_ref (linReward φ (sel (vpoData h k))) β

/-- Probability of outcome `ω` in round `k` given the history `h` (only `h j`, `j < k`, matter):
`ρ(x) π(y₁|x) π(y₂|x) σ(r⋆(x,y₊) − r⋆(x,y₋))`. -/
noncomputable def roundKernel (ρ : X → ℝ) (π_ref : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d)) {T : ℕ} (k : Fin T)
    (h : Fin T → X × Y × Y × Bool) (ω : X × Y × Y × Bool) : ℝ :=
  ρ ω.1 * roundPolicy π_ref φ β sel h k ω.1 ω.2.1 * roundPolicy π_ref φ β sel h k ω.1 ω.2.2.1 *
    prefProb (linReward φ θstar) ω

/-- Probability of the trajectory `h` of `T` rounds of online VPO. -/
noncomputable def vpoTrajWeight (ρ : X → ℝ) (π_ref : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d)) {T : ℕ} (h : Fin T → X × Y × Y × Bool) :
    ℝ :=
  ∏ k, roundKernel ρ π_ref φ θstar β sel k h (h k)

/-- Realized regret `∑_{t=1}^{T} [J⋆(r⋆; π_cal) − J(r⋆, π^{(t)}; π_cal)]`. -/
noncomputable def vpoRegret (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d)) {T : ℕ} (h : Fin T → X × Y × Y × Bool) :
    ℝ :=
  ∑ k, (optCalValue ρ π_ref π_cal β (linReward φ θstar) -
    calValue ρ π_ref π_cal β (linReward φ θstar) (roundPolicy π_ref φ β sel h k))

/-- `κ = sup_{x,y} π_cal(y|x)/π_ref(y|x)` (`RLHF.tex:214`). -/
noncomputable def vpoKappa (π_ref π_cal : X → Y → ℝ) : ℝ :=
  ⨆ p : X × Y, π_cal p.1 p.2 / π_ref p.1 p.2

end Defs

end StatisticalRL.Ch7Rest.Rlhf
