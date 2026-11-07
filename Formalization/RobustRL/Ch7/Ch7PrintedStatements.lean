import Formalization.RobustRL.Ch7.Ch7Definitions

/-!
# Printed Theorems 7.2, 7.3, 7.4 as Lean propositions (definitions only)

Literal transcriptions of the printed statements in `chapters/robust_RL.tex`,
built on `Formalization.RobustRL.Ch7.Ch7Definitions`. They are stated so that they can be
refuted (see `HorizonTrap.lean`, `SingletonAction73.lean`); they are not claimed.

Representation choices (all of which can only make the printed claims *easier*
to satisfy, so a refutation is at least as strong as one of the literal text):
* `S = Fintype.card State`, `A = Fintype.card Action`, `γ = M.discount`; the
  state and action types are quantified in `Type`.
* `hN : 0 < N` is an extra binder in 7.2/7.4: the empirical kernel
  (`robust_RL.tex:206–212`) divides by `N`.
* The iteration count `T = C₁ log(N/(1-γ))` is not an integer in the source;
  it is passed through a rounding map `roundT : ℝ → ℕ`, which the refutations
  allow to be any map within distance `< 1` of the identity on `[0,∞)`
  (`RoundsReal`; floor, ceiling and nearest-integer rounding all qualify).
* The greedy tie rule (:254–258) is unspecified. `Thm7_2_printed` and
  `Thm7_4_printed` quantify over every greedy selector of `Q̂_T`; the weaker
  readings `Thm7_2_printed_existsTie` and `Thm7_4_printed_existsTie` only ask
  for *some* greedy selector (in particular any fixed tie rule) and are
  refuted separately.
-/

open MeasureTheory

namespace StatisticalRL.RobustRL.Ch7

local instance printedStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- A rounding map `ℝ → ℕ` within distance `< 1` of the identity on `[0, ∞)`. -/
def RoundsReal (roundT : ℝ → ℕ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → |(roundT y : ℝ) - y| < 1

/-- Printed Theorem 7.2, `thm:l1-upper-bound`, `chapters/robust_RL.tex:342–359`
(TV ball, DRVI = Algorithm `alg:cvi-dro-infinite` :264–289 after
`T = C₁ log(N/(1-γ))` iterations, :345), with the rounding of `T` given by
`roundT`. `C₁, C₂` are chosen before the instance (:358). -/
def Thm7_2_printed (roundT : ℝ → ℕ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy
          (empiricalDRVI tvBall M σ N hN data
            (roundT (C₁ * Real.log (N / (1 - M.discount))))) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy (pick data)) s ≤ ε}

/-- Existential tie-rule reading of `Thm7_2_printed`: the same hypotheses, but the
conclusion is only required for *some* greedy selector of `Q̂_T` (for example a
fixed tie rule). It is implied by `Thm7_2_printed` whenever a greedy selector exists. -/
def Thm7_2_printed_existsTie (roundT : ℝ → ℕ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      ∃ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy
          (empiricalDRVI tvBall M σ N hN data
            (roundT (C₁ * Real.log (N / (1 - M.discount))))) (pick data)) ∧
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy (pick data)) s ≤ ε}

/-- Printed Theorem 7.4, `thm:l2-upper-bound`, `chapters/robust_RL.tex:437–450`
(χ² ball, DRVI after `T = c₁ log(N/(1-γ))` iterations, :438), with the rounding
of `T` given by `roundT`. `c₁, c₂` are chosen before the instance (:449). -/
def Thm7_4_printed (roundT : ℝ → ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy
          (empiricalDRVI chiBall M σ N hN data
            (roundT (c₁ * Real.log (N / (1 - M.discount))))) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy (pick data)) s ≤ ε}

/-- Existential tie-rule reading of `Thm7_4_printed`: the same hypotheses, but the
conclusion is only required for *some* greedy selector of `Q̂_T` (for example a
fixed tie rule). It is implied by `Thm7_4_printed` whenever a greedy selector exists. -/
def Thm7_4_printed_existsTie (roundT : ℝ → ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      ∃ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy
          (empiricalDRVI chiBall M σ N hN data
            (roundT (c₁ * Real.log (N / (1 - M.discount))))) (pick data)) ∧
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy (pick data)) s ≤ ε}

/-- Printed Theorem 7.3, `thm:l1-lower-bound`, `chapters/robust_RL.tex:377–391`,
at a fixed constant `c₀`: for every tuple `(S, A, γ, σ, ε)` in the printed domain
and every `N` below the printed bound there are two RMDPs `M₀, M₁` (TV balls of
radius `σ`, discount `γ`, on the given `S` states and `A` actions) and an initial
distribution `μ` such that every data-to-stationary-policy estimator has
`max_i P_i(V_i^{⋆,σ}(μ) - V_i^{π̂,σ}(μ) > ε) ≥ 1/8`. Nonemptiness of the state
and action sets is assumed (`S = {1,…,S}`, `A = {1,…,A}`). -/
def Thm7_3_printed_at (c₀ : ℝ) : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
    (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt tvBall M₀ σ μ -
              robustPolicyValueAt tvBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt tvBall M₁ σ μ -
              robustPolicyValueAt tvBall M₁ σ (est data) μ})

/-- Printed Theorem 7.3 (`chapters/robust_RL.tex:377–391`) for every constant
`0 < c₀ ≤ 1/8` (:379, "with `0 < c₀ ≤ 1/8` being any small enough positive
constant"). The "sufficiently small `c₀`" reading is refuted separately by
`not_thm7_3_printed_small`. -/
def Thm7_3_printed : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 → Thm7_3_printed_at c₀

end StatisticalRL.RobustRL.Ch7
