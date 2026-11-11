import Formalization.RobustRL.LowerBounds.Ch7PrintedStatements

/-!
# Corrected Theorems 7.2 and 7.4 as propositions (definitions only)

Library forms of the corrected DRVI upper bounds; proved in
`Formalization/RobustRL/DRVI/Thm72Main.lean` and `Thm74Main.lean` with `C₁ = c₁ = 2`,
`C₂ = c₂ = 10⁶`. The statement index (`Formalization/Statements/Ch7.lean`) restates them in full.
Not covered: the oracle-planner remarks (`robust_RL.tex:361–372`, `:453–457`) and
history-dependent policies (the policy class is stationary, as in `Ch7Definitions`).
-/

open MeasureTheory

namespace StatisticalRL.RobustRL.Ch7

local instance correctedStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Corrected Theorem 7.2, `thm:l1-upper-bound`, `chapters/robust_RL.tex:342–359` (TV ball,
DRVI = Algorithm `alg:cvi-dro-infinite`, `:264–289`). Differs from the printed statement
(`Thm7_2_printed`) only in the iteration count: instead of `T = C₁ log(N/(1−γ))` (`:345`), DRVI
may be run for any number of iterations `T ∈ ℕ` with `T ≥ C₁ log(N/(1−γ))/(1−γ)`
(`docs/SOURCE-ISSUES.md#C37`). This is a minimal edit of the printed formula: the factor
`1/(1−γ)` is necessary (C37 horizon trap), but tightness of the `log(N/(1−γ))` factor is not
shown. All other hypotheses, the constants' quantifier order (`:358`), the ranges, the sample
bound (`:353–355`) and the conclusion are as printed; every greedy selector of `Q̂_T` is allowed
(the tie rule is unspecified, `:254–258`); `hN : 0 < N` as in the printed transcription.
Proved with `C₁ = 2`, `C₂ = 10⁶`. -/
def Thm7_2_corrected : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      ∀ T : ℕ, C₁ * Real.log (N / (1 - M.discount)) / (1 - M.discount) ≤ T →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy (empiricalDRVI tvBall M σ N hN data T) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy (pick data)) s ≤ ε}

/-- Corrected Theorem 7.4, `thm:l2-upper-bound`, `chapters/robust_RL.tex:437–450` (χ² ball,
support-aware). Differs from the printed statement (`Thm7_4_printed`) only in the iteration
count: any `T ∈ ℕ` with `T ≥ c₁ log(N/(1−γ))/(1−γ)` instead of `T = c₁ log(N/(1−γ))` (`:438`;
`docs/SOURCE-ISSUES.md#C37`). Minimal edit of the printed formula; tightness of the log factor is
not shown. All other hypotheses (`:445–447`), the constants (`:449`) and the conclusion are as
printed; every greedy selector of `Q̂_T` is allowed; `hN : 0 < N` as in the printed
transcription. Proved with `c₁ = 2`, `c₂ = 10⁶`. -/
def Thm7_4_corrected : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      ∀ T : ℕ, c₁ * Real.log (N / (1 - M.discount)) / (1 - M.discount) ≤ T →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy (empiricalDRVI chiBall M σ N hN data T) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy (pick data)) s ≤ ε}

end StatisticalRL.RobustRL.Ch7
