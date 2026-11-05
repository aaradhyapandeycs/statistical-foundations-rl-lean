import Formalization.MDP.PolicyMatrixDefinitions
import Formalization.MDP.CoreDefinitions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source-facing statement index for Chapter 2. -/

open MeasureTheory
open scoped BigOperators Matrix

namespace StatisticalRL.Statements
universe u v

/-- `lem:variance-perturbation-var-P-V`, `chapters/prelim.tex:458–467`. -/
def Lemma2_2 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (V Vhat : State → ℝ),
    (∀ s, 0 ≤ V s ∧ V s ≤ 1 / (1 - M.discount)) →
    (∀ s, 0 ≤ Vhat s ∧ Vhat s ≤ 1 / (1 - M.discount)) →
    ‖(fun s a ↦ (M.transition s a).expectation (fun x ↦ Vhat x ^ 2) -
        ((M.transition s a).expectation Vhat) ^ 2) -
      (fun s a ↦ (M.transition s a).expectation (fun x ↦ V x ^ 2) -
        ((M.transition s a).expectation V) ^ 2)‖ ≤
      (4 / (1 - M.discount)) * ‖Vhat - V‖

/-- `lem:Freedman-prelim`, `chapters/prelim.tex:1056–1075`. The increments
are indexed from zero, corresponding to the source's indexing from one. -/
def Lemma2_9 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ),
    (∀ n, Measurable (X n)) →
    ∀ (B σ : ℝ),
    (∀ n ω, |X n ω| ≤ B) →
    (∀ n, μ[X n | ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (X k) (borel ℝ)]
      =ᵐ[μ] fun _ ↦ 0) →
    ∀ (n K : ℕ), 0 < K →
    (∀ ω, (∑ k ∈ Finset.range n,
      μ[fun ω' ↦ X k ω' ^ 2 |
        ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)] ω) ≤ σ ^ 2) →
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
    1 - δ ≤ μ.real {ω | |∑ k ∈ Finset.range n, X k ω| ≤
      Real.sqrt (8 * max (∑ k ∈ Finset.range n,
        μ[fun ω' ↦ X k ω' ^ 2 |
          ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)] ω)
        (σ ^ 2 / (2 : ℝ) ^ K) * Real.log (2 * K / δ)) +
        (4 / 3) * B * Real.log (2 * K / δ)}

/-- Azuma–Hoeffding Lemma 2.8, `lem:azuma-hoeffding`,
`chapters/prelim.tex:1038–1052`. The increments and deterministic bounds
are indexed from zero, corresponding to the printed indexing from one.
Each conditional mean is taken given exactly the preceding increments,
and is an almost-everywhere identity. No finite-space or standard-Borel
assumption, positive-time assumption or positive variance proxy is imposed.
-/
def Lemma2_8 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (B : ℕ → ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k ω, |X k ω| ≤ B k) →
    (∀ k, μ[X k | ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)]
      =ᵐ[μ] fun _ ↦ 0) →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    1 - δ < μ.real {ω | |∑ k ∈ Finset.range n, X k ω| ≤
      Real.sqrt (2 * (∑ k ∈ Finset.range n, (B k)^2) * Real.log (2/δ))}

/-- Lemma 2.3, `lem:basic-property-matrix-notation-inf`,
`chapters/prelim.tex:544–574`, for both policy transition matrices.
The matrix norm follows the book's explicit definition at
`chapters/intro.tex:204–209`: the maximum row-wise absolute sum. The Pi norm
below takes that maximum of the nonnegative row sums. Policies include all
stationary randomized policies, as defined at prelim.tex:66; discount zero is included.
-/
noncomputable def Lemma2_3 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action),
    letI := Classical.decEq State
    letI := Classical.decEq Action
    let P : Matrix State State ℝ := fun s t =>
      ∑ a, (π s).prob a * (M.transition s a).prob t
    let Q : Matrix (State × Action) (State × Action) ℝ := fun sa tb =>
      (M.transition sa.1 sa.2).prob tb.1 * (π tb.1).prob tb.2
    let γ := M.discount
    ((1 - γ • P)⁻¹ = 1 + ∑' n : ℕ, (γ • P)^(n + 1) ∧
      (1 - γ • P)⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1 / (1 - γ)) ∧
      ‖fun s => ∑ t, |((1 - γ • P)⁻¹) s t|‖ = 1 / (1 - γ) ∧
      ∀ s t, 0 ≤ ((1 - γ • P)⁻¹) s t) ∧
    ((1 - γ • Q)⁻¹ = 1 + ∑' n : ℕ, (γ • Q)^(n + 1) ∧
      (1 - γ • Q)⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1 / (1 - γ)) ∧
      ‖fun sa => ∑ tb, |((1 - γ • Q)⁻¹) sa tb|‖ = 1 / (1 - γ) ∧
      ∀ sa tb, 0 ≤ ((1 - γ • Q)⁻¹) sa tb)

end StatisticalRL.Statements
