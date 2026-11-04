import Formalization.MDP.CoreDefinitions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source-facing statement index for Chapter 2. -/

open MeasureTheory
open scoped BigOperators

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

end StatisticalRL.Statements
