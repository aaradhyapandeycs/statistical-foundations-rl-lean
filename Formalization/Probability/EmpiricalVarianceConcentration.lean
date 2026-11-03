import Formalization.Probability.EmpiricalVarianceBernstein

/-!
# Concentration of empirical row variance

A two-moment Hoeffding bound on the genuine iid row experiment. This does not
assert the sharper empirical Bernstein confidence radius in the source.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance varianceConcentrationStateMeasurable : MeasurableSpace State := ⊤

/-- A two-sided exponential tail for the actual frequency-row variance.
The bound uses concentration of first and second empirical moments. -/
theorem empiricalVariance_hoeffding (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (V : State → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 ≤ ε)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ |empiricalVariance N hN V ω - d.variance V|} ≤
      2 * Real.exp (-2 * (N : ℝ) * (ε / 2) ^ 2 / (B ^ 2) ^ 2) +
      2 * Real.exp (-2 * (N : ℝ) * (ε / (4 * B)) ^ 2 / B ^ 2) := by
  let A : Set (Fin N → State) := {ω | ε / 2 ≤
    |(empiricalRow N hN ω).expectation (fun s ↦ V s ^ 2) -
      d.expectation (fun s ↦ V s ^ 2)|}
  let C : Set (Fin N → State) := {ω | ε / (4 * B) ≤
    |(empiricalRow N hN ω).expectation V - d.expectation V|}
  have hsquare (s : State) : V s ^ 2 ∈ Set.Icc 0 (B ^ 2) := by
    constructor
    · positivity
    · nlinarith [(hV s).1, (hV s).2]
  have hfirst := d.empiricalRow_hoeffding (fun s ↦ V s ^ 2) N hN (B ^ 2) (ε / 2)
    (sq_pos_of_pos hB) hsquare (by positivity)
  have hsecond := d.empiricalRow_hoeffding V N hN B (ε / (4 * B)) hB hV (by positivity)
  have hsubset : {ω : Fin N → State | ε ≤ |empiricalVariance N hN V ω - d.variance V|} ⊆
      A ∪ C := by
    intro ω hω
    by_contra hout
    have ha : |(empiricalRow N hN ω).expectation (fun s ↦ V s ^ 2) -
        d.expectation (fun s ↦ V s ^ 2)| < ε / 2 := by
      have : ω ∉ A := fun ha ↦ hout (Set.mem_union_left C ha)
      exact lt_of_not_ge this
    have hc : |(empiricalRow N hN ω).expectation V - d.expectation V| < ε / (4 * B) := by
      have : ω ∉ C := fun hc ↦ hout (Set.mem_union_right A hc)
      exact lt_of_not_ge this
    have hbound := d.empiricalVariance_abs_sub_le N hN V B hV ω
    have hmul : 2 * B * |(empiricalRow N hN ω).expectation V - d.expectation V| < ε / 2 := by
      have hp := (lt_div_iff₀ (by positivity : 0 < 4 * B)).mp hc
      nlinarith
    change ε ≤ |empiricalVariance N hN V ω - d.variance V| at hω
    linarith
  calc
    _ ≤ (d.sampleMeasure N).real (A ∪ C) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ (d.sampleMeasure N).real A + (d.sampleMeasure N).real C := measureReal_union_le _ _
    _ ≤ _ := add_le_add hfirst hsecond

/-- The empirical variance gives a one-sided upper confidence bound on the
true variance, with an explicit exponential failure bound. -/
theorem variance_upper_confidence_hoeffding (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (V : State → ℝ) (B ε : ℝ)
    (hB : 0 < B) (hε : 0 ≤ ε) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | empiricalVariance N hN V ω + ε < d.variance V} ≤
      2 * Real.exp (-2 * (N : ℝ) * (ε / 2) ^ 2 / (B ^ 2) ^ 2) +
      2 * Real.exp (-2 * (N : ℝ) * (ε / (4 * B)) ^ 2 / B ^ 2) := by
  calc
    _ ≤ (d.sampleMeasure N).real {ω | ε ≤ |empiricalVariance N hN V ω - d.variance V|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change empiricalVariance N hN V ω + ε < d.variance V at hω
      change ε ≤ |empiricalVariance N hN V ω - d.variance V|
      have h := neg_le_abs (empiricalVariance N hN V ω - d.variance V)
      linarith
    _ ≤ _ := d.empiricalVariance_hoeffding N hN V B ε hB hε hV

end StatisticalRL.FiniteDistribution
