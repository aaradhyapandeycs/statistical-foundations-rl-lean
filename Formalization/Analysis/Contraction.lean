import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contraction infrastructure for value iteration

This is metric-space infrastructure for the argument in Chapter 2,
`prelim.tex`, linear convergence of VI and PI. It does not itself establish
Bellman optimality, the expected-return interpretation, or policy iteration.
-/

namespace StatisticalRL.Analysis

open scoped NNReal

variable {X : Type*} [MetricSpace X] {K : ℝ≥0} {f : X → X}

/-- Iterating a Lipschitz map shrinks the distance to any of its fixed points.
The RL application must separately prove the Bellman map's Lipschitz property
and identify its fixed point with the optimal expected return. -/
theorem iterate_dist_le (hf : LipschitzWith K f) {target : X}
    (htarget : f target = target) (initial : X) (n : ℕ) :
    dist (f^[n] initial) target ≤ (K : ℝ) ^ n * dist initial target := by
  have hfixed : f^[n] target = target := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, htarget]
  simpa only [hfixed, NNReal.coe_pow] using (hf.iterate n).dist_le_mul initial target

/-- Uniqueness of a contraction's fixed point, before introducing any chosen
fixed-point object. -/
theorem contraction_fixed_unique (hf : ContractingWith K f) {x y : X}
    (hx : f x = x) (hy : f y = y) : x = y :=
  hf.fixedPoint_unique' hx hy

/-- Existence and uniqueness use completeness, rather than assuming the
existence of the value-function object as an extra theorem premise. -/
theorem contraction_exists_unique [Nonempty X] [CompleteSpace X]
    (hf : ContractingWith K f) : ∃! x, f x = x := by
  refine ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hf.fixedPoint_unique hy

end StatisticalRL.Analysis
