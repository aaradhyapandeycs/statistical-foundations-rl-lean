import Formalization.Probability.GaussianConvexShell
import Formalization.Analysis.ConvexSmoothIndicator

/-!
# Compatibility of the smooth sandwiches with the Gaussian convex shell

Infrastructure (not a source result) for the all-convex-sets route to `thm:Berry-Esseen-linear`
(`chapters/inference.tex:132–141`). It connects milestone M2 (`ConvexSmoothIndicator`) with
milestone M1 (`GaussianConvexShell`): the two regions where a smooth sandwich of `1_K` can differ
from `1_K` lie in the `ε`-shell `cthickening ε K ∩ cthickening ε (interior K)ᶜ` of `K`, whose
Gaussian mass M1 bounds for convex `K`.

* `thickening_diff_subset_convexShell`: the upper excess region `thickening ε K \ K`;
* `diff_innerParallel_subset_convexShell`: the lower deficit region `K \ {x | closedBall x ε ⊆ K}`.

Neither needs convexity.
-/

open Metric Set

namespace StatisticalRL.Probability.ConvexSandwichShell

variable {ι : Type*} [Fintype ι]

/-- The upper excess region `thickening ε K \ K` lies in the `ε`-shell of `K`. -/
theorem thickening_diff_subset_convexShell (K : Set (ι → ℝ)) {ε : ℝ} (_hε : 0 ≤ ε) :
    thickening ε K \ K ⊆ cthickening ε K ∩ cthickening ε (interior K)ᶜ := by
  rintro x ⟨hx, hxK⟩
  exact ⟨thickening_subset_cthickening _ _ hx,
    self_subset_cthickening _ (fun h => hxK (interior_subset h))⟩

/-- The lower deficit region `K \ {x | closedBall x ε ⊆ K}` lies in the `ε`-shell of `K`. -/
theorem diff_innerParallel_subset_convexShell (K : Set (ι → ℝ)) (ε : ℝ) :
    K \ {x | closedBall x ε ⊆ K} ⊆ cthickening ε K ∩ cthickening ε (interior K)ᶜ := by
  rintro x ⟨hxK, hx⟩
  refine ⟨self_subset_cthickening _ hxK, ?_⟩
  simp only [mem_setOf_eq, not_subset] at hx
  obtain ⟨y, hy, hyK⟩ := hx
  exact mem_cthickening_of_dist_le x y ε _ (fun h => hyK (interior_subset h))
    (by rw [dist_comm]; exact mem_closedBall.1 hy)

end StatisticalRL.Probability.ConvexSandwichShell
