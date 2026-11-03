# Source review: pointwise χ² weak duality

The [Lean result](../Formalization/RobustRL/ChiSquaredWeakDuality.lean) proves
that, for every finite nominal row `p`, feasible row `q`, value vector `V`,
and clipping threshold `α`, the nominal expectation of `min(V, α)` minus
`sqrt(σ Varₚ(min(V, α)))` is at most the expectation of `V` under `q`.
The feasible ball uses the source orientation χ²(`q`‖`p`) and requires
`q` to vanish outside the nominal support.

The result follows from the existing support-aware χ² expectation bound and
the pointwise inequality `min(V, α) ≤ V`. It is valid for arbitrary real
thresholds and value vectors; these generalize the source's restricted
interval and nonnegative value vector for this one direction. The active
source macro `\ror` expands to `\sigma`, so the radius in the feasible ball
and the scalar objective is the same. See the χ² branch of
[`lemma:dual-form`](../source/upstream/tex/chapters/robust_RL.tex#L303).

The [weak bridge](../Formalization/RobustRL/ChiSquaredPrimalDualWeakBridge.lean)
also compares the supremum over the source interval to the infimum over
feasible rows; its focused, working-tree and clean-copy compilation and
axiom checks passed. Neither result establishes the reverse
inequality, attainment of the scalar maximum, or the full source equality.
Before the bridge was added, the pointwise theorem's focused axiom probe
passed, and working-tree and separate clean-copy checks compiled all 384
then-current project Lean modules on identical source hashes. Subsequent
working-tree and clean-copy checks including the bridge compiled 386 modules
and audited 4,633 declarations, allowing only `propext`, `Classical.choice`,
and `Quot.sound`.
