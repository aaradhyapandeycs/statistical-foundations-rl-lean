# Source review: singleton-action obstruction for the robust χ² lower bound

The [counterexample module](../Formalization/RobustRL/SingletonActionCounterexample.lean)
addresses the displayed domain of Theorem 7.5 in
[`robust_RL.tex`](../source/upstream/tex/chapters/robust_RL.tex#L461). It is
counterevidence for a literal reading of the theorem, not a formalization of
the complete theorem or an author-approved correction. The theorem does not
explicitly exclude `A=1`; whether a wider standing dimension convention was
intended remains a source interpretation question.

The witness fixes `S=2`, `A=1`, `γ=3/4`, `ρ=1`, and `N=1`. For arbitrary
positive source constants `c₃,c₄`, it chooses
`ε=min(4c₃, sqrt(320c₄))`. This is positive and satisfies both the displayed
accuracy condition and the sample-size upper bound. The module constructs
two distinct nominal models with the same known reward and discount and
defines the actual product of their nominal transition-row sampling laws;
it proves the marginal and independence properties of those samples.

In the represented stationary randomized policy class, every policy on a
singleton action space is identical. The robust optimal value therefore
equals the value of every estimator output. One fixed estimator has zero
strict-error risk for every pair of robust models and every initial
distribution on the witness state space. The source theorem chooses its own
pair of models, so this uniformity matters. The module does not encode the
complete infimum over the manuscript's estimator class; the connection from
that class to this represented policy interface remains explicit.

The renamed candidate and an eleven-export axiom probe compiled in a fresh
isolated output. Each export used only `propext`, `Classical.choice`, and
`Quot.sound`. The focused run checked and copied 23 existing project OLeans,
but did not independently rebuild those dependencies from source or hash all
package artifacts. Both the working-tree and separate clean-copy integrations
then passed on identical hashes for all 382 project Lean sources. Each full
check compiled all 382 modules and audited 4,581 project declarations for
transitive axioms, allowing only the three standard axioms above.
