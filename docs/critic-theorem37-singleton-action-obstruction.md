# Source review: singleton-action obstruction for Theorem 3.7(i)

The [Lean construction](../Formalization/Obstructions/Theorem37SingletonAction.lean)
is a counterexample under a standalone reading of the theorem's displayed
domain. The theorem requires `SA ≥ 16` but does not restate `A ≥ 2`. The
preceding policy-learning section does state `A ≥ 2`, and whether that
convention carries into the separate minimax-lower-bounds section remains
unresolved. This is not an author-approved correction or a claim about the
authors' intended scope.

The witness takes `S=16`, `A=1`, `N=1`, and `γ=2/3`. The actual product
sampling law has one independent transition draw per state-action pair. A
constant estimator selects the only action, so its actual infinite-trajectory
Q-function equals the optimal policy's Q-function for every compatible model
and dataset. Its strict error event is therefore empty under every such
sampling law. The parameter construction supplies a positive accuracy that
satisfies the printed restrictions and sample bound for each positive `c_N`.

The quantifiers matter: one estimator works for every compatible model, so
the obstruction does not depend on choosing a single convenient model. It
does not show that the theorem fails on the authors' intended nondegenerate
domain, nor does it formalize the full minimax theorem.

An isolated compile of the project-layout module and a 15-export axiom probe
passed, with only `propext`, `Classical.choice`, and `Quot.sound` among their
axioms. The isolated check used pinned prebuilt dependencies. Both the
working-tree and separate clean-copy integrations then passed on identical
source hashes, compiling 386 project modules and auditing 4,633 project
declarations for transitive axioms.
