# Source review: production robust Bellman contraction

## Hash-bound scope

Reviewed production files:

- `Formalization/ModelFree/QLearningRobustComparator.lean`, SHA-256
  `e5ce5615897b68911374e0b5f58aab1254f03fcae75d44040cc7f46f9b549661`.
- `Formalization/ModelFree/QLearningRobustContraction.lean`, SHA-256
  `5e3e0d1a9d495133dbd052af4c281a8ad2b9478866f5cfa1243735875a6cfab6`.

The source is arXiv:2610.41903v1,
`source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The exact target is Lemma `lemma:robust-Bellman-contraction` (Lemma 4.11 in
the paper), source inventory lines 1422–1438; the operator definitions are
`eq:Q-comparison-operator-plus` and `eq:Q-comparison-operator-minus`, lines
1401–1418, and its proof is at lines 1440–1469. This is a source/statement
review. It is not a fresh compile or transitive Lean axiom audit.

## Definitions, carriers, and premises

The production comparator uses finite state distributions. Its `qChiBall`
requires the finite χ² sum over positive nominal atoms to be at most `ρ` and
separately requires `q(x)=0` whenever `p(x)=0`. This matches the source
uncertainty set `eq:Q-comparison-ball` and its absolute-continuity support
restriction. The robust expectation image consists of actual expectations of
feasible rows, so the `sSup` and `sInf` are over the source set, not an
approximation or a selected optimizer.

The plus/minus operator definitions reproduce the source pointwise formulas:
same reward `r(s,a)`, same `γ`, same maximum-over-actions value `V_Q`, the
supremum/infimum over the same support-aware row ball, and the corresponding
`+b`/`−b` shift. The shift `b` is arbitrary in the Lean theorem; the source
has a particular nonnegative parameter choice. Since a constant shift
cancels in the operator difference, the generalized Lean parameter is
sound. The source specializes `ρ` to a positive value; Lean assumes only
`0≤ρ`, a sound extension that includes the boundary case. That premise is
used to establish the nominal row's feasibility and thus nonemptiness of the
robust expectation image.

The theorem is over finite `State` and `Action`. `DiscountedMDP` also supplies
nonempty state/action carriers, transition probability rows, rewards in
`[0,1]`, and `0≤discount<1`. Nonempty actions are needed to define the actual
finite maximum in `qLearningValue`; the reward bounds are inherited from the
model structure but are not used by this contraction argument. The discount
bounds support positivity of the multiplier and strict contraction. These
model assumptions are consistent with the finite discounted MDP setting of
the source.

## Proof route and statement coverage

The contraction draft proves a row expectation difference bound for each
fixed feasible row, using the finite distribution expectation bound and the
fact that the finite action maximum is 1-Lipschitz in the sup norm. It then
transfers that uniform bound to both supremum and infimum over the same
nonempty set. Finally it applies the two bounds row by row to the robust
Bellman operators. The pointwise bound is
`γ * ‖Q-R‖`; taking the nested finite Pi norms yields the source sup-norm
inequality for each operator. This is the same argument as the source proof's
row expectation inequality, elementary supremum comparison, and maximum over
`(s,a)`.

`qRobustBellman_contracting` returns `ContractingWith` for both operators.
Its Lipschitz fields imply both exact inequalities
`‖T⁺Q−T⁺R‖ ≤ γ‖Q−R‖` and
`‖T⁻Q−T⁻R‖ ≤ γ‖Q−R‖`; the additional strict field is `γ<1`, already
provided by the discounted MDP structure. The ambient Pi norm on a finite
function space is the maximum/sup norm used by the source. Thus the declaration
covers both inequalities in the named source lemma. It also packages the
discount strictness needed by the downstream Banach fixed-point theorem; it
does not assert compactness, attainment, or the χ² variance comparison.

## Verdict and remaining validation

The production definitions and `qRobustBellman_contracting` are source-faithful
for Lemma 4.11, including the support-aware uncertainty set, both operator
shifts, the finite sup norm, both signs, and all hypotheses required by the
proof. No source mismatch or extra proof premise was found. This verdict is
limited to statement and mathematical-source correspondence. It does not
certify current production compilation, imported transitive axioms, or the
separate fixed-point and later comparator claims; those require the project's
compiler and axiom checks.

## Production integration

The reviewed production declarations now pass the full project compilation and transitive axiom audit. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
