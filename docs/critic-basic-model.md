# Independent source review: foundational discounted MDP and Bellman operators

**Verdict: PASS for the finite probability/model definitions, stated Bellman
operators, and the two source Q-operator contraction inequalities in
`Formalization/MDP/Basic.lean`.** This is a scoped source and declaration
review; the file alone does not prove trajectory interpretation or existence of
Bellman fixed points.

## Source reconstruction

`prelim.tex` lines 31–52 gives finite state and action spaces, stationary
transition rows `P(·|s,a) ∈ Δ(S)`, deterministic `r(s,a) ∈ [0,1]` and
`γ ∈ [0,1)`. Lines 63–73 define an arbitrary randomized stationary policy
and the induced state transition row as the policy-weighted mixture of the
original action-conditioned rows. Lines 190–197, 210–223 and 233–239 define
respectively policy Q-Bellman, policy state-value Bellman and optimal Q-Bellman
operators by the displayed nested finite expectations and action maximum.
Lines 251–260 assert the policy and optimal Q operators are γ-contractions in
the finite supremum norm. The source independently defines V and Q as
infinite-trajectory expected returns (lines 89–123); these definitions and the
claim they solve the Bellman equations are mathematically distinct from the
operator formulas and their contraction bounds.

## Expanded definitions and findings

1. `FiniteDistribution Ω` has `prob : Ω → ℝ`, nonnegative masses at every
   point, and total finite sum exactly one. These are the usual finite simplex
   conditions, and together imply every individual mass is at most one. The
   type does not explicitly store nonemptiness, but no value can satisfy its
   normalization on an empty finite carrier. Its `expectation` is the actual
   finite weighted sum, and `bind` proves normalization and nonnegativity for
   the mixture. No arbitrary measure, hidden stochasticity premise, or
   pre-assumed Bellman equation is bundled.
2. `DiscountedMDP` carries finite `State` and `Action` instances plus explicit
   nonempty witnesses, one normalized transition vector for every state/action,
   deterministic real rewards with both source bounds, and the exact
   `0 ≤ discount < 1` endpoints. The abstract finite types are more general
   than source labels `{1,…,S}` and `{1,…,A}` up to finite relabeling; the file
   does not introduce separate numerical cardinal parameters. The action
   nonemptiness ensures `actionMaximum` is a true attained finite maximum,
   rather than a default value for an empty action set. The source assumes a
   known reward as learner information; storing a reward field represents the
   function but does not itself encode an algorithm's information access.
3. `StationaryPolicy` assigns each state an actual normalized finite action
   distribution. `policyTransition` binds that distribution to the current
   state's action-specific transition; `policyTransition_prob` exposes
   `Σ_a π(a|s)P(t|s,a)`, matching source `eq:defn-P-s-pi-inf`. The mixture does
   not interchange current and next states or actions.
4. `qBellman`, `valueBellman` and `qOptimality` match the cited source
   formulas, including reward position, γ multiplier, action/next-state order,
   and optimal action maximum at the **next** state. The state-value operator
   uses the normalized mixture in item 3; linearity of its finite expectation
   yields the source's two nested sums. No positive lower bound on probabilities
   or discount is assumed, and `γ=0` is allowed.
5. The pointwise contraction lemmas use normalized finite weighted
   expectations and the nonexpansive true action maximum. The exported
   `norm_qBellman_sub_le` and `norm_qOptimality_sub_le` state exactly the two
   source inequalities with factor γ. `norm_valueBellman_sub_le` also proves
   the analogous state-value contraction, a valid additional result. Mathlib's
   finite Pi norm is a supremum over component norms, nested for
   `State → Action → ℝ`; an independent compiled probe established
   `‖Q‖ ≤ c ↔ ∀ s a, |Q s a| ≤ c` for `c ≥ 0`. This is the source finite
   ℓ∞ norm, not an ℓ1 or ℓ2 norm. A second probe checked that at `γ=0` both
   Q operators return the immediate reward for every Q.
6. `qBellman_fixedpoint_unique` and `qOptimality_fixedpoint_unique` prove
   **at most one** fixed point from the contraction. Their fixed-point
   hypotheses are legitimate uniqueness premises, not assumed trajectory or
   source-value facts. The inequalities do not by themselves construct a
   fixed point. The source's prose says operators bring two Q-functions
   strictly closer; mathematically the strict comparison is for distinct
   inputs, since identical inputs have distance zero. The formal inequalities
   and uniqueness proof use the correct non-strict bound and `γ<1`.

## Scope limits

`Basic.lean` defines operators and proves their contraction and uniqueness;
it does not by itself construct their fixed points, prove that the source's
infinite expected-trajectory V or Q satisfies those fixed-point equations, or
establish existence of an optimal policy. Those are separate module and
integration obligations. In particular this review does not make any new
claim about completion of the full source Bellman equations, the whole
preliminaries chapter, or the monograph.

## Checks and identity

Using the integrated module, a temporary probe compiled with
`bash scripts/lean-local.sh <temporary-probe>` and checked
the nested Pi-norm and `γ=0` consequences above. `#print axioms` for
`FiniteDistribution.bind`, `policyTransition`, `norm_qBellman_sub_le`,
`norm_valueBellman_sub_le`, `norm_qOptimality_sub_le`,
`qBellman_fixedpoint_unique`, and `qOptimality_fixedpoint_unique` reported
only `propext`, `Classical.choice`, and `Quot.sound`. The probe was removed.
This uses the integrated module's existing build artifact; it is not an
independent clean or full integration build.

SHA-256:

- `Formalization/MDP/Basic.lean`: `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`
