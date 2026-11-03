# Source counterexample audit: Theorem 3.7 with one state

**Finding (high confidence):** Under the explicit v1 theorem and the monograph's known-reward model, both parts of Theorem 3.7 have the one-state counterexample below. This is a paper-level mathematical finding, not an author-approved erratum or a completed Lean refutation. No hidden numerical `S ≥ 2` standing assumption was found in the source materials checked. An assumption that S is asymptotically large would exclude the example if made into a binding domain restriction, but the source's informal focus on large quantities does not specify such a threshold or say it overrides the theorem's explicit size condition.

**Independence disclosure:** This reviewer previously wrote `docs/critic-one-state-review.md` and implemented `Formalization/Obstructions/OneState.lean`. This report independently rechecks source, estimator domain, measurability and quantifiers, but it is not an independent certification of that implementation. `docs/critic-one-state-lean-review.md` is the separate implementation review. I also inspected `docs/critic-finite-optimal.md`, `docs/critic-finite-occupancy.md`, and `docs/critic-discounted-finite.md` and the corresponding implementation interfaces; their scoped results do not close the infinite-trajectory or statistical experiment gaps below.

## Source and accessible revision check

- The pinned raw TeX for `prelim.tex` lines 31–45 has finite state and common finite action carriers; the transition is a normalized state distribution, the stationary reward `r : S × A → [0,1]` is deterministic and fully known a priori, and `γ ∈ [0,1)`. Lines 51–59 assume stationarity and describe a *focus* on large S, A, and effective horizon without a quantitative bound. Policy and infinite-trajectory definitions are at lines 63–76 and 89–140. In particular Q fixes the initial action, then follows a policy; the stated optimal policy dominates at all state-action pairs.
- The model-based chapter lines 11–31 describes independent transition queries, repeats that rewards are fully known unless otherwise noted, and does not exclude a singleton state. Section 3.3's policy-learning introduction says `A ≥ 2` at line 787; the construction here takes `A = 16`. The later minimax section starts at 1438, and Theorem `theorem:azar` at 1443–1464 explicitly says `SA ≥ 16`, with no `S ≥ 2` or exception to known rewards. I searched the preliminaries and this chapter for state-size restrictions and relevant language; no applicable numerical standing condition was found. A local two-state *example* at line 1540 introduces a particular family in the proof, not a stated universal prerequisite.
- The pinned TeX hashes match `source/provenance.json`: model-based chapter `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`; preliminaries `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. The accessible [v1 PDF](https://arxiv.org/pdf/2610.41903v1), printed pages 47–48, agrees with the theorem's displayed parameter range, cardinality, and (i)–(ii) quantifiers.
- The [official arXiv record](https://arxiv.org/abs/2610.41903), checked 2026-11-02, displays only submission v1, 30 October 2026. The public arXiv record and the checked [author publication page](https://yuejiechi.github.io/publications.html) did not identify an erratum for this work. This limited public-source check cannot rule out unpublished, separately posted, later, or otherwise undiscovered corrections. No author was contacted. The pinned v1 remains the target regardless.

## Inputs, estimator and its admissibility

Fix a one-element state carrier `{s}` and the indexed common action carrier `{1,…,16}`. An admissible model supplies `r(s,·) ∈ [0,1]^16`, fixed known `γ ∈ [2/3,1)`, and transition distributions `P(·|s,a)`. As a distribution on a singleton, each transition is necessarily the point mass at s. The queried dataset has N samples per action; all observed next states are s. Even though these random variables are degenerate, their product law makes them independent. The reward table is known to the learner for the actual MDP, even when the theorem's existential MDP varies it; the estimator can therefore be one common rule that accepts that table as an input.

Define the single deterministic rule, on every known reward table r, every allowed γ, and every dataset D, by

```text
m(r) = max_{1 ≤ b ≤ 16} r(s,b)
Qhat(r, γ, D)(s,a) = r(s,a) + γ m(r)/(1−γ).
```

It never consults an unobserved transition kernel or Q*, and never changes its algorithm according to the adversary's model. It is the same formula for all reward tables, γ, and data. For a fixed MDP, this is a constant function of D, hence measurable for the finite product sample σ-algebra. If r and γ are themselves included as observed inputs, the finite maximum and arithmetic make the rule continuous (therefore Borel measurable) on `[0,1]^16 × [2/3,1)`; it is also measurable jointly with the discrete dataset. This mathematical measurability statement is not yet a Lean theorem in the project.

For part (i), use the uniform deterministic rule selecting the smallest action index attaining the known table's maximum, ignoring D. Ties are broken by the fixed index order. On the reward space its selection regions are finite Boolean combinations of closed and open coordinate comparisons, hence Borel; again for any fixed model it is constant in D. This rule satisfies `A ≥ 2`.

## Exact source trajectory argument and quantifiers

Fix an arbitrary admissible MDP with these sizes and its known reward table. Every trajectory stays in s. For any policy, every reward at time `t ≥ 1` is at most `m(r)`; since `0 ≤ γ < 1`, its action-conditioned discounted return is at most

```text
r(s,a) + ∑_{t=1}^∞ γ^t m(r) = r(s,a) + γ m(r)/(1−γ).
```

The stationary reward-greedy deterministic policy attains this at every time `t ≥ 1`, simultaneously for every fixed initial action a. Thus, according to the paper's actual trajectory definition and its optimal-policy convention,

```text
Q*(s,a) = Q^greedy(s,a) = Qhat(r,γ,D)(s,a).
```

The same policy has `V*(s) = m(r)/(1−γ)`. This proof does not assume an optimal Bellman equation or independence across reward draws. It covers every admissible r and P, and every D, so the failure event in either part is empty and has probability zero for every model in the fixed-size class. Consequently the theorem's `∀ estimator, ∃ M` assertion fails for the one estimator above, **not** merely for one easy model. The crucial quantifier order is a single rule first, then all possible MDPs with S=1 and A=16, with the model's reward table provided as allowed input.

For any proposed universal constant `c_N > 0`, choose

```text
S = 1,  A = 16,  γ = 2/3,  N = 1,
ε = min { 1/64, sqrt(27 c_N log 16)/2 }.
```

All quantities are well defined and ε is strictly positive. We have `ε ≤ 1/64 < 3/32 = 1/[32(1−γ)]`, `SA = 16`, and `ε² ≤ (27 c_N log 16)/4`, so

```text
c_N log(SA)/[(1−γ)^3 ε²]
  = 27 c_N log 16 / ε² ≥ 4 ≥ N = 1.
```

Thus no choice of a smaller positive universal `c_N` makes the counterexample's hypotheses vacuous. The conclusion requires probability at least `1/4`, while it is exactly zero for every permissible MDP. A restriction `S ≥ 2` would exclude this particular example, but this audit does not claim that it is sufficient for the stated lower bound or that it has been approved.

The paper's proof constructs `M = 1 + (S−1)(A−1)` hypotheses (model-based chapter 1844–1906); the active state set is empty and `M = 1` when `S=1`. The Fano step (2022–2032) explicitly requires `M ≥ 4` and has `log M` in a denominator. This explains the proof's failure at the same boundary; the trajectory construction above is the actual disproof under the stated assumptions.

## Existing Lean evidence and missing exact declarations

- `Basic.lean` defines the actual finite distributions, nonempty finite MDP carriers, reward bounds, policy Bellman operator and optimality Bellman operator. `FixedPoint.lean` obtains unique Bellman solutions. `OneState.lean` proves the displayed formula satisfies `qOptimality`, hence equals `optimalityFixedPoint`, proves reward/discount-only dependence across models, and proves the reward-greedy point-mass policy has the same `policyFixedPoint`. The separate one-state Lean review found those Bellman claims and their allowed axiom closures valid. The formula's Lean definition currently accepts a whole MDP, so a source-facing statistical estimator should expose the known-input interface rather than relying solely on extensional independence.
- `FiniteOptimal.lean` concerns finite-horizon undiscounted trajectory returns; its explicit finite greedy policy and dominance do not identify infinite discounted Q*. `FiniteOccupancy.lean` concerns finite occupancy; its review reports remaining full-law and optimal-specialization bridges. `DiscountedFiniteTrajectory.lean` proves convergence of finite-horizon expected discounted **state** returns to a state Bellman fixed point; it explicitly does not establish the source's infinite-path expectation, action-conditioned Q, or optimal Q bridge. None is a direct proof of the sample-experiment theorem.
- To express a self-contained Lean refutation with the actual source semantics, the project still needs at least these exact objects and verified links (names are descriptions, not claims of existing exports):
  1. A genuine infinite discounted path probability law for a fixed model and policy, plus the first-action-conditioned/intervention law for arbitrary `(s,a)` (including zero policy probability), a measurable summable reward return, and the trajectory-expectation `Q^π`. Prove the relevant one-state greedy return formula and that it dominates `Q^π` for all source-admissible policies. Alternatively prove a general sound bridge from trajectory `Q^π` and trajectory-optimal `Q*` to the existing policy and optimality fixed points, including existence and simultaneous optimality; either route must genuinely connect to the source definition.
  2. An actual N-per-state-action independent generative-model product law, with input spaces recording state/action labels, the known reward table and fixed discount. An estimator defined on those observable inputs, with the concrete formula above, a measurability theorem (including any parameter dependence used), and a proof that its output equals source-defined `Q*` for every one-state MDP and every sample outcome. For (i), similarly supply the fixed tie-breaking reward-greedy policy and its source-Q equality.
  3. A formal parameter-feasibility statement quantified `∀ c_N > 0, ∃ ε > 0` at `S=1`, `A=16`, `γ=2/3`, `N=1`, proving the strict ε bound and sample-size inequality, with the real logarithm and square root domains checked. Then prove the exact source failure event has probability zero and state the negation of the theorem's `∀ estimator, ∃ M` conclusion with those parameters. This must quantify over all source-admissible models and permit the known reward to vary.
  4. Compile the exact resulting exports, inspect transitive axioms against the project trust boundary, and obtain a separate source/semantic review. Definitions or hypotheses that assume trajectory equality, an exact estimator, a vanishing event, or the theorem's negation would not discharge these obligations.

This report makes no source edits, Lean edits, claim of an approved correction, or whole-paper completion claim.
