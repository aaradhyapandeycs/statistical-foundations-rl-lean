# Source review: degenerate domains in the robust χ² lower bound

**Status:** source-only; no compiler run. This is a counterexample to the lower theorem's displayed quantifier range, conditional only on reading that display as its complete domain. It is not an author-approved interpretation or erratum.

## Finding

The χ² minimax lower-bound theorem in the chi-squared guarantees subsection (lines 461–480) does not state `S≥2` or `A≥2`. The robust-MDP definition uses finite carriers `S={1,…,S}` and `A={1,…,A}` but does not numerically exclude either singleton; the preliminaries' emphasis on “large” dimensions is descriptive rather than a theorem hypothesis. No section-wide action-count restriction appears in the robust-RL chapter.

At `A=1`, every policy, including a randomized or data-dependent output policy, assigns probability one to the sole action at every state. Hence for every robust MDP, its robust optimal value equals the robust value of every possible policy. For any positive `ε`, the event
`V^{\star,\sigma}(\mu)-V^{\widehat\pi,\sigma}(\mu)>\varepsilon`
is empty, for every dataset and every model. Therefore the theorem's two-model minimax expression is zero, not at least `1/8`. This conclusion does not depend on the two models sharing rewards, the estimator's inputs, or any sampling-law details.

There is a second degenerate boundary under the chapter's standing known-reward convention: when `S=1`, the only transition distribution on the singleton state is known automatically, and every χ² uncertainty set over that support contains only that distribution. Since rewards are known, a policy maximizing the reward at the sole state is known and exactly optimal. Thus the same zero-risk estimator exists for `S=1`, even if `A>1`.

## The displayed numerical domain is feasible

Take `γ=3/4`, `\sigma=1`, `S=2`, `A=1`, and `N=1`. For any positive proposed constants `c_3,c_4`, choose
`0<\varepsilon\leq\min\{2c_3,\sqrt{320c_4}\}`.
Then `\varepsilon\leq c_3/(1-\gamma)=4c_3`, and
\[
  \frac{c_4}{(1-\gamma)^3\varepsilon^2}
  \left(1+\frac{\sigma}{1-\gamma}\right)
  = \frac{320c_4}{\varepsilon^2}\geq 1=N.
\]
So the counterexample is not vacuous because of an impossible sample/precision constraint. The same parameter choice with `S=A=1` also satisfies the displayed cardinalities, if one is concerned only with the literal statement.

The theorem omits an explicit `\varepsilon>0` condition even though its sample threshold contains `\varepsilon^{-2}`. The counterexample above uses positive ε and so does not rely on that omission; adding positive accuracy to the statement is still advisable.

## Scope and proposed correction

As printed, Theorem 7.5 states that it applies to “any” `(S,A,\gamma,\ror,\varepsilon)` satisfying the listed conditions, which include no state/action lower bounds. Under that literal reading, `A=1` (and separately `S=1` with known rewards) contradicts the claim. The monograph's general statement that it focuses on large state/action spaces could signal intended scope, but it is not a formal restriction. Unlike some earlier chapter sections, the chi-squared guarantees subsection gives no explicit `A\ge2` convention to inherit.

The minimal transparent domain repair is to state `S\ge2`, `A\ge2`, and `\varepsilon>0` in the lower-bound theorem (or to explicitly label singleton cases as excluded). The existing [singleton-action obstruction](../Formalization/Obstructions/SingletonAction.lean) proves the abstract extensional equality for deterministic policies, but does not yet supply the robust-value semantics or this theorem's full experiment. This review does not establish that the cited nondegenerate lower-bound construction works on all of the repaired domain, and does not check the external citations.

## Source evidence

- `robust_RL.tex` lines 20–45 defines finite state/action sets and rectangular uncertainty, with no cardinality restriction.
- `robust_RL.tex` lines 25 and `prelim.tex` line 42 place the model under deterministic known rewards; the robust chapter focuses uncertainty on transitions.
- `robust_RL.tex` lines 431–450 state the χ² upper theorem; lines 461–480 state the lower theorem without `S\ge2`, `A\ge2`, or explicit `\varepsilon>0`.
- The radius macro is `\ror=\sigma` in `commands.tex` line 254.
- The source's “large” dimension language in `prelim.tex` is motivational text, not a quantified restriction.

Pinned source hashes: `robust_RL.tex` `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9`; `prelim.tex` `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`; `commands.tex` `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3`.
