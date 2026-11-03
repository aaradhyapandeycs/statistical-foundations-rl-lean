# Independent source review: forced-prefix Q-learning KL chain

Status: independent source/semantic review and exact-source compile/axiom
audit complete. The source chapter SHA is
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The four staged module hashes below match those recorded in
`docs/builder-q-learning-trajectory-kl-chain.md` at review time.

## Source target

The target is the proof of `Q-comparison-facts`, part (ii), Lemma 4.10(ii),
source lines 2641–2692. Equations `eq:KL-ub-k-rho-proof` and
`eq:Q-comparison-geometric-return` fix the orientation and finite-horizon
meaning: `P'_k` is first, baseline `P_k` second, and the initial state-action
pair is identical and fixed. A horizon `k` trajectory has exactly `k`
transitions, with policy actions after each transition through the terminal
action; it has no transition after that terminal action. The source separately
uses the geometric stopping law, its infinite sum, and Pinsker after the
finite-horizon chain rule.

## Exact source hashes and findings

| Staged module | SHA-256 | Independent source finding |
|---|---|---|
| `.local/QLearningTrajectoryKLPrefixDraft.lean` | `0e9970e1ec4477989ca397f4d3b51ca6138ae2a37a4e6d87e96c0f08730730d2` | `QForcedPrefix 0` is `PUnit` of mass one; successor adds one next-state draw, the common policy action at that state, and the remaining suffix. The initial pair is external/fixed, so no time-zero transition is sampled. The support induction uses candidate-positive atom ⇒ baseline-positive atom, including common-policy factors; the `k=0` case uses no row premise. |
| `.local/QLearningTrajectoryKLHeterogeneousDraft.lean` | `62a87b2c77a348274852e6a2a230c86fe2ad73bc3f6272cba88240f12411a64c` | The joint chain rule is for different finite carriers and supports candidate-to-baseline likelihood inclusion, not full support. Its log split and finite sums have the oriented form `KL(μ'K' || μK)=KL(μ'||μ)+E_{μ'}KL(K'_x||K_x)`. The common-marginal specialization correctly removes the common policy KL term. |
| `.local/QLearningTrajectoryKLInductionDraft.lean` | `a08f062b9f65c973649a192251c6d22ff8c6a89645e9922a159d56a736518cca` | The recursive row cost is candidate transition expectation, followed by the shared policy expectation; its recurrence adds `KL(M' row || M row)`. Under an explicit all-row bound by `ρ`, induction proves cost `≤kρ`. This numerical bound does not itself identify the cost with path-law KL. |
| `.local/QLearningTrajectoryKLPathInductionDraft.lean` | `e3469cffd92a6fb3d12248482f0236d5f8a6e4b7065a65c2d718144e042b55dc` | The successor factorization has one candidate/baseline transition row and a continuation over the shared policy plus suffix. The two chain rules are called with the correct orientation; the path-law expression equals the recursive cost, including the zero-cost `k=0` base. |

## Verdict and limitations

The four statements form a source-faithful finite forced-prefix KL chain at
the level of finite atomic masses. The carrier deliberately omits the fixed
initial pair, which cannot change KL. The path support assumption is exactly
the rowwise support inclusion needed to keep candidate path mass absolutely
continuous with respect to baseline path mass. Zero-mass candidate cells
contribute zero under `finiteKLExpression`; no reference full-support
assumption is imposed.

The exported chain theorem is stated using
`StatisticalRL.GenerativeLowerBound.finiteKLExpression` on actual
`FiniteDistribution.prob` functions. The reviewed modules do not state the
result directly using `InformationTheory.klDiv`; a downstream theorem wanting
that measure-level API must apply the existing finite-`klDiv` conversion under
the path-support hypothesis. Also, the numeric `kρ` result assumes the rowwise
finite-KL bound as an input. The source's separate implication from the
uncertainty-set/χ² assumption to that rowwise KL bound is not in this four-file
chain and must be supplied by its own proved adapter.

The source's geometric stopped-law mixture identity, infinite expectation
calculation, total stopped-law KL bound `ργ/(1−γ)`, and final Pinsker/value
comparison are not established by these four modules. The stopped-law drafts
mentioned in the builder handoff remain separate and unreviewed here.

## Independent exact-source compile and axiom evidence

Before compilation, all four staged source hashes were checked against the
reviewed values above; each matched exactly. The modules were compiled in
dependency order with `bash scripts/lean-local.sh`, using isolated outputs in
`.local/q-trajectory-kl-chain-independent-review-20261103/out`:

1. `QLearningTrajectoryKLPrefixDraft`
2. `QLearningTrajectoryKLHeterogeneousDraft`
3. `QLearningTrajectoryKLInductionDraft`
4. `QLearningTrajectoryKLPathInductionDraft`

All four compiles succeeded. The prefix file emitted only the previously
recorded unused-simp-argument and unnecessary-`simpa` warnings; the other
three compile logs were empty. The temporary module-path links used to make
the staged imports visible to the repository wrapper were removed after the
audit. Existing project/Mathlib dependencies were consumed; no dependency
rebuild or production module change occurred.

The independent probe
`.local/q-trajectory-kl-chain-independent-review-20261103/AxiomProbe.lean`,
SHA-256 `2b8526509185fc528d28940e1ba3b6d48aeef27936f9666d0905e9144467a223`,
prints axioms for every definition, instance and theorem exported by the four
modules. `QForcedPrefix` itself reports no axioms. Every other probed export
reports exactly `propext`, `Classical.choice`, and `Quot.sound`; no custom
axiom or placeholder was found in the four exact sources. The isolated OLean
hashes are recorded in the output directory. This is compile and axiom
evidence for the finite forced-prefix chain only, not a geometric stopping,
Pinsker, or value-stability result.

## Production integration

The reviewed finite forced-prefix KL chain is integrated as the corresponding `Formalization/ModelFree/QLearningTrajectoryKL*.lean` modules. Geometric stopping, countable Pinsker and full model stability remain separate. The proof and declaration bodies match the reviewed staged sources; imports and status comments were updated. The full project check compiled 288 modules and audited 3,756 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
