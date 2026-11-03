# TD fixed-terminal proxy concentration: source review

Source: Chen, Chi, Fan, Li, Wei, and Yan, *Statistical Foundations of
Reinforcement Learning: A Non-Asymptotic Perspective*, arXiv:2610.41903v1,
model-free chapter, the variance proxy `TD-variance-proxy` and the first bound
in Lemma `TD-variance-proxy-bound`. The pinned chapter SHA-256 is
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

Independent AI reviewers checked the source quantities, confidence allocation,
actual sampling law, schedule and budget substitutions, and the production
copy transformations. The actual 321-module project build and a separate
clean-copy rebuild both passed; each transitive axiom audit checked 4,021
declarations and allowed only `propext`, `Classical.choice`, and `Quot.sound`.
The clean copy started with empty project artifacts and used the pinned
dependency cache. All 321 Lean source hashes agree between the two checks.

## Scope

`StatisticalRL.TemporalDifference.tdSource_fixedTerminalProxy_of_budget` in
`Formalization/ModelFree/TDSourceFixedTerminalProxyBudget.lean` bounds the
actual late-window proxy vector in the infinity norm by `16 barη H²` for a
fixed eligible terminal, with probability at least `1−δ/(2T)` under the
actual synchronous sampling law. Here `H=1/(1−γ)` and
`barη=2 log³(T)/((1−γ)T)`. The stated sufficient source-budget constant
`c₃≥384` is an explicit choice under the source's large-enough-constant
convention, not a claim that the manuscript specifies this number.

The theorem retains the source finite rate schedule, bounded initial values,
confidence and accuracy domains, `γ≥1/2`, the sample budget, and eligibility
`T/(c₂ log T)≤t≤T`. It derives the late-rate and smallness estimates, the
dyadic cutoff, and the global positive-rate requirements by a zero-tail
extension, then transports the event back to the original finite schedule.
The state union spends `δ/(2ST)` per coordinate. Nonnegativity of the actual
proxy supplies the infinity-norm conclusion from coordinatewise upper bounds.
No proxy upper bound or desired probability conclusion is assumed.

**This proves only the first of the two bounds in the printed lemma.** The
second bound concerns the original full predictable variance `W_t` and is
proved separately using the early/late decomposition and the source-scale
`33` estimate; see the [full variance-lemma review](critic-td-variance-lemma.md).
The main TD accuracy theorem remains open. The proxy bound alone does not
establish the complete named lemma.

## Reviewed production sources

| Module | SHA-256 |
|---|---|
| `TDSourceFreedmanLogComparison` | `86519cefe68295848df04f44e1db0cd2349e18c80c801218d7f5dce1ea0f97ad` |
| `TDSourceFreedmanDyadicCutoff` | `c4a2342595b0a306e0182cb58ad986361fd7efb3e6817fcac8956b110a8ffaa2` |
| `TDSourceFreedmanBudgetSmallness` | `525f203d2103a60f8394756ddbbf9a533e6e85efe6cb3266a28116db0b7bfeb2` |
| `TDSharpSecondFreedman` | `ea6917740ca5d5ee499ae7d4c3862646b8e958e6068c84789c2efb28a89b333f` |
| `TDSharpSecondFreedmanEligibleUnion` | `d218bcc7eb27efcbe319ff1b2ffc9d136bcf9b1f487ce94cd764136f534c8efc` |
| `TDSourceFixedTerminalProxy` | `f336705ce6b5a0fc6f20357d07ba9251c714c41bafa8e73d4aad93aa7655446b` |
| `TDSourceFixedTerminalProxyBudget` | `0780ce434f4ba78c43f15d374cf01af32fdb9d798fe9ff76ea1a80c37662fb8e` |

All modules are under `Formalization/ModelFree/`. The independently compared
production copies preserve the reviewed declarations and proofs; an identical
existing eligibility predicate replaces a duplicate staged predicate. The
working-project check is recorded locally in
`verification/20261103T132956675217Z/`; the independent clean-copy check used
the same source hashes and passed the same audit.
