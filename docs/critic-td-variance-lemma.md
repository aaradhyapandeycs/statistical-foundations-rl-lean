# TD variance lemma: source review

Source: Chen, Chi, Fan, Li, Wei, and Yan, *Statistical Foundations of
Reinforcement Learning: A Non-Asymptotic Perspective*, arXiv:2610.41903v1,
model-free chapter, `lemma:TD-variance-proxy-bound`, lines 727–743, in the
standing TD schedule and sample-budget context at lines 180–213. The pinned
chapter SHA-256 is
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

Independent AI reviewers checked the source statement, both variance bounds,
the actual sampling law, the same-event probability, the source schedule and
sample-budget consumption, and the production copy transformations. The
source-facing export compiled in the 332-module project check. Its transitive
axiom audit checked 4,099 declarations and allowed only `propext`,
`Classical.choice`, and `Quot.sound`. A separate clean-copy rebuild with
empty project artifacts and the pinned dependency cache passed the same 332
modules and the same 4,099-declaration axiom audit; all Lean source hashes
matched the working-project check.

## Source-facing statement

The export
`StatisticalRL.TemporalDifference.tdSource_varianceProxy_exists_universal_constants`
in `Formalization/ModelFree/TDSourceVarianceProxyUniversal.lean` chooses the
universal constants before the finite carriers and all model and problem data.
For the source finite discounted MDP, fixed policy, deterministic learning
schedule, initialization, confidence, accuracy, and sample-budget assumptions,
and any fixed source-eligible terminal `T/(c₂ log T)≤t≤T`, it proves a single
event of probability at least `1−δ/(2T)` under the actual TD sampling law.
That event contains **both** printed inequalities:

- the late proxy infinity norm is at most `16 barη H²`;
- the original predictable-variance infinity norm is at most
  `33 log³(T)/((1−γ)³ T)`.

Here `H=1/(1−γ)` and `barη=2 log³(T)/((1−γ)T)`. The wrapper chooses
`c₁=c₂=1/4` and `c₃=4096` and verifies sufficient constant relations before
applying the budget-fed proof. These are proof witnesses for the source's
small/large universal constants, not numbers specified by the manuscript.
It does not assume either desired bound, an extra high-probability event, or a
late-time or rate cap beyond the source schedule and budget.

## Actual variance and confidence

The proof identifies the original predictable second-moment sum with the
actual conditional variance under the TD history. It splits the source update
range at `floor(t/2)`: early squared weights are bounded using the source rate
schedule and budget, while the late contribution is bounded by the actual
late proxy. The scalar comparison absorbs the early term and the proxy's
`16 barη H²` bound into the printed 33-scale bound using `T≥2`; no additional
large-T premise is introduced into the final export.

The previously established fixed-terminal proxy event has probability at
least `1−δ/(2T)`. The original-variance estimate holds almost surely for the
same sampled data, so adding it to that event loses no confidence. Both
coordinatewise nonnegativity and finite infinity-norm conversions are handled
by the proof. The full TD accuracy theorem is separate and remains open.

## Reviewed production sources

| Module | SHA-256 |
|---|---|
| `TDEarlyVarianceBudget` | `64b282472e71b820f916e8644250891647880167c31be597971a7b42ceb997ed` |
| `TDOriginalVarianceSplitActual` | `e8ee0fa9bf329e48b3962d4363ddd0887ceb1fc4c39defcfe21ffc5de3486575` |
| `TDOriginalVarianceSplitBudget` | `e0ab679da868c395ba72fff0fba87a6d23f08b595929fe5e518f65a3b2241e1d` |
| `TDOriginalVarianceScale` | `684628965cd0b5bd418eaba8f1bb52c37aca3655fa4969498b2339c2f8c75340` |
| `TDOriginalVarianceCommonEvent` | `b20e1147d41bed34628bbac69d2a0531e132687878b22597f33ea5fe0bbd33c3` |
| `TDSourceVarianceProxyLemma` | `58e5a56a635759aeb1d37071bb4d4a6eaad16f47658e77bac2ebb99452893670` |
| `TDSourceUniversalConstants` | `fad5dfe4d41786ddcd397856d39ba07ff7ae19b7e218e2a94f4c32ce8936ff0d` |
| `TDSourceVarianceProxyUniversal` | `75c930e4ab917f6eb1284b54122aa44efece5e30e8faf2ed2aaa28847b5e156a` |

All modules are under `Formalization/ModelFree/`. Independent comparisons
verified that the production copies preserve the reviewed statements and proof
bodies, with only qualified imports and module-header prose changed.
The working-project evidence is recorded locally in
`verification/20261103T140943408415Z/`.
