# Independent review: UCBVI zero-count scalar correction

## Scope and source comparison

The integrated module path is
`Formalization/Online/OnlineZeroCountOptimisticUpdate.lean`. The reviewed
production-layout source has SHA-256
`ffaa10c823a197794eff6d6b4ecb18ff97edf48cf949a9ab4ed6c43eaaa2f2d1`.
The preview was compared with the narrow-import candidate that was compiled
and axiom-probed (SHA-256
`59750dde5c58b5d3e24f1ac350a98b98fdd3d6289c626066d9af77e859f51a8a`). The
only difference is the module-level comment describing the proposed repair.
Imports, declaration statements, definitions, and proof bodies are identical.

The mathematical source is `source/upstream/tex/chapters/onlineRL.tex`.
Algorithm 5.2 initializes counts to zero and Q/V to H, then updates all rows
after collecting data (approximately lines 296–336). The printed Bernstein
bonus at lines 407–417 divides by the visit count, without defining an N=0
case. The proof of optimism treats N≤2 as a deterministic Q=H case at lines
3320–3327. Therefore the candidate makes an undefined source branch explicit;
it does not claim that Lean's totalized division at zero implements the
source's intended saturation.

## What the scalar module establishes

The total update returns H at N=0 without evaluating a bonus. For every
positive N it is exactly the printed capped scalar update. Its small-count
lemma proves saturation for N≤2 under nonnegative reward, empirical mean, and
horizon, with `log(1/δ) ≥ 1`, nonnegative c1, and `c2 ≥ 2`. Its range lemma
proves the corrected update lies in `[0,H]` under nonnegative reward, mean,
horizon, logarithm, and bonus coefficients. The logarithm helper derives
`log(1/δ) ≥ 1` from `0<δ≤1/100`.

These are scalar results. A consumer must show that its empirical mean is
nonnegative for the actual normalized empirical row and bounded continuation,
and derive the small-count parameter assumptions from the source's constants
and confidence allocation.

## Compile and axiom evidence

The narrow-import candidate compiled in an isolated output. Its five checked
exports—the zero branch, positive branch, small-count saturation, range, and
logarithm helper—used only `propext`, `Classical.choice`, and `Quot.sound`.
The production-layout preview was also independently compiled and probed,
and its bytes now match the integrated module. The working project and a separate clean copy both passed the full module
build and transitive axiom audit on matching source hashes.

## Limits

The N=0 rule is a proposed visible correction, not an author-approved erratum
or an implementation of a defined source expression. This module does not
define the capped backward planner, prove its initialization/update
correspondence, establish the empirical-row and true-value ranges in that
planner, consume the adaptive observed-prefix certificate, or prove source
optimism. It also does not prove the online regret theorem.
