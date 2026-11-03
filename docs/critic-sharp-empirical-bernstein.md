# Independent sharp Bernstein review

Reviewed 2026-11-02, independently of the builder. Verdict: **PASS as a fixed deterministic vector, population-variance Bernstein contribution; PARTIAL for source Lemma 2.5.** The staged source was preserved unchanged. This is ordinary infrastructure review, not author approval, a frozen-anchor audit, or whole-lemma certification.

## Identity and source

- `.local/SharpEmpiricalBernstein.lean`: SHA-256 `f47b57d451b8ee49c8b702a834ee99747ec5cca36288bf9344dd08c11a596e67`, matching the builder handoff.
- `source/upstream/tex/chapters/prelim.tex`: SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- Sampling definition: source lines 916–927. Population variance: lines 427–437, equation `eq:defn-Var-Psa-V`. Bernstein statement: lines 956–978, label `lem:Bernstein-prelim`, especially `eq:Bernstein-Psa-prelim` and `eq:Bernstein-P-whole-prelim`.

The source requires simultaneous non-strict bounds for a finite family of nonnegative vectors independent of the empirical row, with success probability strictly greater than `1 − δ`, `0 < δ < 1`. Its row radius is `sqrt(2 log(4k/δ)/N) sqrt(Var_P(V)) + 2 ‖V‖∞ log(4k/δ)/(3N)`. Its second assertion replaces `k` by `SAk` and requires independence from the entire empirical matrix. The later empirical Bernstein statement at lines 985–997 is a distinct result with empirical variance, `N−1`, and coefficient 7; this file does not prove it despite its filename.

## Final theorem binder review

Target: `StatisticalRL.FiniteDistribution.empiricalRow_source_threshold_strict`. There are no hidden concentration assumptions. Expanded logical fields of the distribution are listed separately.

| Binder or expanded field | Bin | Justification |
|---|---|---|
| `State : Type*` | TYPING | finite state carrier |
| `[Fintype State]` | STANDING | source finite state space |
| `d : FiniteDistribution State`, underlying `prob : State → ℝ` | SOURCE | selected transition row |
| `d.prob_nonneg : ∀ s, 0 ≤ d.prob s` | SOURCE | row is a probability vector |
| `d.sum_prob : ∑ s, d.prob s = 1` | SOURCE | row normalization |
| `V : State → ℝ` | SOURCE | one selected deterministic vector |
| `N : ℕ` | SOURCE | sample count |
| `hN : 0 < N` | STANDING | required by source empirical frequency `1/N`; zero samples have no empirical probability row |
| `B : ℝ` | TYPING | explicit upper-bound parameter generalizing the norm |
| `L : ℝ` | TYPING | explicit logarithmic tuning parameter |
| `hB : 0 ≤ B` | SOURCE | nonnegative norm/range bound |
| `hL : 0 < L` | SOURCE | holds for `log(4k/δ)` when `k > 0`, `0 < δ < 1` |
| `hV : ∀ s, V s ∈ Icc 0 B`, lower conjunct | SOURCE | vector nonnegativity |
| `hV`, upper conjunct | SOURCE | taking `B = ‖V‖∞` supplies it |

Counts: SOURCE 9, STANDING 2, TYPING 3, RULED 0, EXCESS 0 (counting expanded rows as above). `B` and `L` make this an internal general statement; their norm/log instantiation and source family assembly remain to be compiled before claiming the source lemma. No variance-positive premise survives in this final theorem.

## Definitions and proof semantics

`FiniteDistribution` stores actual nonnegative masses summing to one. Its expectation is the weighted finite sum. `variance` is exactly `E[V²] − E[V]²`, proved equal to `E[(V−EV)²]`. The sample law is `Measure.pi (fun _ : Fin N ↦ d.toPMF.toMeasure)`, not an arbitrary measure accompanied by a tail assumption. Coordinate marginals equal the row law and independence follows from the product construction. `empiricalRow` uses actual indicator frequencies and its expectation equals the sample mean. Zero-mass states require no positive-support assumption.

The scalar MGF proof is substantive: `(n+2)! ≥ 2·3^n` majorizes the exponential series tail by a convergent geometric series for `|z| < 3`. The centered value satisfies `|V−EV| ≤ B`. Integration cancels the linear term and yields the centered-square variance, followed by `1+x ≤ exp x`. The actual iid sum MGF factors through proved independence and row marginal identities. Chernoff integrability is valid because the sample carrier is finite. Thus the sharp bound is proved, not assumed.

For positive variance, `u = ε/(Var+Bε/3)` satisfies `uB < 3`; substitution gives exponent `−Nε²/(2(Var+Bε/3))`. Reflection `B−V` preserves variance and produces the lower tail. The union gives coefficient 2. Setting `ε = sqrt(2 L Var/N) + 2BL/(3N)` makes the exponent at most `−L`. These are exactly the source constants for a single vector after norm/log substitution; nonnegative square-root factorization reconciles the two written radius formulas.

The final strict failure event is the complement of the source non-strict success bound. Zero variance is handled through a proved zero tail, not a positive-variance assumption: if `B > 0`, `L > 0` makes the radius positive; if `B = 0`, `V` is identically zero and the strict failure event is empty. `N = 1` is admitted; `N = 0` is explicitly excluded. The positive-variance intermediate permits `L = 0`, giving the harmless bound 2. The final theorem requires `L > 0`, which covers the source logarithm for nonempty families.

## Validation and scope limits

Independent commands:

- `bash scripts/lean-local.sh .local/SharpEmpiricalBernstein.lean`: exit 0, no diagnostics.
- `bash scripts/lean-local.sh .local/SharpCriticAxioms.lean`: exit 0. The temporary file was an exact copied source with appended `#print axioms`; it was deleted after review.

All nine staged theorems were audited: `exp_remainder_le`, `centeredRow_mgf_le_sharp`, `empiricalRow_upper_sharp_chernoff`, `empiricalRow_upper_sharp`, `empiricalRow_lower_sharp`, `empiricalRow_twoSided_sharp`, `empiricalRow_zeroVariance_sharp`, `empiricalRow_source_threshold`, and `empiricalRow_source_threshold_strict`. Every transitive axiom list is exactly `[propext, Classical.choice, Quot.sound]`. No placeholders or custom axioms were found. One compiler was used, sequentially, within the shared two-compiler limit.

Remaining source gaps: formal norm/log substitution; finite-family union and empty-family convention; measurable random-family law and independence transfer; whole-matrix union with the `SA` factor; actual strict success probability `> 1−δ`; integration into production exports and the production audit. Mathematically the source slack is sufficient: `L = log(4k/δ)` yields per-vector failure at most `δ/(2k)`, so a deterministic finite union gives at most `δ/2 < δ`. This calculation is not yet a Lean theorem here. No finite-support minimum-gap argument is necessary. The subsequent empirical-variance result remains entirely outside this contribution.
