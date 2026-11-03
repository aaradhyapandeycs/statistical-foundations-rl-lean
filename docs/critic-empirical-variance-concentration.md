# Independent empirical variance concentration review

Reviewed 2026-11-02. Target: `.local/EmpiricalVarianceConcentration.lean`, SHA-256 `385479ab6a59961672c8eee4dac5d77b0bc265f636d685eeede10881dfc84bb8` (recomputed before review). This is ordinary staged infrastructure, not a frozen/manifested source declaration. I independently read the target, its probability/variance dependencies, the builder note, and the raw source.

**Verdict: PASS for the stated additive two-moment variance tail and its one-sided corollary. The general source empirical Bernstein lemma remains UNPROVED.** No mathematical or axiom defect found in this file. Integration/export compilation remains the lead's responsibility; this review certifies the exact staged file above.

## Source correspondence and scope

Authoritative source: arXiv:2610.41903v1, `source/upstream/tex/chapters/prelim.tex:983–998`, label `empirical bernstein`; variance definition at lines 428–437, label `eq:defn-Var-Psa-V`. Source file SHA-256 recorded in provenance and builder note: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

The source asserts simultaneous empirical-mean error control for a finite family of nonnegative vectors independent of the empirical row, for N≥2 and 0<δ<1, with success probability strictly greater than 1−δ and radius

`√(2 log(4|𝒱|/δ)/(N−1)) √Var_P̂(V) + 7 ‖V‖∞ log(4|𝒱|/δ)/(3(N−1))`.

The reviewed declarations instead control the additive error in empirical variance for one fixed bounded vector. They contain no δ, random family, family independence hypothesis, simultaneous event, strict success probability, or mean-error conclusion. Their displayed constants are correct for their own bound; they do not establish the source constants 2 and 7/3 or its N−1 denominator. The builder note correctly and prominently states this limitation. This intermediate result must not mark the source lemma proved.

## Expanded logical inputs

The same binder classification applies separately to both theorems (`empiricalVariance_hoeffding`, lines 19–24, and `variance_upper_confidence_hoeffding`, lines 61–66). This is an infrastructure audit, so SOURCE below means an explicit premise of the independently reconstructed intermediate statement, not an assertion that the source lemma itself has these exact binders.

| Binder | Bin | Meaning / justification |
|---|---|---|
| `{State : Type*}` | TYPING | Finite state carrier, source finite S. |
| `[Fintype State]` | TYPING | Enumeration of finite states. |
| `d : FiniteDistribution State` | SOURCE | Genuine probability row. Expanded fields: `prob : State → ℝ` (typing), `∀s, 0≤prob s` and `∑s,prob s=1` (probability-row standing premises). |
| `N : ℕ` | SOURCE | Sample count. |
| `hN : 0 < N` | SOURCE | Positive count needed for normalized empirical frequency; intermediate scope includes N=1. |
| `V : State → ℝ` | SOURCE | Fixed vector, chosen before sampling. |
| `B : ℝ` | SOURCE | Deterministic upper range endpoint. |
| `ε : ℝ` | SOURCE | Deterministic error threshold. |
| `hB : 0 < B` | SOURCE | Positive range endpoint, needed for threshold division. |
| `hε : 0 ≤ ε` | SOURCE | Nonnegative threshold. |
| `hV : ∀s, V s ∈ Icc 0 B` | SOURCE | Expanded: `∀s, 0≤V s ∧ V s≤B`. |

Top-level counts per theorem: SOURCE 9, TYPING 2, STANDING 0, RULED 0, EXCESS 0. Expanding the distribution replaces its one SOURCE row with one typing field and two standing probability constraints; expanding interval membership adds its two pointwise inequalities. No result-shaped input or concentration assumption is hidden in a bundle. The local full measurable-space instance imposes no additional mathematical restriction on a finite carrier.

## Measure, variance, and proof reconstruction

`rowMeasure` is the measure of the actual PMF obtained from nonnegative, unit-sum `d.prob`. `sampleMeasure N` is `Measure.pi (fun _ : Fin N ↦ d.rowMeasure)`, not an arbitrary measure supplied with a concentration premise. Coordinate marginals and mutual independence are proved in `EmpiricalRow.lean`. Every function/event here is measurable on a finite full measurable space, and the probability measure is finite, so the real-measure monotonicity and union bound are valid.

`empiricalRow` uses actual sample frequencies divided by N. Its expectation is exactly `N⁻¹ ∑ᵢ V(ωᵢ)`. `variance` is `E[V²]−E[V]²`, with a proved centered-square characterization. Therefore `empiricalVariance` is exactly the source empirical row variance with denominator N, not the unbiased N−1 estimator. Existing downward-bias/correction lemmas do not alter this definition.

Let Q=P̂, m_Q=QV and m_P=PV. Both means lie in [0,B], so

`|Var_Q(V)−Var_P(V)| ≤ |Q(V²)−P(V²)| + 2B |QV−PV|`.

If the left side is at least ε, either the second-moment error is at least ε/2 or the first-moment error is at least ε/(4B). The implementation proves this containment by the strict complementary inequalities; this correctly handles equality at the tail boundary. It applies the already proved iid Hoeffding theorem to V²∈[0,B²] and V∈[0,B], then a union bound. The two resulting terms are exactly

`2 exp(−N ε²/(2B⁴)) + 2 exp(−N ε²/(8B⁴))`.

These equal the file's unsimplified expressions. No independence between the two moment events is needed or assumed. For the corollary, `Var_Q(V)+ε < Var_P(V)` implies `ε < Var_P(V)−Var_Q(V) ≤ |Var_Q(V)−Var_P(V)|`; weakening to ≥ε makes the two-sided tail directly applicable. Thus outside that strict failure event the valid conclusion is `Var_P(V) ≤ Var_Q(V)+ε`.

## Boundaries and rate

- N=0 is excluded. N=1 is valid: the empirical variance is zero, and the possibly loose probability bound remains correct.
- ε=0 is included: the two-sided event is the whole sample space, and the bound is 4. This is consistent, not informative. The one-sided bound is likewise valid.
- B=0 is excluded explicitly. For a zero vector one may choose any positive B, but this declaration does not supply the sharp separate zero-range theorem. No division-by-zero argument is concealed.
- Equality at V=0, V=B, and the tail thresholds is included. Deterministic distributions/constant vectors have zero variance discrepancy; the theorem still holds. The RHS may exceed one and is not clipped.
- The bound gives additive variance error of order B²√(log(1/δ)/N). For example ε=B²√(8 log(4/δ)/N) gives the displayed RHS at most δ for 0<δ<1, by elementary calculation; no such confidence inversion theorem is claimed here. Inserting a generic additive variance error into a population-variance mean bound introduces a weaker remainder and does not establish the sharp source self-normalized rate. A sharper argument or equivalent full empirical Bernstein proof remains necessary.

## Independent validation

Repository pins inspected: Lean `v4.27.0-rc1`, Mathlib `32d24245c7a12ded17325299fd41d412022cd3fe`. Used only the repository wrapper and existing dependency artifacts. Compiler slot coordinated with the lead and policy reviewer; no more than two Lean processes were active.

1. `bash scripts/lean-local.sh .local/EmpiricalVarianceConcentration.lean` — exit 0, no diagnostics.
2. Copied the exact reviewed source to `/tmp/CriticEmpiricalVarianceConcentration.lean`, appended `#print axioms StatisticalRL.FiniteDistribution.empiricalVariance_hoeffding` and `#print axioms StatisticalRL.FiniteDistribution.variance_upper_confidence_hoeffding`, and ran `bash scripts/lean-local.sh /tmp/CriticEmpiricalVarianceConcentration.lean` — exit 0.
3. Both transitive axiom closures were exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axiom, or admitted dependency appeared. The temporary probe was deleted.

No Lean implementation file was changed in this review. Full project/export validation was not duplicated; the lead must perform it after integration. Source empirical Bernstein closure, all-confidence sharp radius, and independent random finite-family lifting remain open.
