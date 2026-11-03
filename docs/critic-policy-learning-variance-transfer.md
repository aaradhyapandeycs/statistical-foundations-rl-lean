# Independent review: leave-one-out variance transfer

**Verdict: pass for the deterministic transfer.** The module proves the scalar inequality used in `generative_model_model_based.tex:1345–1371`, especially `eq:Phat-sa-Vhat-star-concentration-proof-mb-tight`; it does not prove a concentration event or policy-learning theorem.

For any actual finite probability row d and arbitrary signed real vectors f,g, the file derives weighted Cauchy–Schwarz by applying `Real.sum_mul_le_sqrt_mul_sqrt` to `√p(s)f(s)` and `√p(s)g(s)`. The use of the nonnegative row masses correctly recovers the actual finite expectation. Expanding the square gives a triangle inequality for square roots of second moments; replacing the vectors by their centered forms gives `√Var_d(f+g)≤√Var_d(f)+√Var_d(g)`. `Var_d(f)≤E_d f²≤‖f‖∞²` then yields the sharp `|√Var_d(f)−√Var_d(g)|≤‖f−g‖∞`. The argument covers zero variance and constant vectors, with no division by a standard deviation or nonnegativity assumption on f,g.

For actual finite probability rows p,q, the residual difference is bounded by `2‖f−g‖∞`, using separate normalized-row expectation bounds and the triangle inequality. If `‖f−g‖∞≤η`, a≥0, and the explicit intermediate premise `|(q−p)g|≤a√Var_p(g)+b` holds, the generic transfer proves `|(q−p)f|≤a√Var_p(f)+(2+a)η+b`. The p/q orientation and the source's `2η` and `aη` contributions are correct. No independence is claimed for f or g; when g is selected from data, a later probabilistic proof must establish its concentration inequality simultaneously before selection.

The source-radius specialization takes N>0, h>0, β≥4, `η=1/(Nh)`, and the explicit grid premise with `a=√(β/N)` and `b=β/(3Nh)`. Since N≥1 and β≥4 imply `√(β/N)≤β/2`, the algebra proves `(2+√(β/N))/(Nh)+β/(3Nh)≤2β/(Nh)`, preserving the exact source coefficient 2. The β≥4 assumption is visible and must be discharged in a source application from `β=2log(16SAN/(hδ))` and its own parameter assumptions; this file does not prove that downstream fact. h is any positive real here; applying the source interpretation requires h=1−γ. No division by γ appears, so γ=0 is covered after setting h=1. The result also permits N=1 and zero variance.

The file does not supply the finite grid, value-cover distance, actual-law Bernstein event, selected-index validity, policy choice, self-bounding resolvent, or final learning guarantee. Its `hcover` and `hgrid` premises are genuine intermediate inputs, not a source theorem claimed under extra hidden assumptions.

Staged source SHA-256 `b601af7ce8d8bc5935e11b299c27875ded4f50674d37867bd991c68f5464b9d0`; source chapter SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. An exact unchanged source copy retaining its original imports and with eleven appended `#print axioms` commands compiled independently, exit 0. Every exported theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. Actual integrated-export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningVarianceTransfer.lean` is byte-identical to staged SHA-256 `b601af7ce8d8bc5935e11b299c27875ded4f50674d37867bd991c68f5464b9d0`. The actual module compiled and import-only axiom checks of all eleven exports used only `propext`, `Classical.choice`, and `Quot.sound`.
