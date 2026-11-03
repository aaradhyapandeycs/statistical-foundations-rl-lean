# Source absorbing grid, value cover and beta-count handoff

`.local/PolicyLearningAbsorbingGrid.lean` constructs the exact source grid in `eqn:net-eps-LOO-inf` (`generative_model_model_based.tex:1282–1290`), proves its closed-interval coverage and count, and consumes reviewed preservation/Lipschitz results to prove the actual empirical value-cover assertion of `LemValueCover` (`:1292–1299`). It also supplies a deterministic cardinality/logarithm comparison toward source β₁ at `:1308–1311`. Independent review and production integration remain pending.

## Exact grid and endpoints

For h=1−γ>0 and positive natural N,

`absorbingGridStep M N hN = 1/(Nh)`,

`absorbingGridPoint M N hN i = i/(Nh)` for `i : Fin(N+1)`,

`absorbingParameterGrid = image of all those points`.

The multiplication identity proves each point is exactly i times the source step. Every point is in [0,1/h]. The first point is 0, the last is N/(Nh)=1/h, and both endpoint memberships are proved. The positive denominator makes the indexing injective, so the finite parameter set has cardinality exactly N+1. N=0 is excluded by the explicit positivity witness, and there is no invented zero-sample grid semantics.

`absorbingGrid_covers_interval` proves every u∈[0,1/h] has an index i with `|u−gridPoint i|≤1/(Nh)`. Its actual witness is the natural floor of uNh. Nonnegativity and uNh≤N give the index bound, while the ordinary floor inequalities give the distance bound. In particular the closed right endpoint is included as index N; no strict-interior assumption or clamping fallback occurs. N=1 and γ=0 are covered.

The grid parameter functions read only N and M.discount. `absorbingParameterGrid_empirical` proves the parameter set formed from the actual empirical model equals the original model's parameter set for every sample, definitionally. Thus the finite parameter set is deterministic before sampling; this statement does not assert independence of every function constructed from it.

## Actual fixed-parameter value family and duplicate handling

`absorbingGridValue M N hN x i` is the **actual optimal trajectory value function** of the x-absorbing model with fixed parameter gridPoint i. Its admissibility proofs come from the grid interval theorem. `absorbingGridValueFamily` is the finite image of those functions.

The functions in this particular family are also distinct: at the absorbing state x their actual trajectory values equal their respective grid parameters, regardless of optimal tie choices. Hence the index-to-value-function map is injective and the value family has cardinality exactly N+1. The file additionally proves the generic bound `card(image f)≤N+1` for any map of those indices; duplicate images under later transformations may be collapsed without increasing the count. It does not incorrectly identify an index count with arbitrary family cardinality without an injectivity proof.

## Source LemValueCover composition

`absorbingGrid_covers_optimalValue` applies interval coverage to u*=V*(x). Its parameter is admissible by actual trajectory bounds. The reviewed preservation theorem proves the absorbing value at u* equals original V* everywhere; the reviewed fixed-parameter 1-Lipschitz theorem then gives a grid index i such that

`‖V* − V*_(x,gridPoint i)‖∞ ≤ 1/(Nh)`.

Neither equality nor closeness is assumed. The result applies to any valid source MDP. `empirical_absorbingGrid_covers_valueEstimator` specializes it to the actual empirical MDP built from M,N,data and identifies its original optimal trajectory value with the actual model-based value estimator. Its exact conclusion is a witness `i : Fin(N+1)` with

`‖valueEstimator M N hN data − absorbingGridValue (empiricalModel M N hN data) N hN x i‖∞ ≤ absorbingGridStep M N hN`.

Each witness parameter is a member of the source finite grid by `absorbingGridPoint_mem`. Therefore the indexed conclusion supplies precisely the source parameter-net witness in `LemValueCover`. It is pointwise for every sample outcome, not restricted to a concentration event or support condition.

The selected covering index may depend on the full data via the empirical optimum. It is **not** declared independent of the omitted row. The finite family with fixed indices is the object to which a separate independence/union argument may apply. Fixed-u row independence, the measurability of that family, Bernstein concentration on it, and the source policy-learning statistical theorem remain separate obligations and are not consequences merely of this covering result.

## Exact logarithm comparison toward source beta

For any nonempty family size k≤N+1 and δ>0, `absorbingGrid_bernstein_log_bound` proves

`2 log(4k / [δ/(2SA)]) ≤ 2 log(16SAN/[(1−γ)δ])`.

The right side is exactly the source β₁. The arithmetic uses N+1≤2N for N≥1 and h≤1 from γ≥0; the confidence allocation δ/(2SA) corresponds to the source's desired union budget δ/2 across state-action pairs. The proof establishes the logarithmic comparison only. It does not itself allocate probabilities, assume events independent, prove a Bernstein event, or take a data-selected witness as fixed. The exact N+1 family qualifies directly; a nonempty duplicate-collapsed image with smaller k also qualifies.

## Source range and remaining work

All grid and cover results hold for source finite nonempty MDPs with reward in [0,1] and 0≤γ<1, including zero discount and horizon interval endpoints. The only new domain premise is the positive frequency/sample count N. The grid logarithm lemma additionally uses δ>0 and a nonempty size k within the proved count; the source application has 0<δ<1 and k=N+1. No source-sharp error or concentration premise is supplied.

This provides staged deterministic evidence for the complete named value-cover lemma and its finite-grid prerequisites. It is not an independently certified source-node closure, a fixed-u independence theorem, or the final policy-learning guarantee. A reviewer must check the exact source objects and actual empirical-model specialization before integration.

## Verification

The file imports the actual integrated preservation/Lipschitz chain. It was compiled only after the lead allocated a compiler slot. `bash scripts/lean-local.sh .local/PolicyLearningAbsorbingGrid.lean` compiled cleanly, including the actual empirical value cover and logarithm comparison. An exact unchanged-source copy `.local/AbsorbingGridAxiomAudit.lean` with twenty-two appended `#print axioms` commands also compiled without warnings/errors. Every definition/theorem reports only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The temporary probe was deleted, and the compiler slot released immediately.

SHA-256:

- `.local/PolicyLearningAbsorbingGrid.lean`: `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef`.
- Integrated `Formalization/Generative/PolicyLearningAbsorbingLipschitz.lean`: `65c20456263f0ce790b7da68951776a01bc08dcd313ed09f6da07c7f25f361fe`.
- Integrated `Formalization/Generative/PolicyLearningAbsorbingPreservation.lean`: `883eb9411a0f9aadad8631346a3d5149d256a6fa610d1c769b4d66070c06bb71`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

All imports already target production module paths. This is builder validation against the integrated dependencies; source fidelity, named-environment coverage and actual production export integration require a separate independent review.
