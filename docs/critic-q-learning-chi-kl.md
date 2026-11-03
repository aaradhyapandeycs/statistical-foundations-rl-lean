# Source-only independent audit: supported finite-row KL ≤ chi-square

Exact inspected source: `.local/QLearningChiKLDraft.lean`, SHA-256 `ba7bd9d077a7cb3658fbe9722602baac445a7ef6e6f50a7eb45a8f96fc6429e7` (recomputed). No compiler was used for this review. The builder reports compilation; this note provides independent source/semantic review only, not independent compile/axiom or production approval.

**Verdict:** the three public helpers faithfully establish the supported-row step used in source `lemma:Q-comparison-facts` (ii), `generative_model_model_free.tex:2660–2673`: KL(q||p)≤chi²(q||p), with the correct orientation and support convention. They do not establish the trajectory chain rule, random-horizon law, Pinsker step, optimal-Q comparison, or whole part (ii).

## Binder audit

Each row below is an expanded binder of the indicated export. Counts per public export: TYPING 2, STANDING 2, SOURCE 1, RULED 0, EXCESS 0. The helper source domain consists of arbitrary actual probability rows with q supported on p; no radius assumption is needed for the first inequality.

| Export | Binder | Classification | Mathematical role |
|---|---|---|---|
| `qChi_finiteKLExpression_le` | implicit `State : Type*` | TYPING | Source finite state carrier |
| same | `[Fintype State]` | TYPING | Source finite sums |
| same | `p : FiniteDistribution State` | STANDING | Actual nominal normalized nonnegative probabilities |
| same | `q : FiniteDistribution State` | STANDING | Actual alternative normalized nonnegative probabilities |
| same | `hs : ∀x,p(x)=0→q(x)=0` | SOURCE | Source uncertainty-set zero-support restriction |
| `qChi_rowMeasure_absolutelyContinuous` | implicit `State : Type*` | TYPING | Same carrier |
| same | `[Fintype State]` | TYPING | Finite discrete law |
| same | `p : FiniteDistribution State` | STANDING | Nominal actual row |
| same | `q : FiniteDistribution State` | STANDING | Alternative actual row |
| same | `hs` | SOURCE | Same explicit support restriction |
| `qChi_rowKL_le` | implicit `State : Type*` | TYPING | Same carrier |
| same | `[Fintype State]` | TYPING | Finite discrete law |
| same | `p : FiniteDistribution State` | STANDING | Nominal actual row |
| same | `q : FiniteDistribution State` | STANDING | Alternative actual row |
| same | `hs` | SOURCE | Same support restriction |

`FiniteDistribution` expands to the mass function, coordinate nonnegativity and total mass one. There is no strict positivity/full-support premise, arbitrary kernel, hidden nonempty instance, probability bound, KL gate or target-shaped estimate. The named local measurable-space instance fixes State to the full discrete sigma algebra; it is a source convention implemented in the module, not a freely supplied logical premise.

## Zero support and actual laws

`qChiSquared p q` is the actual sum over p(x)>0 of (q−p)²/p. Both sums of p and q on this support are proved equal to one; the latter uses hs. The centered mass correction sums to zero. For positive p and q the pointwise log bound is log z≤z−1. At q=0 the summand is treated separately and the correction exactly cancels its chi-square term. At p=0, hs forces q=0 and the discarded term is zero. No cancellation by a zero nominal mass occurs. Omitting hs would invalidate the meaning of this comparison under totalized division/log; the file does not omit it.

The absolute-continuity theorem independently proves `q.rowMeasure ≪ p.rowMeasure`: support(q)⊆support(p) is derived from hs and actual PMF masses, then transferred to arbitrary null sets. It does not assume full support or infer absolute continuity merely from a real expression.

`rowMeasure` is `d.toPMF.toMeasure`, with the existing probability-measure instance. The private singleton characterization derives its real singleton mass equals d.prob(x). Thus the final theorem concerns the actual finite probability measures, not just a formal density expression.

## Real KL and finiteness

`finiteKLExpression` is the total real sum Σ q(x)log(q(x)/p(x)). Its agreement with actual KL is invoked only after the proved absolute continuity, through `finite_klDiv_eq_expression_of_ac`. That dependency requires actual finite probability laws and measurable singletons and proves the exact `klDiv.toReal` equality, with nominal-zero atoms handled using absolute continuity.

The final export states `(InformationTheory.klDiv q.rowMeasure p.rowMeasure).toReal ≤ qChiSquared p q`. A `.toReal` inequality alone could conceal infinite KL because infinity maps to zero. Here that loophole is ruled out mathematically: the same dependency module proves `finite_klDiv_ne_top_of_ac`, and the file has already established its entire premise. Finite State makes the likelihood log integrable (`Integrable.of_finite`). Finiteness is derivable on the exact declared domain, although it is not separately exported in this file. A later chain-rule or ENNReal comparison should explicitly consume that finiteness theorem rather than treating `.toReal` as an unconditional equivalence.

For q in the actual ball, its membership supplies both hs and chi-square≤rho, so the source row KL≤rho follows by transitivity. The current export is the stronger radius-free row step, not a complete ball/trajectory wrapper. Zero rho, identical laws, degenerate supports, and singleton states are permitted. There is no inappropriate γ restriction; this row inequality is independent of discount.

## Dependency snapshot and remaining evidence

Inspected production dependency hashes: `GenerativeLowerBoundFiniteKLDataProcessing.lean` `471ec68b7d653a1bdace8e73097dbd5f85c5d7f9c5e6f4d714759a52b1c88aa9`; `EmpiricalRow.lean` `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`; `QLearningRobustComparator.lean` `e5ce5615897b68911374e0b5f58aab1254f03fcae75d44040cc7f46f9b549661`.

No semantic obstruction found in the exact helper statement or proof route. Required before integrated completion: independent exact-source compilation and transitive axiom probes (including the KL-expression bridge), actual export integration, and separate review of any ball, finite-trajectory, or random-geometric-horizon consumption. No whole source theorem certification is made here.

## Independent exact-source compilation and axiom evidence

The allocated focused audit subsequently compiled an exact byte copy into fresh isolated `.local/chi-kl-independent-review/QLearningChiKLDraft.olean`, invoking `bash scripts/lean-local.sh` against actual built production dependencies. Both the original and copied source recompute to `ba7bd9d077a7cb3658fbe9722602baac445a7ef6e6f50a7eb45a8f96fc6429e7`. `compile.log` is empty and compilation exits zero. No builder staged olean was reused for the target.

A fresh import-only `ImportAudit.lean`, with the isolated output first on its import path and actual production/package dependencies thereafter, probes all three public exports plus `finite_klDiv_eq_expression_of_ac` and `finite_klDiv_ne_top_of_ac`. `axioms.log` reports only propext, Classical.choice and Quot.sound for all five. All evidence is in `.local/chi-kl-independent-review`. The private singleton lemma is transitively covered by the public measure-KL export. No source edit was necessary.

Verdict now includes independent exact-source compilation and transitive axiom verification for this staged helper. Actual production export verification, trajectory/geometric-horizon consumption and whole part-(ii) source closure remain separate. The compiler slot was released before this evidence was appended.

## Production integration

The reviewed finite-row KL-to-χ² result is now integrated as `Formalization/ModelFree/QLearningChiKL.lean`; the trajectory stability theorem remains separate. The declaration and proof bodies match the reviewed staged source; imports or status comments were updated where required. The project-wide check compiled 250 modules and audited 3,333 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
