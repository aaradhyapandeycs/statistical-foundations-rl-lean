# Whole-monograph progress

## VI-LCB main theorem (Theorem 6.3)

Theorem 6.3 is proved as printed (constants read as ∃c_b₀ ∀c_b ∃c₁), combining Lemmas 6.2 (corrected), 6.4, 6.5 (corrected), 6.6 and the Lemma 6.7 provider with its premises discharged for the algorithm output. Independently source-reviewed. The named-result ledger now has 73 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Q-learning lower bound: restricted Theorem 4.7 and Lemma 4.15; source issues C30, C31

Theorem 4.7 is indexed as `Thm4_7_restricted` (constant learning rates; the rescaled-linear case is not proved in the source, C30) and Lemma 4.15 as printed, with printed-proof slips repaired (C31). Both independently source-reviewed. The named-result ledger now has 72 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## LCB-Q: Lemma 6.9, restricted Lemmas 6.10 and 6.12, corrected Theorem 6.8; source issues C28, C29

The LCB-Q algorithm is modelled (`Formalization/OfflineRL/LCBQ*.lean`). Lemma 6.9 is proved as printed; Lemma 6.10 is indexed as `Lemma6_10_restricted` because the printed lemma omits the large-c_b premise and is false without it (C28). Lemma 6.12 is indexed as `Lemma6_12_restricted` under the sufficient premise log(SAT/δ) ≥ 1 (C24), with printed-proof gaps repaired (C29). Theorem 6.8 is indexed as `Thm6_8_corrected` (log² in the sample-size condition, C24). All independently source-reviewed. The named-result ledger now has 70 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Online minimax lower bound (Theorem 5.19, Lemmas 5.20, 5.21)

Theorem 5.19 and Lemmas 5.20–5.21 are proved as printed, using a new finite adaptive-data KL chain rule (`Formalization/Probability/AdaptiveKL.lean`) in place of the printed reductions; proof gaps in the printed argument are recorded as C25–C27. All independently source-reviewed. The named-result ledger now has 66 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Lemmas 6.6, 6.18 and corrected Theorem 3.7; source issue C24

Lemma 6.18 is proved in conditional-on-counts form and Lemma 6.6 for sampled pairs (zero-count case disclosed; the printed covering step is repaired, C23). Theorem 3.7 is indexed as `Thm3_7_corrected` on the weakest domain the counterexamples allow (C1, C2). Theorem 6.8 is recorded as false as printed (C24, needs log²). All independently source-reviewed. The named-result ledger now has 63 covered entries out of 90 (3.7 as a corrected variant). The complete monograph remains **INCOMPLETE**.

## Offline minimax lower bound (Theorem 6.13)

Theorem 6.13 (`thm:infinite-lwoer-bound`) is newly proved with its printed hypotheses (Gilbert–Varshamov packing, value gap, concentrability, dataset KL chain rule, Fano), indexed as `Thm6_13` and independently source-reviewed (no blocking or major findings). The named-result ledger now has 60 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Fano's lemma (Lemma 2.10)

Lemma 2.10 (`lem:fano`, both parts) is newly proved in `Formalization/Probability/Fano/FanoLemma.lean` over the existing test-risk definitions and indexed as `Lemma2_10`; it was reviewed by an independent source critic with no blocking, major or minor findings. The named-result ledger now has 59 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Statement index: Lemmas 2.4, 2.5, 2.12, 6.15 and restricted Lemma 6.11

Lemmas 2.4 (Hoeffding) and 2.5 (Bernstein, both displays) are indexed over existing proofs; the
whole-matrix clause holds for any cross-row dependence. Lemma 2.12 (KL tensorization for finitely
many probability measures on arbitrary measurable spaces) is ported from its independently
reviewed private proof. Lemma 6.15 (transition KL bound for the offline hard family) is newly
proved with explicit universal constant `c₃ = 16·336²`; the printed proof's mis-cited Bernoulli
KL step is recorded as [C21](SOURCE-ISSUES.md#candidate-c21-mis-cited-bernoulli-kl-step-in-the-offline-transition-kl-lemma).
Lemma 6.11 (`lemma:useful`) is newly proved with explicit constant 84 under the premise
`log(SAT/δ) ≥ 1`, disclosed as a restricted variant; the printed lemma is false without some such premise ([C22](SOURCE-ISSUES.md#C22)). The named-result ledger now has 58 covered
entries out of 90. The complete monograph remains **INCOMPLETE**.

## Statement index: Lemmas 2.6 and 2.11, restricted Lemmas 6.7 and 6.14, and the occupancy flow equation

The discounted state occupancy now has a proved flow equation `d = (1−γ)ρ + γ dᵀP_π`
(`MDP/DiscountedOccupancyFlow.lean`). With it, the variance-propagation bound of Lemma 6.7 is
proved for the actual optimal-greedy rows and occupancy, for every value vector and penalty
satisfying the premises the source proof uses; this is indexed as `Lemma6_7_restricted` and
disclosed in SOURCE-ISSUES, since deriving those premises for the VI-LCB output on the
Theorem 6.3 event remains open. Lemma 2.11 (reverse Fano bound) and Lemma 2.6 (empirical Bernstein inequality) are ported from
their independently reviewed private proofs together with their provider modules (10 and 43).
Lemma 6.14 (values and optimal policies of the offline hard family) is newly proved by a
Bellman-optimality fixed-point verification, which also supplies the source's final attainment
step; it is indexed as `Lemma6_14_restricted` because the optimal action at s>0 is identified
only for ε>0 (at ε=0 the two actions tie; disclosed in SOURCE-ISSUES). Each entry passed
an independent review. A fresh full `python3 scripts/check.py` from empty project build artifacts
compiled all 1,115 project modules and the axiom audit passed for 9,328 declarations with only
`propext`, `Classical.choice` and `Quot.sound` ([evidence](validation/index-batch-20261106/)). The named-result ledger now has 53 covered entries out of 90.
The complete monograph remains **INCOMPLETE**.

## Statement index: Lemma 3.8

Lemma 3.8 (properties of the two hard generative-model instances) now has its full entry: the
parameter relations, the strict optimal-Q separation for the actual two-state source MDPs and the
ratio identity, applying existing proofs. To keep the Chapter 3 statement file definition-only,
`hardRow` and `hardMDP` moved verbatim to `Generative/GenerativeLowerBoundTwoStateDefinitions.lean`;
all 50 dependent modules were recompiled. An independent review passed; the axiom audit passed
for 8,946 declarations with only `propext`, `Classical.choice` and `Quot.sound`. The named-result
ledger now has 49 covered entries out of 90. The complete monograph remains **INCOMPLETE**.

## Statement index: Lemmas 3.6 and 4.14

Lemma 3.6 (empirical value residual, on the event `eq:Bernstein-empirical-optimal-value`, for
every empirically optimal deterministic policy) now has its statement entry and applying wrapper
over the existing self-bounding proof. Lemma 4.14 (optimal values of the 4-state Q-learning hard
MDP) is newly proved: the source construction is defined in
`ModelFree/QLearningHardMDPDefinitions.lean`, with the source's state-dependent action sets encoded
by two actions per state (copies at single-action states), and all printed V⋆/Q⋆ values are
derived for every 1/4 < γ < 1. Both entries passed independent source-fidelity reviews; the
changed modules and dependents were recompiled and the axiom audit passed for 8,938 declarations
with only `propext`, `Classical.choice` and `Quot.sound`. The named-result ledger now has 48
covered entries out of 90 inventoried environments. The complete monograph remains
**INCOMPLETE**.

## Statement index: five more chapter results

Five source results now have full statement-index entries with applying wrappers:
Lemma 2.7 (Bernoulli tails), Lemma 2.13 (Bernoulli KL bounds), corrected Lemma 4.3
(TD step-size weights, [C5](SOURCE-ISSUES.md#candidate-c5-missing-premise-in-td-step-size-lemma-43)),
Lemma 4.9 (Q-learning step-size weights) and Lemma 5.17 (online Q-learning rate
properties). Lemmas 2.7, 4.3 and 5.17 index results that were already proved; Lemma 2.13
adds a proof of the comparison KL(p‖q) ≤ KL(q‖p) for 1/2 ≤ q < p < 1, and Lemma 4.9
assembles the existing weight bounds into the full printed lemma. Each entry passed an
independent source-fidelity review. The changed modules and their dependents were
recompiled against the previously verified build, and the axiom audit passed for 8,905
declarations with only `propext`, `Classical.choice` and `Quot.sound`; CI repeats the full
build. The named-result ledger now has 46 covered entries out of 90 inventoried
environments, including disclosed corrected or restricted variants. This is not a
percentage of all work needed. The complete monograph remains **INCOMPLETE**.

## Online Q-learning source proof verified

The actual online Q-learning regret and joint optimism/error results now have
their full Chapter 5 statements and applying wrappers, independent source
reviews, and a fresh full project check. All 20 previous Chapter 5 wrappers
are preserved. Definitions are separated from proof imports without changing
the mathematical declarations.

The exact scope is one fixed deterministic maximizing tie and initial
nonterminal V=H. Theorem 5.16 retains cb=2 and the original bonus logarithm,
with an explicit universal soft-O rate; Lemma 5.18 retains both clauses.
[C20](SOURCE-ISSUES.md#C20) explains the completion and printed-proof repairs.
The unmodified `python3 scripts/check.py` compiled all 1,052 project modules
from empty project artifacts and audited 8,873 declarations with only
`propext`, `Classical.choice` and `Quot.sound`. No project OLeans were reused;
the pinned dependency artifact metadata and all source hashes were preserved.
See the [verification and scope record](online-qlearning-source-verification.md).

Size: 101,188 physical project Lean lines including comments and blank lines,
6,065 more than the preceding published main. The named-result ledger has
41 covered entries out of 90 inventoried environments, including disclosed
corrected or restricted variants. This is not a percentage of all work needed.
The complete monograph remains **INCOMPLETE**.

Previous checked batch: the Chapter 6 scoped variants passed a fresh full
938-module build and the axiom audit for 8,414 declarations on 2026-11-05.
See [the verification and scope record](ch6-corrected-variants-evidence.md)
for the exact manifest, restrictions and reproduction command. The complete
monograph remains incomplete; the named-result ledger distinguishes original
results from corrected or restricted variants.

Status: **active; incomplete**. Source: arXiv:2610.41903v1, 326 PDF pages.

No whole-paper or chapter completion is certified. Source-level claims need
an exact Lean statement, all mathematical prerequisites, compilation, an axiom
audit, and independent correspondence review before promotion.

## Original VI/PI and corrected MVP main result verified

- Original Lemma 2.1 now has its complete two-clause Chapter 2 Prop and
  applying wrapper: arbitrary VI initialization, arbitrary initial stationary
  randomized PI policy, all maximizing greedy ties and the printed γ^k rate.
  Proved trajectory/fixed-point and optimality identities justify the value
  representation. Genuine definition extraction preserves existing theorem
  signatures and proof bodies.
- Corrected Lemma 5.14 now proves all three displayed decoupling inequalities
  on one actual-law event, including K=1. Actual learner-family membership,
  corrected terminal-zero values, per-stage row/rank sums, transcript laws
  and event transfer are proved, rather than confidence premises.
- Corrected MVP main regret holds for every positive H,K and 0<δ<1:
  R ≤100 max(1,I) min(√(SAH³K),HK) with probability at least 1−δ.
  C=100 is universal, c₁=4,c₂=16, I and reciprocal δ′ are explicit.
  Small regimes and K=1 are direct; the large regime discharges the actual
  decoupling probability and source eligibility internally.
- The zero-count rule, trigger convention, confidence allocation, ceiling
  profile cover, auxiliary terminal zero and one fixed tie remain explicit
  corrections or proof-scope repairs (C8/C12/C13/C15/C16/C17).
- A fresh project-only `python3 scripts/check.py` rebuilt all 913 modules
  with zero project-artifact reuse. The audit checked 8,162 declarations
  with only propext, Classical.choice and Quot.sound. Pinned dependency
  caches were used without rebuilding; path/size/mtime metadata matched
  before and after. No package-byte seal or dependency clean build is claimed.
- Size: 92,344 Lean lines including comments/blanks. The ledger has
  23 original-result entries including existing disclosed restrictions, plus
  12 corrected variants. No whole chapter or monograph is certified.
- Next: remaining Chapter 2 concentration statements and the other open
  source environments throughout the monograph. Private drafts stay uncounted.

## Chapter 2 policy-matrix resolvent lemma verified

- Original Lemma 2.3 is proved for every stationary randomized policy and
  both policy transition matrices, including discount zero. The inverse is
  proved to exist, has the printed Neumann expansion, maps the all-ones vector
  to the geometric horizon, has the book's maximum row-wise absolute-sum norm,
  and has nonnegative entries. The full statement and applying wrapper are in Ch2.
- Qualification compiled four providers and both index modules and probed
  14 actual exports. Affected integration rebuilt 8 modules and verified
  reuse of 829, for 837 total; 7,616 declarations passed the standard-axiom
  audit. This is an affected check with retained ancestry, not a fresh clean build.
- Size: 84,866 Lean lines including comments/blanks. The ledger now has
  22 original-result entries, including existing disclosed restrictions, plus
  10 corrected variants. No chapter or whole-monograph completion is claimed.

## Chapter 2 Azuma–Hoeffding inequality verified

- Original Lemma 2.8 is proved for arbitrary probability spaces, deterministic
  varying bounds, natural prior-increment conditioning, strict confidence and
  zero-time/zero-proxy endpoints. The complete Prop and applying wrapper are
  in the Chapter 2 statement index.
- Qualification compiled seven providers and both full index files and probed
  12 actual exports. Affected integration rebuilt 11 modules and verified
  reuse of 822, for 833 total; 7,597 declarations passed the standard-axiom
  audit. This is an affected check with retained ancestry, not a fresh clean build.
- Size: 84,618 Lean lines including comments/blanks. The numbered ledger is
  now 21 original results plus 10 corrected variants; no chapter or whole-book
  completion is claimed.

## Corrected actual MVP joint T2/T3/T4 displayed bounds verified

- The three source estimates hold on one actual sequential experiment with
  the printed 4 log₂(K) δ′ failure coefficient, K≥2, fixed 4/16 coefficients,
  C8/C12/C13/C16 and one fixed maximizing tie. Concentration tail parameters
  vary while the planner remains fixed at the same corrected δ′.
- The full statement and applying wrapper expose the actual successor and
  the true value of the deployed episode policy. The displayed source's
  standing K≥SAH·Iota condition is retained. The optimism/T2/T5 displayed
  entries also retain it; the stronger library exports are unchanged.
- Qualification: fourteen providers and twenty-seven actual-export checks,
  then the source-expression bridge and two full Chapter 5 files. Affected
  integration: 19 rebuilt + 807 verified reused = 826 modules;
  7,575 declarations with permitted standard axioms. This is an affected
  check with retained reuse evidence, not a fresh clean 826-module rebuild.
- Size: 84,223 Lean lines including comments/blanks. The numbered ledger
  remains 20 original entries with their existing disclosures plus 10 corrected
  variants. Lemma 5.14, the main MVP theorem and the whole monograph remain open.

## Corrected actual MVP T2 and T5 displayed bounds verified

- T2 holds deterministically for K≥2 with fixed c₁=4,c₂=16, using the
  actual retained-row count and factor-four reciprocal budget. T5 holds for
  every K≥1 on the actual sequential law; the K=1 branch is direct for
  arbitrary positive H, and the source natural-log failure coefficient is
  retained. Both use C8/C13/C16 and one fixed greedy tie.
- Qualification: six T2 and eleven T5 providers, eight and fourteen export
  probes, and two full Chapter 5 files with seventeen applying-proof probes.
  Affected integration: 21 rebuilt + 790 verified reused = 811
  modules; 7,489 declarations with permitted standard axioms. This is an
  affected check, not a fresh clean 811-module build.
- These displayed claims add no numbered ledger entry: 20 original named
  results with existing disclosures and 10 corrected variants remain. Source
  Lemma 5.14 and the full MVP regret theorem remain open.

## Corrected MVP T6 variance lemma verified

- Corrected Lemma 5.15 (`lem:bound-T6-ucb-mvp`, onlineRL.tex:1822–1833)
  proves T6 ≤ 4H T2 + 4H W4 + KH²I with probability at least 1−4SAHKδ′
  under the actual sequential reset/transition law, including K=1 by a direct
  zero-variance argument. No conditional-martingale or concentration estimate
  is inserted as a premise of the final export.
- T2 uses the printed bonus at positive stored counts and analysis charge H
  at zero (C8). Other disclosed conventions remain C13 power-of-two triggers,
  C16 reciprocal δ′, and a fixed maximizing tie. The printed numerator-100
  confidence allocation is not certified by this result.
- The actual retained continuation process, predictable conditional variance,
  T8 confidence estimate, greedy episode telescope and scalar closure are
  proved. Five statement-facing definitions were extracted without changing
  their bodies; the complete Chapter 5 Prop has definition-only imports and
  its wrapper applies the final library export.
- Qualification: 30 canonical modules and 45 exports, then both complete
  Chapter 5 files and 15 applying-proof exports. Affected integration:
  34 rebuilt + 760 verified reused = 794 modules; 7,417
  project declarations with only permitted standard axioms. This is an
  affected check with retained reuse evidence, not a new clean full check.
- Size: 82,034 Lean lines including comments/blanks in 794 files. Ledger:
  20 original named entries with existing disclosures and 10 separate
  corrected variants. No complete chapter or monograph is certified.
- Independent source, transformation, statement and evidence reviews passed.
  Terra built the T6 providers; coordinator integrated and audited; an
  independent critic checked source correspondence and actual consumption.
- Next: actual future-family concentration, adaptive decoupling (Lemma 5.14),
  remaining MVP variance/bonus bounds and full regret. Private helper builds
  are not counted as source-result closure.

## Corrected actual-law MVP optimism verified

- The displayed optimism claim at onlineRL.tex:1480–1487 is proved for the
  actual sequential episode law, with the same reset distribution, causal
  retained-history planner and realized transcript. All episode/stage/state/
  action values are covered at probability at least 1−2SAHKδ′. No batch-event
  probability or table-equivalence certificate is assumed by the final theorem.
- The operational histogram, selected batch, finite stack read, history stage
  table and planner are linked by proved pathwise identities. A product-law
  batch event is lifted through independent resets and the proved sequential
  transcript-law equality. Counts 0–2 use the capped deterministic branch.
- Explicit corrections remain C8 zero-count completion, C13 power-of-two
  trigger, C16 reciprocal confidence allocation, and one fixed greedy tie.
  Recomputing the retained table each episode is extensionally equivalent to
  caching it between triggers; no imperative cache interpreter is claimed.
- Qualification passed seven model targets with 50 theorem exports, seventeen
  optimism targets with 26 exports, and both full Chapter 5 files with fourteen
  statement-proof exports. Affected integration: 28 rebuilt+736
  verified reused=764 modules; 7,269 declarations with standard axioms.
- Size: 79,918 Lean lines including comments/blanks in 764 files. The named
  ledger stays at 20 original entries with existing disclosures and nine
  corrected variants: this new result is a displayed claim, not a numbered
  source environment. No complete chapter or monograph is certified.
- Ownership: Data — committed model, sampler and history-table identities;
  Terra — batch concentration, optimism and sequential-law transport;
  coordinator — definition extraction, complete index, qualification and
  integration; independent critic — source/consumption and evidence checks.
- Next: corrected terminal-zero fixed-profile families, actual learner-value
  membership, decoupling and the remaining MVP variance/regret argument.

## Corrected full MVP uniform concentration verified

- Corrected Lemma 5.13 now retains both displayed inequalities and the
  source coefficient 40000 under the actual expanded product law. It uses
  δ′=δ/(100S²A²H²K²); the printed numerator 100 allocation remains refuted
  (C16). The continuation-family endpoint is explicit, without a generic
  terminal-zero premise.
- All monotone ceiling profiles and arbitrary finite families depending on
  the full strictly-future sample block are covered simultaneously. These
  stronger classes include the printed profile/empirical-summary families.
  Size≤K+1, inclusion of zero and range[0,H] are the source family premises;
  the covering/logarithmic/variance bounds are derived in the proof.
- The full statement and applying wrapper compile. The wrapper uses event
  inclusion and a small abstract-real algebra lemma; no heartbeat increase
  or statement change was needed. Qualification: 19 targets and 31 actual
  exports passed. Affected integration: 21 rebuilt+719 verified
  reused=740 modules, 6,951 standard-axiom declarations.
- Size: 77,558 Lean lines including comments/blanks in 740 files. Ledger:
  20 original named entries with their existing disclosures, nine corrected
  variants. No chapter or whole-monograph completion is certified.
- Ownership: coordinator — corrected source-constant proof, complete index,
  qualification and integration; independent critic — source, definitions,
  mapping, actual exports and final evidence. Data — actual retained sampler
  and corrected terminal-zero value/profile bridge; Terra — actual batch
  event transfer and optimism. Their unfinished downstream work stays private.
- Next: actual learner-value family membership, corrected auxiliary values,
  probability transfer to the online experiment, MVP optimism and regret.

## MVP probability infrastructure and uniform-bound counterexample

- The actual expanded product law now has proved fresh-coordinate conditional
  moments, a reverse-stage reveal filtration, exact batch variance and error
  identities, fixed-mask Freedman bounds, finite unions and uniform coverage
  of finite future-dependent families with sample-dependent vector choices.
  The bound retains its explicit profile/choice/level/mask logarithm.
- Generic Lemma 5.13 fails under the natural bounded h+1 continuation-family
  reading at S=2,A=H=1,K=4. The Lean witness gives iota=1, both K-regimes,
  an empty necessary event under the actual product law and a strictly
  positive probability promise. The source's H/H+1 family ambiguity and
  absence of a generic terminal-zero condition are disclosed as C16.
- C17 records a separate source-level failure of the auxiliary value-family
  identification: its terminal value H differs from the learner's zero.
  This argument gap does not refute the final MVP regret conclusion. A full
  Lean execution witness and corrected actual-value coupling remain open.
- Qualified 39-provider compilation and a 73-export probe passed. Guarded
  affected integration: 9 rebuilt+714 verified reused=723 modules;
  6,876 project declarations permit only the standard three axioms.
- Size: 76,666 Lean lines including comments/blanks in 723 files.
  Ledger remains 20 named entries with existing disclosures and eight
  corrected variants. Neither generic infrastructure nor the false original
  Lemma 5.13 is counted as a newly completed source result.
- Ownership: Terra — actual-product probability and finite-family proofs;
  coordinator — counterexample, qualification and integration; independent
  critic — source/endpoint, all actual exports and final receipts. Data's
  committed-histogram and empirical-row work remains quarantined until its
  actual kernel/profile bridge is completed and independently reviewed.
- Next: the corrected confidence allocation and numerical source bound,
  actual batch/profile kernels, corrected auxiliary values and online
  coupling. Every complete-chapter and whole-monograph claim remains open.

## MVP profile and stored-count conclusions verified

- Lemma 5.11's printed profile-cardinality bound is proved for every finite
  episode-by-stage state-action row table, a superset of the algorithm's
  realized traces. It retains K≥SAH log₂K and the exact printed RHS, and
  handles K=1 explicitly. The safe ceiling family includes every actual
  profile; the printed intermediate rounding gap is recorded as C15.
- The corrected power-of-two trigger variant of Lemma 5.12 is proved for K≥2 from the actual
  cumulative/pending/stored counter fold, for arbitrary chronological traces
  with the constructed stage clock. The power-of-two trigger interpretation
  follows the source doubling prose. Its pointwise factor-two argument fails
  (C13), while a dyadic-block proof establishes the final factor4 sum.
- Both full statements import definition modules only; applying wrappers
  consume the actual exports. The combined index's 12 proof exports passed
  the focused axiom probe. Affected integration: 17 rebuilt+
  667 verified reused=684 modules; 6,658 declarations with only
  propext, Classical.choice and Quot.sound.
- Size: 74,861 Lean lines including comments/blanks in 684 files.
  Ledger: 20 original named entries with existing disclosures and eight
  corrected variants. No complete chapter or monograph is certified.
- Ownership: Terra — operational count builder; Data — profile cardinality
  and cumulative/operational bridge; coordinator — full index and integration;
  independent critic — source, definition bodies, guards and final evidence.
- Next: actual expanded-law uniform concentration, its random-profile
  application, and the MVP regret proof. Single-row probability helpers are
  private prerequisites; they are not the completed uniform source lemma.

## Signed variance error verified and repaired

- The second clause of Lemma 5.22 (`lemma:sqv`, onlineRL.tex:3612–3615) is
  false as stated for a general signed random variable. A two-point law
  with probabilities 1/8 and 7/8 at 1 and −1 has Cmax=1, mean−3/4, variance7/16,
  and centered-square variance63/64. The printed coefficient 1 bound fails.
- The witness uses Mathlib's actual probability-measure variance, with a
  measurable coordinate sample under the finite product law. Its exact
  mean and both variances are linked to verified finite expectations.
- Both corrected inequalities with coefficient 4 are proved for an arbitrary
  probability space and measurable |X|≤C. The first printed inequality
  already had 4; only the centered-square coefficient changes. No separate
  integrability or MemLp hypothesis is added. See SOURCE-ISSUES C14.
- The nonnegative [0,C] special case with centered-square coefficient 1 is
  valid and remains available. The published UCBVI theorem uses valid
  bounds, so this general-lemma error does not invalidate its Lean proof.
- The full statement/applying wrapper, three provider modules and actual
  export probes passed. Affected 671 integration: 7 rebuilt+
  664 verified reused; 6,484 declarations audited with standard axioms.
- Size: 73,559 Lean lines including comments/blanks in 671 files. Ledger:
  19 original named entries with existing disclosures, seven corrected
  variants. The printed false Lemma 5.22 is not counted as an original.
  Other chapter obligations and the entire monograph remain incomplete.
- Ownership: coordinator — finite signed witness and source issue;
  Terra builder — general measure proof, exact variance bridge and index;
  independent critic — raw source, counterexample, scope and final evidence.

## Printed inverse-visit count lemma verified

- Lemma 5.3 (`lem:sum-inv-Nhk-ucbvi`, onlineRL.tex:638–646) now has the
  printed 2SAHlog₂K bound on the sum of 1/max(N,1), for K≥2. First visits
  contribute one; the earlier zero-totalized reciprocal helper is not used
  as a substitute for this printed denominator.
- The proof reindexes exact strict-past visit ranks. A row with N visits
  contributes 1+harmonic(N−1); the N=0/1 cases and the logarithmic comparison
  are proved. Actual pre-episode row counts are linked to those ranks.
- The result generalizes the source's algorithm trajectory to any causal
  episode planner and finite path. It assumes no probability event, bonus
  condition, positive count, independence or concentration estimate.
- The full Chapter 5 Prop spells the denominator inline, uses the printed
  episode-major sum order and has no proof-module import. Its applying
  wrapper commutes finite sums and consumes the actual pathwise export.
- The affected 668 check passed: 6 rebuilt+662 verified reused;
  6,460 declarations audited with only the standard three axioms.
- Size: 73,339 Lean lines including comments/blanks in 668 files. Ledger:
  19 original named entries with existing disclosures, six corrected
  variants. Other chapter results and whole-monograph work remain open.
- Ownership: Data builder — generic rank/harmonic calculation, actual path
  bridge, pure count definition and source index; coordinator — integration
  and publication; independent critic — source, signature, import and
  terminal source/artifact evidence.

## Corrected main UCBVI regret theorem verified

- Theorem 5.2 (`thm-ucbvi-regret`, onlineRL.tex:472–482) is proved for the
  explicit finite zero-count algorithm (C8) and a fixed maximizing tie rule.
  For every K≥1 and 0<δ<1, its actual regret is at most
  20(√(SAH³K)+S²AH³)(1+iota) with probability at least 1−δ. Universal bonus
  constants 4 and 16 are independent of all model/confidence parameters.
- Regret compares the true optimal value and the true value of the policy
  actually selected for each episode, at its observed initial state. The
  probability law uses iid initial resets and the actual causal transitions.
  No intermediate event, variance estimate or regret certificate is assumed.
- K=1 and the small-sample regime are handled by regret≤KH. For large K,
  the proved T0 and T5/T6 events imply the scalar closure; their 39Mδ′
  failure budget is at mostδ under the printed confidence allocation.
  The auxiliary K≥2 restrictions therefore do not restrict this theorem.
- The affected 666 check passed: 11 rebuilt+655 verified reused;
  the full audit checked 6,443 declarations with only the standard axioms.
  Source review and exact statement/applying wrapper checks passed.
- Size: 73,062 Lean lines including comments/blanks in 666 project files.
  Ledger: 18 original named entries with existing disclosures and six
  corrected variants. Other chapter 5 algorithms, remaining chapters and
  substantive prose obligations remain open; no whole chapter or book closure.
- Ownership: Terra builder — actual regret, sharp scalar/T0 closure and
  final theorem; Data builder — unconditional suffix/T56 prerequisites;
  coordinator — integration/publication; independent critic — source
  semantics, quantified rate/constants, all branches and terminal evidence.

## Complete corrected T5/T6 lemma verified

- Corrected/restricted Lemma 5.9 now has all three initial inequalities with
  the printed 14-confidence coefficient and both simplified inequalities
  with the printed 30 coefficient under the printed large-K condition.
  All quantities use the same actual reset-vector/causal-path law. Literal
  printed T0 and iota appear in the complete Chapter 5 statement.
- The proof discharges the uniform stage-suffix T3 concentration family,
  derives the actual uniform T0/optimism event, and combines the proved T8,
  selected-policy variance and gap estimates. No concentration event or
  variance bound remains an assumed premise of the final source export.
- The chosen universal bonus constants are 4 and 16. Scope remains K≥2,
  the finite zero-count completion/analysis charge H (C8) and a fixed greedy
  tie rule. C12's auxiliary K=1 endpoint is not certified here.
- The guarded affected check passed: 97 rebuilt and 562 verified
  reused modules, covering all 659 project modules; the full audit checked
  6,382 declarations with only the standard three axioms. This is an
  affected build, not a fresh clean full rebuild.
- Project size: 72,393 Lean lines including comments/blanks in 659 files.
  The ledger retains 18 original named entries with existing disclosures
  plus five corrected variants. No whole chapter or monograph is certified.
- The isolated main UCBVI theorem passed source review and qualified
  focused compilation. Its production integration remains separate and
  pending; it is not counted by this milestone.
- Ownership: Data builder — suffix martingale family and unconditional
  probability producer; Terra builder — uniform actual gap/T56 assembly;
  coordinator — simplified event, complete statement/applying proof,
  integration and publication; independent critic — source, imports,
  semantic consumption and terminal evidence.

## Complete corrected joint T2/T3/T4 lemma verified

- Corrected/restricted Lemma 5.8 now has all four printed inequalities on
  one event under the actual reset-vector and causal sequential-path law.
  In particular, it proves the comparison between the two T3 radii, as well
  as the bound on the absolute T3 sum. The exact printed iota, lower-bound
  hypothesis and strict confidence 1−4 log₂(KH) delta-prime are retained.
- T2 is bounded deterministically using first visits and reciprocal counts.
  The T3 proof derives predictable conditional variance and applies Freedman;
  T4 telescopes to episode return minus selected-policy value, with zero
  conditional mean and range H, before applying episode Azuma. No event or
  variance estimate is an unproved premise.
- Scope: K≥2 addresses C12; the finite zero-count completion and analysis
  charge H address C8; the implementation uses one fixed deterministic
  maximizing tie rule. This is a corrected variant of the auxiliary lemma.
- The affected 566-module check passed: 50 rebuilt, 516 verified reused,
  and 5,811 declarations audited with only standard axioms. It is not a
  fresh clean 566-module build. See [verification](online-t234-joint-verification.md)
  and [independent review](critic-online-t234-joint.md).
- Current library: 64,724 project Lean lines including comments and blanks,
  in 566 files. The ledger has 18 original named-result entries with their
  existing disclosed restrictions, plus four corrected variants. No complete
  chapter or monograph is certified.
- Work continues on adaptive T5/T6 bounds, stagewise optimistic-to-policy
  gaps and their joint confidence accounting, followed by final regret.
  Quarantined component drafts are not source completion evidence.
- Ownership: builders — actual T2 count bounds, T3 predictable variance and
  T4 episode concentration; coordinator — joint event, complete statement
  index, integration and publication; independent critic — source semantics,
  actual export consumption, qualification and terminal build evidence.

## Fixed-policy cumulative variance lemma verified

- Original Lemma 5.4 (online-RL source lines 648–658) now has its full
  deterministic-policy statement and an applying proof in the Chapter 5 index.
  Its trajectory law uses the actual policy and true transition rows. The
  expectation bound H² holds for any initial distribution.
- A stronger randomized-policy finite-trajectory bound supplies the proof.
  Total return variance includes action variation and expected tail variance;
  the nonnegative terms are retained before bounding cumulative transition
  variance by the variance of a return in [0,H]. No conditional variance
  certificate is an input.
- The affected 520-module check passed: 11 rebuilt, 509 verified reused from
  joint513, and 5,441 declarations audited with standard axioms. Seven freshly
  qualified modules and the actual statement proof also passed focused probes.
- At this milestone: 59,246 project Lean lines including comments and blanks,
  across 520 files; 18 original named-result entries with disclosed restrictions
  elsewhere, plus three separate corrected variants. No chapter or monograph
  completion is certified. See [verification](online-policy-variance-verification.md)
  and [independent review](critic-online-policy-variance.md).
- At that milestone, joint T2/T3/T4 and adaptive T5/T6 work remained in
  staged drafts. The newer T234 milestone is recorded above.
- Ownership: builder — variance decomposition and finite trajectory budget;
  coordinator — source specialization, statement index and frozen integration;
  independent critic — source semantics, definition extraction, actual export
  consumption, qualifications and verification evidence.

## Complete corrected joint W1/W2/W3 lemma verified

- Corrected/restricted Lemma 5.7 now has all three printed inequalities on
  one actual-law event, the exact printed coefficients and iota, and strict
  confidence 1−12S²AHK delta-prime. Singleton state spaces are included.
- The four-event argument shares one coordinate event and one optimism
  event. For S≥2 its failure budget is (10+4S)SAHK delta-prime; for S=1
  empirical and true expectations coincide, so every W term is zero.
- Scope remains K≥2 (C12), finite zero-count completion (C8), fixed greedy
  tie and the source confidence/bonus domains. T2/T3/T4 bounds, subsequent
  variance budgets and the final regret theorem remain open.
- Ownership: builder — W2/W3 actual-path bounds and joint confidence;
  coordinator — source statement, index wrapper, frozen integration and
  publication; independent critic — mathematical source, helper consumption,
  extracted context, qualification, driver and final verification evidence.
- The affected 513-module check passed: 40 rebuilt, 473 reused from the
  verified477 baseline; 5,423 declarations were audited using only standard
  axioms. This was not a fresh clean513 build. See
  [verification](online-w123-joint-verification.md) and
  [independent review](critic-online-w123-joint.md).
- At that milestone: 58,997 Lean source lines including comments and blanks,
  across 513 project Lean files. The ledger retains 17 original named-result
  entries with disclosed restrictions and three separate corrected variants.
  The joint lemma supersedes the W1-only variant; these counts do not certify
  chapter or monograph completion.

## Restricted W1 clause verified

- The W1 clause of Lemma 5.7 now has its full quantified statement entry and
  proof wrapper, with the printed coefficients, logarithmic factor and
  confidence. It concerns the actual reset/path law, selected rows and the
  same selected policy's true continuation variance.
- Scope remains explicit: K≥2 for the vanishing-log endpoint issue C12,
  the finite zero-count convention C8, and a fixed deterministic greedy tie.
  That milestone covered W1 only; the complete corrected joint result is
  recorded above. T3/T4 concentration and final regret remain open.
- Ownership: builder — deterministic-prefix concentration, adaptive-history
  transfer and actual-path counts/variance aggregation; coordinator —
  readable statement, confidence weakening and integration; independent
  critic — source semantics, transformations, frozen build and final evidence.
- The affected 477-module check passed: 28 rebuilt and 449 reused from the
  verified453 baseline, with 5,240 declarations audited using only standard
  axioms. This was not a fresh clean477 build. See
  [verification](online-w1-restricted-verification.md) and
  [independent review](critic-online-w1-restricted.md).
- Current library: 56,505 Lean source lines including comments and blanks,
  across 477 project Lean files. The ledger has 17 original named-result
  entries with disclosed restrictions and three separate corrected/restricted
  variants. These counts do not measure whole-monograph completion.

## Corrected UCBVI telescope verified

- Corrected Lemma 5.6 now states and proves the full deterministic episode
  telescope for any greedy tie choice, nonnegative bonus coefficients and
  the source confidence range. Its sole semantic correction is the explicit
  H analysis charge at zero visits (SOURCE-ISSUES C8).
- The same actual-path chain supplies the four-term summed decomposition,
  the source-law optimism-to-decomposition probability transfer for the
  existing fixed-tie planner, and the exact fixed-optimal T1=W1+W2 split.
  These give no bound on the terms or final regret rate.
- Builders own the source history/probability chain; the coordinator owns
  definitions extraction, broader parameter helpers, index and integration;
  the independent critic checks source correspondence, scope and transforms.
- The affected 453-module check passed (10 rebuilt, 443 reused from the
  verified447 baseline) and audited 5,097 declarations with standard axioms.
  This was not a fresh clean453 build. See
  [verification](online-regret-telescope-verification.md) and
  [independent review](critic-online-regret-telescope.md).
- The ledger retains 17 reviewed named-result entries with their restrictions,
  plus two separately recorded corrected variants. No chapter or monograph
  completion is certified. Subsequent W1 progress is recorded above;
  T3 filtration and concentration remain separate quarantined continuations.

## Full robust duality lemma verified

- Both source bullets of Lemma 7.1 now have the complete expanded Chapter 7
  statement and proof: actual finite-row primal infima, attained clipped
  objective maxima and all-threshold dominance under the source hypotheses.
  Zero nominal atoms, ties, singleton rows, zero variance and every positive
  radius are included. The former TV-only ledger variant is superseded.
- Ownership: chi-squared witness builders — density, moments, all radius cases
  and full source maximum; statement builder — expanded two-branch Prop and
  proof wrapper; independent critic — source semantics, witness consumption,
  transformation and final statement review; coordinator — baseline guards,
  integration, actual-export probes and publication.
- The affected check passed 13 rebuilt modules and 434 reused from the
  verified TV438 baseline (447 current modules); the full namespace audit
  passed 5,026 declarations with standard axioms only. This was not a fresh
  447-module clean build. See [verification](robust-strong-duality-verification.md)
  and [independent review](critic-robust-strong-duality.md).
- That release brought the ledger to 17 reviewed named-result entries, with their disclosed
  restrictions, and one separate corrected optimism variant. No chapter or
  whole-monograph completion is certified.

## TD main theorem verified

- Theorem 4.1 now has a complete source-facing statement and proof for the
  printed schedule, budget, confidence and full accuracy range. Its endpoint
  uses exactly T samples per state and the actual infinite trajectory value.
  The proof supplies universal witnesses c₁=c₂=1/4 and
  c₃=max(4096, exp(4)/(log 2)^4); no condition on η₀ is added.
- Ownership: coordinator — final integration, exact-T wrapper and statement;
  probability builder — joint-law projection and pathwise output bridge;
  independent source critic — source domains and sampling/value semantics;
  proof critic — concentration events, confidence allocation and helper
  consumption. The projection builder did not independently certify that
  component; the separate source critic reviewed it.
- The clean `python3 scripts/check.py` run passed all 418 modules and audited
  4820 project declarations, allowing only `propext`, `Classical.choice`
  and `Quot.sound`. [Verification](td-main-theorem-verification.md),
  [source review](critic-td-full-accuracy-source-20261104.md),
  [proof-consumption review](critic-td-full-accuracy-consumption-20261104.md).
- That release brought the ledger to 16 named-result entries (including the restrictions
  disclosed there) and one separately recorded corrected optimism variant.
  This is not a percentage of the monograph. No chapter or whole-paper
  completion is certified.

## Statement-index backfill

- The index states the printed Lemma 4.8 and restricts its global learning-rate
  hypothesis when applying the existing, stronger exports. This implication is
  not a source discrepancy; the former C11 finding has been removed.
- Ownership: coordinator — Chapters 2 and 4 and integration; chapter builder —
  Chapter 3; online builder — Chapter 5; independent critic — source review of
  all entries. Changes to existing modules only extract definitions and add
  imports; existing theorem statements and proof bodies are preserved.
- The 16-entry backfill passed the clean 403-module build and transitive
  axiom audit (4720 declarations). See [verification](statement-index-verification.md)
  and [independent source review](critic-statement-index-backfill.md).

## Current checked infrastructure

- A source-level one-episode counterexample shows that the auxiliary online
  W1 bound cannot use its printed vanishing log factor at `K=1`. The
  combined T2/T3/T4 lemma also asks for probability greater than one when
  `K=H=1`. These are
  independently checked and not yet formalized in Lean; the main regret
  theorem is not refuted. See [Candidate C12](SOURCE-ISSUES.md) and its
  [source check](critic-online-k1-iota-obstruction.md).


- A source-level counterexample at `γ=0` shows that the standalone offline
  VI-LCB iteration bound cannot hold on the full preliminary discount domain.
  This example has not yet been formalized in Lean. The main offline theorem
  assumes `γ ≥ 1/2` and is not refuted. See [source issue C10](SOURCE-ISSUES.md).
- A singleton-action generative experiment gives one estimator with zero
  trajectory-Q loss under the actual sampling law for every compatible model.
  It is a conditional obstruction to the literal displayed domain of Theorem
  3.7(i); whether an earlier `A ≥ 2` convention carries forward is unresolved.
  The focused, working-tree and clean-copy checks passed.
  See the [source review](critic-theorem37-singleton-action-obstruction.md).
- A χ² weak-duality bridge lifts the pointwise clipped inequality to a
  comparison of the scalar supremum and the infimum over feasible rows. It
  passed focused, working-tree and clean-copy compilation and axiom audits.
  The reverse inequality and maximum attainment are now completed by the
  full Lemma 7.1 proof above.
- The standalone TD step-size counterexample and the pointwise χ² weak-duality
  helper have passed focused, working-tree and clean-copy compilation and
  axiom audits. Those two helpers alone do not establish the main TD theorem or the full
  robust-duality lemma, respectively; Theorem 4.1 is verified separately above. See the [step-size source issue](SOURCE-ISSUES.md)
  and [χ² review](critic-robust-chi-weak-duality.md).
- A proposed corrected UCBVI implementation proves all-stage actual-trajectory
  optimism under the source's strict factor-two confidence bound for a fixed
  deterministic tie rule and explicit `N=0 → Q=H` convention. Its 41-module
  isolated build and 180-export probes passed, as did the integrated and
  clean-copy checks. This does not certify the literal source algorithm
  where the zero-count bonus is undefined. See the
  [source review](critic-online-corrected-optimism.md).
- The proposed UCBVI zero-count correction is formalized at the scalar update
  level: unvisited rows retain `Q=H`, positive counts use the printed update,
  and small-count saturation and range are proved. A proposed corrected
  planner and optimism result are separately integrated and verified; the
  literal printed-source claim remains open. See the
  [review](critic-online-zero-count-scalar-independent-review.md).
- The χ² robust policy-value foundation defines the infimum over actual
  trajectory values for stationary randomized policies, and proves the
  singleton-action zero-gap mechanism for that policy class. General robust
  optimality and the source lower-bound experiment remain open. See the
  [review](critic-robust-chi-policy-value-independent-review.md).
- A singleton-action counterexample establishes feasible source parameters and
  zero strict-error risk for one fixed estimator against every model pair in
  the stationary-policy interface, under actual product sampling laws. Its
  focused, working-tree and clean-copy compilation and axiom audits passed.
  The full source minimax expression remains separate. See the
  [review](critic-robust-chi-singleton-action-v5.md).
- The policy-evaluation source-radius gap has an all-positive-sample repair
  for every nonempty finite state space, using the actual sampling law and the
  source beta with an explicit sufficient choice `C₀ ≥ 8`. The separate
  sample-complexity theorem was already proved. See the
  [source review](critic-policy-evaluation-source-gap-repair.md).
- A combined proposed correction of the generative policy and Q lower bounds
  uses the shared constant `1/32768` on the explicit restricted domain
  `S,A ≥ 2`, `SA ≥ 16`. The two risk clauses may have different hard models.
  See the [review](critic-generative-lower-bound-combined-correction.md); this
  is not a proof of the original wider-domain statement.
- A reproducible lexical inventory covers the active source include tree. It
  identifies 90 named theorem/lemma/claim environments, 17 algorithms, 1,381
  display environments, and numerous further candidate obligations. These are
  scanner counts, not a proof-coverage percentage or a semantic completeness
  claim. The generated inventory retains its initial unformalized status labels;
  the separate [coverage ledger](COVERAGE.md) records reviewed results.
- `Formalization/MDP/Basic.lean` defines finite stochastic kernels, policies,
  and Bellman maps; it proves both policy and optimality contraction bounds.
- `Formalization/MDP/FixedPoint.lean` proves Bellman fixed-point existence,
  uniqueness, geometric iteration bounds, and interval bounds. Identification
  with actual trajectory policy and optimal Q values and optimal-policy
  existence is established separately below.
- `Formalization/MDP/FiniteHorizon.lean` and `FiniteTrajectory.lean` construct
  nonstationary finite trajectories and prove that their expected cumulative
  reward equals backward evaluation. Finite-horizon optimality is addressed
  separately by `FiniteOptimal.lean` below.
- `Formalization/MDP/FiniteQTrajectory.lean` additionally constructs the
  action-conditioned trajectory law, proves both indexed finite-horizon policy
  Bellman equations, and supplies zero terminal values.
- `Formalization/MDP/FiniteOptimal.lean` constructs a greedy deterministic
  stage sequence in one common, time-varying environment, proves it dominates
  randomized Markov policies, and derives the finite optimal Bellman equations.
  The [independent review](critic-finite-optimal.md) identifies the finite
  policy representation and zero-horizon boundaries that remain to address.
- `Formalization/MDP/FiniteOccupancy.lean` constructs finite state and
  state-action occupancy laws and proves their factorization and initial-state
  identity. `OccupancyBridge.lean` proves equality with events under one full
  episode law and derives the greedy optimal-policy indicator formula. See the
  [initial review](critic-finite-occupancy.md) and the subsequent
  [bridge review](critic-occupancy-bridge.md).
- `Formalization/MDP/DiscountedFiniteTrajectory.lean` defines discounted
  rewards on actual finite trajectory laws, proves their Bellman recursion,
  and proves that finite expectations converge to the unique state Bellman
  fixed point. Its [independent review](critic-discounted-finite.md) checks
  the finite-law semantics and discount exponents. Infinite-path expectations
  and their partial-sum convergence are constructed separately below; the
  finite-prefix payoff integrals are now connected to the actual infinite law
  by `PrefixValueBridge.lean` below.
- `Formalization/MDP/PolicyValueQ.lean` proves that the state Bellman fixed
  point equals the policy average of the Q Bellman fixed point, and proves the
  corresponding reward-plus-continuation identity. Its
  [independent review](critic-policy-value-q.md) records the then-open
  infinite-trajectory interpretation, addressed in `ForcedPrefixBridge.lean`.
- `Formalization/MDP/InfiniteTrajectory.lean` constructs a normalized infinite
  controlled path law from the actual policy and transition distributions.
  It proves the first-step law and identifies arbitrary prefixes with Mathlib's
  iterated history-kernel construction. Its identification with the project's
  finite path law is established at every prefix length in
  `FinitePrefixBridge.lean` below. The
  [independent review](critic-infinite-trajectory.md) checks the law and the
  history/next-step distribution.
- `Formalization/MDP/InfinitePrefix.lean` proves the exact policy-transition
  product for every finite singleton cylinder; the separately defined finite
  path law is related below. See the
  [independent review](critic-infinite-prefix.md).
- `Formalization/MDP/FinitePrefixBridge.lean` proves that for every length,
  including zero, the actual infinite-law prefix has exactly the independently
  constructed finite path law. Transferring payoffs and their limits remains
  separate; see the [independent review](critic-finite-prefix-bridge.md).
- `Formalization/MDP/InfiniteValueBellman.lean` proves an actual-path
  first-step expectation identity for every valid discount and directly proves
  the γ = 0 Bellman specialization. Its general identification is addressed by
  `PrefixValueBridge.lean`; see the
  [independent review](critic-infinite-value-bellman.md).
- `Formalization/MDP/PrefixValueBridge.lean` identifies the actual infinite
  trajectory value with the policy state Bellman fixed point for every
  source discount and stationary randomized policy. It transports finite
  payoffs and uses the two independently established limits; see the
  [independent review](critic-prefix-value-bridge.md). The actual Q-value
  identification remains separate.
- `Formalization/MDP/ForcedActionTrajectory.lean` constructs the actual
  first-action intervention, including zero-policy-mass actions, with the
  original policy governing all subsequent steps. See the
  [independent review](critic-forced-action.md).
- `Formalization/MDP/ForcedActionReturn.lean` defines the corresponding actual
  infinite Q-return expectation and proves its integrability, geometric bounds,
  and convergence of expected partial sums. See the
  [independent review](critic-forced-return.md). Its Bellman fixed-point
  identity and V–Q averaging relation are established separately below.
- `Formalization/MDP/ForcedPrefixBridge.lean` identifies the actual forced-
  first-action infinite Q expectation with the policy Q fixed point for all
  discounts and actions, including zero policy probability. It proves the
  policy Q Bellman equation and actual V–Q averaging identity. Stationary
  optimality is addressed separately below; see the
  [independent review](critic-forced-prefix-bridge.md).
- `Formalization/MDP/OptimalTrajectoryValue.lean` constructs a deterministic
  stationary greedy policy whose actual trajectory Q attains the optimality
  Bellman fixed point and whose Q and V dominate all stationary randomized
  policies. The result does not quantify over nonstationary or history-dependent
  policies; see the [independent review](critic-optimal-trajectory-value.md).
- `Formalization/MDP/PolicyIteration.lean` proves the source γ^k trajectory-Q
  error rate for arbitrary maximizing tie choices and finite optimal-value
  attainment, including an arbitrary initial stationary randomized policy.
  A fixed tie rule also eventually stabilizes at the greedy policy. See the
  [independent review](critic-policy-iteration.md).
- `Formalization/MDP/DiscountedOccupancy.lean` constructs the source's
  discounted state and state-action occupancy laws from actual infinite path
  events and the specified initial distribution, proves normalization, the
  policy factorization and deterministic-policy indicator, and handles γ = 0.
  The explicit optimal-policy indicator is established separately below; see
  the [independent review](critic-discounted-occupancy.md).
- `Formalization/MDP/OptimalDiscountedOccupancy.lean` specializes the
  occupancy indicator to the constructed optimal greedy policy, with the same
  initial distribution and actual trajectory events. See the
  [independent review](critic-optimal-discounted-occupancy.md).
- `Formalization/MDP/InfiniteReturn.lean` defines the actual infinite discounted
  return and its expectation under that path law, and proves measurability,
  integrability, the geometric bound, and convergence of expected partial sums.
  The [independent review](critic-infinite-return.md) records the then-open
  payoff-integral bridge and Bellman identification, now established separately
  in `PrefixValueBridge.lean`.
- `Formalization/Probability/Variance.lean` proves the source's exact finite
  transition-variance perturbation bound, Lemma 2.2. See its independent
  [scoped review](critic-variance-review.md).
- [Concentration API discovery](probability-api-discovery.md) identifies a
  pinned Mathlib route for Hoeffding and the additional work needed for
  variance-sensitive Bernstein, random test families, and strict probabilities.
  Neither source concentration lemma has yet been proved.
- `Formalization/Probability/EmpiricalRow.lean` constructs actual iid finite
  transition-row samples and normalized empirical frequencies for positive
  sample count, proves the sample-mean identity, and proves unbiasedness.
  The [independent review](critic-empirical-row.md) records this scope. This is
  a prerequisite, not a proof of either concentration lemma.
- `Formalization/Probability/EmpiricalHoeffding.lean` proves the sharp
  fixed-vector two-sided Hoeffding tail for actual iid row samples, including
  a separate zero-norm case. The simultaneous source lemma for independent
  random vector families and its strict probability remain open. See the
  [independent review](critic-empirical-hoeffding.md).
- `Formalization/Probability/EmpiricalHoeffdingFamily.lean` proves the
  exact source radius simultaneously for a deterministic finite family, with
  strict success probability, and treats empty and zero-vector cases. The
  random independent-family extension remains open; see its
  [independent review](critic-empirical-hoeffding-family.md).
- `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean` proves the
  strict source-radius bound for variable-size, possibly empty random families
  independent of the actual empirical row, under an explicit family-test
  measurable structure; see the
  [independent review](critic-empirical-hoeffding-random-family.md).
- `Formalization/Probability/RandomFamilyBorel.lean` constructs a finite-family
  measurable space from injective Borel tuples and proves the source-radius
  strict bound under unordered-family/empirical-row independence. Equality
  with other hyperspace σ-algebras and a full source declaration audit remain
  separate; see the [independent review](critic-random-family-borel.md) and
  [source correspondence](source-hoeffding-correspondence.md).
- `Formalization/Probability/EmpiricalBernstein.lean` proves the actual iid
  empirical mean variance, zero-variance case and a variance-sensitive
  exponential tail with constants weaker than the source. The source Bernstein
  lemma remains open; see the [independent review](critic-empirical-bernstein.md).
- `Formalization/Probability/SharpEmpiricalBernstein.lean` derives the
  source-constant fixed-vector Bernstein tail under actual iid sampling,
  including zero range and variance. The simultaneous random-family and
  whole-matrix source bounds remain open; see the
  [independent review](critic-sharp-empirical-bernstein.md).
- `Formalization/Probability/BernsteinFamily.lean` proves the source
  Bernstein radius and strict success for a single empirical row and a
  random finite Borel family independent of that row, including empty and
  zero cases. The whole-matrix inequality remains separate; see the
  [independent review](critic-bernstein-family.md).
- `Formalization/Probability/BernsteinMatrixMarginals.lean` proves the
  source whole-matrix Bernstein bound from iid sampling within each row,
  allowing arbitrary cross-row dependence, with the correct matrix independence
  and strict success. See the [independent review](critic-bernstein-matrix-marginals.md).
- `Formalization/Probability/EmpiricalVarianceBernstein.lean` proves the
  iid empirical-variance bias correction and a source-radius bound in a
  restricted confidence regime. General self-normalized concentration remains
  open; see the [independent review](critic-empirical-variance-bernstein.md).
- `Formalization/Probability/EmpiricalVarianceConcentration.lean` proves a
  two-sided additive concentration bound for the empirical variance and a
  one-sided population-variance confidence bound on the actual iid sample law.
  The source's sharper self-normalized empirical Bernstein theorem remains
  open; see the [independent review](critic-empirical-variance-concentration.md).
- `Formalization/Probability/EmpiricalBernsteinSelfNormalized.lean` proves
  exact leave-one-out empirical-variance identities and a sharp deterministic
  sum-of-squares self-bound. The required stochastic self-bounding inequality
  and source empirical Bernstein conclusion remain open; see the
  [independent review](critic-empirical-bernstein-self-normalized.md).
- `Formalization/Probability/SelfBoundingConcentration.lean` proves an
  iid empirical-standard-deviation lower-tail bound with correct N⁻¹ᐟ² scale
  but constants weaker than the source empirical Bernstein result. The
  source's sharper self-normalized inequality and family extension remain
  open; see the [independent review](critic-self-bounding-concentration.md).
- `Formalization/Probability/EmpiricalBernsteinCombined.lean` proves a
  fixed-vector confidence bound in terms of observed empirical variance with
  explicit constants weaker than the source. Sharp constants and the random
  family statement remain open; see the [independent review](critic-empirical-bernstein-combined.md).
- `Formalization/Obstructions/SingletonAction.lean` proves a singleton-action
  policy-loss obstruction. `Obstructions/OneState.lean` proves a one-state
  Bellman fixed-point formula and optimal greedy policy. See
  [SOURCE-ISSUES.md](SOURCE-ISSUES.md) for the source review, including a
  one-state counterexample under the known-reward convention and the pending
  Lean bridge to the full statistical theorem.
- `Formalization/Obstructions/HardMDP.lean` constructs the source's two-state
  hard example and proves its correct optimal and bad-policy Bellman values,
  source-range value separation, and policy loss. Its [independent review](critic-hard-mdp.md)
  also checks a rational counterexample to the printed intermediate Q formula.
  Stationary optimal trajectory semantics are addressed separately; the full
  statistical lower bound remains open.
- `Formalization/Obstructions/OneStateTrajectory.lean` proves that one
  estimator using known rewards and discount is exact for actual stationary
  optimal trajectory Q, uniformly over one-state models and data laws.
  The formal statistical experiment is addressed separately; see the
  [independent review](critic-one-state-trajectory.md).
- `Formalization/Obstructions/OneStateExperiment.lean` constructs the actual
  one-sample-per-row generative law and proves one jointly measurable
  known-reward Q estimator has zero error uniformly across the admissible
  one-state models for each feasible source parameter choice. A literal
  source-theorem proposition and its formal negation are not yet encoded;
  see the [independent review](critic-one-state-experiment.md).
- `Formalization/Obstructions/OneStatePolicyExperiment.lean` constructs a
  measurable deterministic reward-greedy estimator whose actual trajectory
  Q-policy loss is zero across the one-state generative experiment. A literal
  source-theorem proposition and formal negation remain separate; see the
  [independent review](critic-one-state-policy-experiment.md).
- `Formalization/Generative/ModelBasedPolicyEvaluation.lean` constructs
  the genuine iid policy-row experiment and measurable empirical Bellman
  estimator, with actual empirical trajectory semantics. The literal inverse
  expression and the source sample-complexity bound are proved separately
  below. See the
  [independent review](critic-model-based-policy-evaluation.md).
- `Formalization/Generative/ModelBasedPolicyLearning.lean` constructs the iid
  state-action experiment, empirical MDP, Q estimator, and measurable
  deterministic greedy policy with empirical trajectory optimality. The
  true-model sample-complexity theorem is established separately below; see
  the [independent review](critic-model-based-policy-learning.md).
- `Formalization/Obstructions/Theorem37Negation.lean` proves the negation
  of a source-facing encoded version of Theorem 3.7(ii) using the one-state
  experiment. Its estimator interface and stationary-policy interpretation
  have unresolved source-equivalence boundaries; see the
  [independent audit](critic-theorem37-negation.md). It is not an
  author-approved correction or a proof of the printed theorem.
- `Formalization/Generative/PolicyEvaluationPerturbation.lean` proves the
  exact actual-trajectory Bellman error identity and its γ/(1−γ) sup-norm
  residual bound for true and empirical models with common known reward and
  discount, including γ = 0. It is deterministic; the source statistical
  guarantee remains separate. See the [independent review](critic-policy-evaluation-perturbation.md).
- `Formalization/Generative/PolicyEvaluationInverse.lean` proves that the
  stochastic empirical matrix yields an invertible `I−γ P̂π` and that the
  empirical Bellman estimator equals the source's literal inverse expression.
  Statistical guarantees remain separate; see the
  [independent review](critic-policy-evaluation-inverse.md).
- `Formalization/Generative/PolicyEvaluationHoeffding.lean` proves a
  strict high-probability actual-sampling evaluation bound and a sufficient
  sample size scaling as (1−γ)⁻⁴. This is weaker than the source's
  (1−γ)⁻³ result; see the [independent review](critic-policy-evaluation-hoeffding.md).
- `Formalization/Generative/PolicyLearningZeroDiscount.lean` proves zero
  true-model trajectory Q and V loss for the empirical greedy policy at γ = 0,
  for every positive sample count and every outcome. The general source theorem
  remains open; see the [independent review](critic-policy-learning-zero-discount.md).
- `Formalization/Generative/PolicyLearningAbsorbing.lean` constructs the
  fixed-parameter absorbing model and proves its deterministic data-invariance
  properties. `PolicyLearningAbsorbingPreservation.lean` proves Lemma 3.3,
  preservation of actual optimal trajectory values, and its empirical
  counterpart. `PolicyLearningAbsorbingLipschitz.lean` proves exact fixed-parameter
  value stability. Statistical independence remains separate; see the
  [absorbing review](critic-policy-learning-absorbing.md),
  [preservation review](critic-policy-learning-preservation.md), and
  [stability review](critic-policy-learning-absorbing-lipschitz.md).
- `Formalization/Generative/FiniteHorizonPolicyPerturbation.lean` proves
  exact nonstationary-policy trajectory perturbation identities.
  `FiniteHorizonContinuationBernstein.lean` proves fixed-row Bernstein
  concentration for the actual random empirical continuation using proved
  future-sample independence. A full finite-horizon sample bound remains
  open; see the [perturbation review](critic-finite-horizon-policy-perturbation.md)
  and [concentration review](critic-finite-horizon-continuation-bernstein.md).
- `Formalization/Generative/FiniteHorizonEmpiricalContinuation.lean` proves
  that the actual empirical optimal continuation depends only on strictly
  future-stage samples and is independent of the current row. The causal
  planner’s source sample theorem is now proved for positive N; see the [independent review](critic-finite-horizon-empirical-continuation.md).
- Finite-horizon residual accumulation and optimal-policy transfer prove
  deterministic value and forced-action Q error bounds for every exact
  suffix-optimal empirical policy under a shared residual envelope.
  The source sample-threshold conversion is established for the causal
  backward-greedy planner and positive N; see
  the [independent review](critic-finite-horizon-source-theorem.md).
- The source TD bounded-iterates lemma is proved pathwise for the actual
  synchronous update and actual trajectory value. Its convergence theorem remains open; see the [independent review](critic-td-iterate-bounds.md).
- The corrected indexed hard family now has finite Fano and two-point
  deterministic-estimator risk proofs, including strict lower-risk
  bounds under explicit budgets. The unrestricted printed theorem and its
  wider printed domain remains open; see the
  [independent review](critic-generative-lower-bound-policy-risk-branches-compiled.md).
- The synchronous TD sample interface constructs the actual finite
  policy-transition product law and connects it to bounded iterates;
  filtration and convergence remain open. Its extra time-zero draw is
  unused; see the [review](critic-td-synchronous-sampling.md).
- A corrected policy-risk lower bound proves the source 1/4 probability
  on the explicit restricted domain S,A≥2 and SA≥16, even for a
  common randomized estimator of deterministic policies. It does not
  establish the printed theorem for S=1 or its Q-estimation part; see
  [review](critic-generative-lower-bound-kernel-quarter.md).
- Finite-horizon variance-derived auxiliary values and their source
  growth bound are proved for fixed policies. Data-selected policy
  independence for arbitrary global ties remains open; see
  [review](critic-finite-horizon-auxiliary-growth.md).
- The finite-horizon auxiliary error recursion now yields the cited
  deterministic Lemma 9 bound under its explicit all-level Bernstein
  conditions, including source depth and constants. The corresponding
  event for the causal selected planner is proved; see
  [review](critic-finite-horizon-lemma-nine-wrapper.md).
- The corrected Q-estimation mixture has actual optimal-Q separation,
  full-array sampling reconstruction and its active-product mixture
  density and moments. A separate corrected Q-risk theorem handles arbitrary
  randomized real-Q estimators on S,A≥2; the wider printed domain remains
  open. See [review](critic-generative-lower-bound-q-final-randomized.md).
- One actual-law all-level Bernstein event holds for the true-optimal
  policy and the causal backward-greedy empirical selector, with an
  explicit confidence factor. Arbitrary globally selected ties remain open; see [review](critic-finite-horizon-all-level-bernstein.md).
- The causal finite-horizon planner has simultaneous all-stage V and Q
  bounds with explicit confidence, sample condition and radius. The
  printed sample-threshold/log conversion is proved for positive N; arbitrary
  globally chosen ties remain open; see [review](critic-finite-horizon-same-data-performance.md).
- The synchronous Q-learning update satisfies the source Q/V range and
  optimal trajectory-Q error invariant pathwise. The sampling and
  convergence results are separate; see [review](critic-q-learning-iterate-bounds.md).
- The exact TD learning-weight identities and a finite-product
  exponential envelope are proved; the corrected schedule-specific
  bounds remain separate. See [review](critic-td-learning-weights.md).
- Corrected TD step-size early and late bounds include the missing
  large-T/time premises, and the source main budget supplies the
  large-T premise for a sufficient constant. The stochastic TD
  theorem remains open; see [review](critic-td-step-size-budget.md).
- Q-learning has an actual finite product experiment and proved
  past-prefix/current-row independence. Conditional moments are established
  separately below; convergence remains open. See
  [review](critic-q-learning-causality.md).
- Q-learning increments have conditional mean zero and true-row
  conditional variance under the actual sample prefix. Their strict
  increment history is included in that prefix; its conditional
  square is the tower-transferred row variance. Coarse deterministic caps
  are available; the sharp convergence rate remains open. See
  [review](critic-q-learning-natural-history.md).
- The actual TD error obeys the exact finite chronological telescope
  with its source noise terms. Conditional moments and the TD rate
  remain separate; see [review](critic-td-error-unroll.md).
- TD noise has conditional mean zero and actual policy-row conditional
  variance under its exact sample prefix, with deterministic
  propagated-increment bounds, conditional cross-state cancellation and
  exact propagator rows. The source weighted-variance proxy, its finite sum,
  and the fixed-terminal natural history are established; a deterministic
  terminal cap, Freedman event and final rate remain open. See
  [variance review](critic-td-weighted-variance.md),
  [sum review](critic-td-variance-sum.md), and
  [history review](critic-td-terminal-history.md).
- Q-learning has coarse caps for actual iterate-dependent increments and
  an actual-law Freedman event for the optimal-value fluctuation, simultaneously
  over state-action rows and the late terminal times. The source-indexed
  weight schedule, predictable variance, magnitude bounds and confidence
  union are proved. A separate robust-comparator absorption event is proved
  below; the final convergence rate remains open. See [fixed-row review](critic-q-learning-optimal-freedman.md)
  and [union review](critic-q-learning-optimal-freedman-union.md).
- The source TD squared-iterate energy inequality is proved for each
  coordinate and positive update under the actual sample law, with the
  source initial-value and rate conditions. The later sharp variance
  concentration and TD accuracy theorem are recorded separately; see
  [review](critic-td-square.md).
- The chronological TD propagator composition, weighted square-energy
  telescope and its deterministic endpoint cap are established. A general
  fixed-terminal centered-square martingale has actual-history centering,
  an explicit source late-window wrapper, single-state conditional variance
  control, cross-state square-covariance cancellation, and a per-update
  propagated conditional variance bound. Its late-window sum is bounded by
  the actual random source proxy, which is controlled by the energy telescope
  and centered-square martingale under explicit positive-time rate and
  late-window bounds. A zero-tail extension preserves every used-through-T
  iterate, weight and propagator while supplying global positive-rate bounds;
  the actual random proxy and eligible-terminal event are unchanged by this
  extension. A deterministic
  increment bound and coarse variance cap are also derived
  for the late-window centered-square martingale. The fixed-terminal late
  proxy and original predictable variance simultaneously satisfy both source
  infinity-norm bounds with probability at least 1−δ/(2T), under the source
  schedule and an explicit universal sample-budget constant. The final TD
  accuracy theorem remains separate. See
  [full variance-lemma review](critic-td-variance-lemma.md),
  [proxy concentration review](critic-td-proxy-concentration.md),
  [rate-extension review](critic-td-source-rate-finite-extension.md),
  [event-transport review](critic-td-source-rate-proxy-transport.md),
  [scalar review](critic-td-sharp-self-bound-scalar-independent.md),
  [caps review](critic-td-sharp-freedman-caps-independent.md),
  [energy review](critic-td-sharp-energy.md),
  [martingale review](critic-td-sharp-martingale-source.md),
  [fresh-variance review](critic-td-square-fresh-variance-bridge.md),
  [covariance review](critic-td-square-covariance.md),
  [propagated-variance review](critic-td-square-propagated-variance-independent.md),
  [variance-sum review](critic-td-sharp-variance-sum-independent.md), and
  [energy-proxy review](critic-td-sharp-energy-proxy-independent.md).
- TD weights satisfy the source mass identity and first- and squared-mass
  bounds. A source-schedule envelope and an actual-law scalar fixed-terminal
  Freedman event are established under explicit late-terminal and large-T
  assumptions. The event uses conservative caps; a sharp variance analysis,
  simultaneous events and the source accuracy theorem remain open. See
  [weight review](critic-td-weight-mass.md) and
  [terminal review](critic-td-terminal-caps-freedman.md).
- The support-aware χ² uncertainty set defines both robust Q-learning
  operators. Both are contractions and have unique fixed points for a
  nonnegative radius. Compactness gives actual optimizing rows and their
  shifted fixed-point value bounds. The source two-sided χ² comparison
  of robust expectations is proved, as is the support-aware finite-row
  KL-to-χ² bound. Both robust fixed-point residual signs have bounds at
  the exact source radius and reward shift. Actual fixed-comparator
  fluctuations have proved conditional moments, variance budgets, and a
  source-radius absorption event simultaneously over both signs, rows and
  late terminal times with confidence at least 1−δ. A
  same-sample comparator sandwich holds simultaneously on the absorption
  event with probability at least 1−δ under the source schedule, T≥2,
  0<δ<1 and bounded initialization. See
  [operator review](critic-q-learning-robust-contraction.md),
  [optimizer review](critic-q-learning-robust-compact-attain-range.md),
  [comparison review](critic-q-learning-chi-comparison.md),
  [KL review](critic-q-learning-chi-kl.md),
  [residual review](critic-q-learning-chi-residual.md),
  [source-parameter review](critic-q-learning-chi-source-parameters.md),
  [fixed-value review](critic-q-learning-chi-fixed-value-chain.md),
  [probability review](critic-q-learning-chi-probability.md), and
  [sandwich review](critic-q-learning-comparator-chain-independent.md).
- The source chi-square comparison lemma, including the actual optimal-Q
  infinity-norm stability estimate, is proved. The selected-model comparator
  reduction consumes that estimate and discharges the former assumption in
  the universal-constant Q-learning accuracy theorem. The resulting source
  theorem uses the actual synchronous product sampling law and retains the
  source schedule, initialization, confidence and sample-budget conditions.
  See the [comparison and accuracy review](critic-q-learning-comparison-and-main.md),
  [conditional assembly review](critic-q-learning-conditional-final-independent.md),
  and [selected-model review](critic-q-learning-selected-model-closeness-source.md).
- The finite-law pairwise variance identity and square-variance bound include
  zero-mass atoms, singleton carriers and H=0. Actual TD conditional
  variance and cross-state square-covariance bridges are proved separately;
  see [review](critic-td-variance-pairwise-source.md).
- Pinsker is proved for supported finite and countable mass functions with
  the source coefficient 2 and half-L1 total variation, including zero atoms
  and endpoints. The countable result applies to the actual geometric
  stopped-prefix masses using a derived absolute-KL summability bound. The
  actual-measure/event-supremum identification remains a separate result; see
  [finite review](critic-q-learning-finite-pinsker-source-second.md)
  and [countable review](critic-q-learning-countable-pinsker-independent.md).
- A finite one-step Markov joint-law KL chain rule and an actual finite
  forced-prefix KL induction are established with explicit support conditions,
  including zero transitions at k=0. The geometric stopped-law bound is used
  in the stability proof; see [one-step review](critic-q-learning-trajectory-kl.md)
  and [prefix review](critic-q-learning-forced-prefix-kl-chain.md).
- The TV branch of robust-RL Lemma 7.1 now has its full source-facing statement
  and proof: the primal infimum over actual finite rows equals an attained
  maximum of the clipped source objective over the full `[Vmin,Vmax]` interval,
  with the maximizing value dominating every other interval point. The source
  assumptions `V ≥ 0` and `σ > 0` and half-L1 TV normalization are retained;
  zero nominal atoms, ties, singleton rows, and radii above one are covered.
  That TV-only milestone is superseded by the full two-branch proof above. The
  affected 438-module rebuild passed (23 rebuilt, 415 reused from the prior
  verified 418-module clean baseline) and audited 4,959 declarations; this was
  not a fresh 438-module clean build. See the [verification record](tv-strong-duality-verification.md)
  and [independent source review](critic-robust-tv-strong-duality.md).
- The finite KL data-processing modules prove log-sum with empty decoder
  cells, finite-law KL contraction and its actual indexed-family specialization.
  The complete printed minimax theorem remains open; see the independent
  [cell review](critic-generative-lower-bound-cell-logsum.md),
  [finite-law review](critic-generative-lower-bound-finite-kl-data-processing.md),
  and [family review](critic-generative-lower-bound-family-data-processing.md).
- The corrected multi-hypothesis lower-bound infrastructure constructs the
  indexed MDP family, correct forced-action Q values and policy-loss decoder,
  and proves the actual indexed observation law and KL transport. Its
  stronger hypotheses S,A≥2 are explicit. The Fano route remains a separate
  obligation; corrected policy and Q risk results have since been proved by
  their respective completed routes. See the [family review](critic-generative-lower-bound-family-mdp.md),
  [gap review](critic-generative-lower-bound-policy-gap.md), and
  [KL review](critic-generative-lower-bound-family-kl.md).
- `Formalization/Generative/FiniteHorizonGenerativeSampling.lean` builds
  the actual finite-stage generative experiment, empirical stages and
  future-block independence. The finite-horizon sample theorem remains open;
  see the [independent review](critic-finite-horizon-generative-sampling.md).
- `Formalization/Generative/GenerativeLowerBoundKLAffinity.lean` proves
  finite full-support KL-to-testing and Bernoulli-product estimation bounds.
  `GenerativeLowerBoundTwoStateMDP.lean` and `GenerativeLowerBoundObservationLaw.lean`
  connect these to actual two-state MDPs and their complete sampling laws,
  proving a strict Q-estimation lower bound for one common deterministic
  estimator. Arbitrary extra randomization and the general fixed-size lower
  bound remain separate. See the [KL review](critic-generative-lower-bound-kl-affinity.md),
  [MDP review](critic-generative-lower-bound-two-state-mdp.md), and
  [observation-law review](critic-generative-lower-bound-observation-law.md).
- `Formalization/Generative/GenerativeLowerBoundTestingReduction.lean` and
  `GenerativeLowerBoundOverlapTesting.lean` prove finite-law testing and
  strict estimation-error transfer helpers. The quantitative KL-to-testing
  link and actual two-state observation law are established separately; see the
  [testing review](critic-generative-lower-bound-testing-reduction.md) and
  [overlap review](critic-generative-lower-bound-overlap-testing.md).
- `Formalization/Probability/BoundedIncrementFixedTimeTail.lean` proves a
  preliminary one-sided variance-restricted martingale tail with weaker
  constants. `BernsteinExponentialEnvelope.lean` and
  `ConditionalBernsteinSharpMGF.lean` establish the sharp scalar and
  conditional MGF coefficients; the sharp process and Freedman tail are
  proved separately below. See the [tail review](critic-bounded-increment-fixed-time-tail.md)
  and [sharp MGF review](critic-sharp-conditional-bernstein-mgf.md).
- `Formalization/Generative/GenerativeLowerBoundBernoulliMeasure.lean`
  identifies finite Bernoulli relative entropy, and `GenerativeLowerBoundProductKL.lean`
  proves its finite-product tensorization. The two-state hard-MDP experiment
  and testing lower bound are established separately; see the [independent review](critic-generative-lower-bound-bernoulli-product.md).
- `Formalization/Probability/ConditionalBernsteinMGF.lean` and
  `BoundedIncrementExponentialProcess.lean` prove a restricted-domain
  conditional MGF bound and its exponential supermartingale. The sharp
  Freedman tail is proved separately below; see the reviews of the [MGF](critic-conditional-bernstein-mgf.md)
  and [process](critic-bounded-increment-exponential-process.md).
- `Formalization/Generative/GenerativeLowerBoundParameters.lean` proves
  scalar hard-instance parameter estimates, and `GenerativeLowerBoundBernoulli.lean`
  proves the corresponding scalar Bernoulli divergence bound. The actual
  product experiment and two-state testing bound are proved separately; see the
  [parameter review](critic-generative-lower-bound-parameters.md) and
  [Bernoulli review](critic-generative-lower-bound-bernoulli.md).
- `Formalization/Probability/FreedmanNaturalHistory.lean` proves the exact
  source Freedman inequality, Lemma 2.9, for conditioning on the sigma-algebra
  generated by prior increments, with the printed constants and endpoints.
  See the [natural-history audit](critic-freedman-natural-history.md) and
  [assembly audit](critic-freedman-exact-assembly.md).
- `Formalization/Probability/FreedmanVariancePeeling.lean` proves the
  deterministic dyadic cover and radius comparison used in the source
  Freedman argument; the stochastic tail is proved separately below.
  See the [independent review](critic-freedman-variance-peeling.md).
- `Formalization/Generative/PolicyLearningMainSample.lean` proves the
  source model-based policy-learning Theorem 3.2, with universal constant
  10240, the printed N-dependent logarithm, actual product sampling, and
  simultaneous V and forced-action Q guarantees for all empirical-optimal
  deterministic ties. Positive N is explicit as the source sampling/log
  domain. See the [theorem audit](critic-policy-learning-main-sample.md) and
  [independent source review](critic-policy-learning-main-sample-integrated-second.md).
- `Formalization/Generative/PolicyLearningSourcePointwise.lean` proves
  the source policy-learning evaluation Lemma 3.5 with shared universal
  constants, actual product sampling, and all empirical-optimal deterministic
  ties. Positive N is explicit as the sampling and logarithm domain; see the
  [source audit](critic-policy-learning-source-pointwise.md) and
  [integrated independent audit](critic-policy-learning-source-pointwise-second.md).
- `Formalization/Generative/PolicyLearningFittedPolicyEvaluation.lean`
  proves a high-probability fitted-policy evaluation bound, and
  `PolicyLearningAnyOptimalPolicy.lean` extends its event and deterministic
  performance comparison to all empirical-optimal deterministic ties. The
  fixed true-optimal policy event and source theorem are proved separately; see
  the [fitted-policy review](critic-policy-learning-fitted-policy-evaluation.md)
  and [tie review](critic-policy-learning-any-optimal-policy.md).
- `Formalization/Generative/PolicyLearningVarianceResolventBridge.lean`
  proves the source-constant fitted-policy evaluation bound from an explicit
  row-residual premise, without requiring nonnegative empirical forcing.
  `PolicyLearningPerformanceTransfer.lean` transfers two evaluation budgets
  to V and forced-action Q performance. The probability assembly remains
  separate; see the [bridge review](critic-policy-learning-variance-resolvent-bridge.md)
  and [performance review](critic-policy-learning-performance-transfer.md).
- `Formalization/Generative/PolicyLearningEmpiricalOptimalResidual.lean`
  proves the all-row residual bound for the data-selected empirical optimum
  on the same simultaneous sampling event. `PolicyLearningEmpiricalVarianceSelfBound.lean`
  proves the fitted-value variance expansion, and `PolicyLearningTrueResolventJensen.lean`
  establishes the arbitrary-input true-resolvent bridge. Combining these
  into the policy-learning theorem remains open; see the independent reviews
  of the [residual](critic-policy-learning-empirical-optimal-residual.md),
  [self-bound](critic-policy-learning-empirical-variance-self-bound.md), and
  [resolvent](critic-policy-learning-true-resolvent-jensen.md).
- `Formalization/Generative/PolicyLearningVarianceTransfer.lean` proves
  standard-deviation stability and a conditional grid-to-value transfer.
  `PolicyLearningAllRowBernstein.lean` proves the source-constant simultaneous
  all-row, all-grid event under actual sampling. Data-selected transfer and
  the policy-learning theorem remain separate; see the independent reviews
  of [variance transfer](critic-policy-learning-variance-transfer.md) and
  the [all-row event](critic-policy-learning-all-row-bernstein.md).
- `Formalization/Generative/PolicyLearningAbsorbingGrid.lean` proves the
  source finite grid and Lemma 3.4, the actual empirical optimal-value cover.
  `PolicyLearningLeaveOneOutBernstein.lean` proves a fixed-family, one-row
  concentration event; the all-row union and data-selected transfer are
  separate. See the independent reviews of the [grid](critic-policy-learning-absorbing-grid.md)
  and [Bernstein event](critic-policy-learning-leave-one-out-bernstein.md).
- `Formalization/Generative/PolicyLearningLeaveOneOutIndependence.lean`
  proves that the fixed-parameter auxiliary value family is independent of
  the omitted empirical row under the actual sampling law. It does not
  assert independence for a parameter selected from the data; see the
  [independent review](critic-policy-learning-leave-one-out-independence.md).
- `Formalization/Generative/PolicyLearningHoeffding.lean` proves a
  conservative actual-sampling policy-learning value guarantee by a finite
  union over deterministic policies, accounting for the fitted policy’s data
  dependence. Its rate is weaker than the source and does not prove its Q
  guarantee; see the [independent review](critic-policy-learning-hoeffding.md).
- `Formalization/Generative/PolicyEvaluationVariance.lean` proves a
  source-derived policy variance identity, finite and infinite discounted
  variance-budget bounds and the budget's unique Bellman equation. The
  empirical-resolvent and sharper statistical links are proved separately; see the
  [independent review](critic-policy-evaluation-variance.md).
- `Formalization/Generative/PolicyEvaluationUniversalConstant.lean` proves
  the source policy-evaluation sample theorem, Theorem 3.1, with a universal
  constant 720 chosen before all finite model and accuracy parameters. It
  uses the actual policy-row sampling law and trajectory values. Independent
  source and integrated-export reviews are recorded in the
  [theorem audit](critic-policy-evaluation-source-theorem.md),
  [second source audit](critic-policy-evaluation-source-independent.md), and
  [universal-constant audit](critic-policy-evaluation-universal-constant.md).
- `Formalization/Generative/PolicyEvaluationTerminalError.lean` proves
  the terminal auxiliary error estimate. `PolicyEvaluationHighSample.lean`
  combines it with the recursion on one actual-sampling event, while
  `PolicyEvaluationSampleAssembly.lean` proves sample-threshold arithmetic
  and one-state exactness. The source-shaped final theorem is assembled
  separately; see the independent reviews of the [terminal bound](critic-policy-evaluation-terminal-error.md),
  [high-sample bound](critic-policy-evaluation-high-sample.md), and
  [sample assembly](critic-policy-evaluation-sample-assembly.md).
- `Formalization/Generative/PolicyEvaluationFinalArithmetic.lean` proves
  the printed high-sample radius from explicit recursion, growth, and terminal
  estimates; the assumptions and statistical assembly are discharged separately. See the
  [independent review](critic-policy-evaluation-final-arithmetic.md).
- `Formalization/Generative/PolicyEvaluationBernsteinRecursion.lean` combines
  the actual-sampling simultaneous Bernstein event with the conditional
  auxiliary residual recursion. The terminal estimate and source sample bound
  are assembled separately; see the [independent review](critic-policy-evaluation-bernstein-recursion.md).
- `Formalization/Generative/PolicyEvaluationAuxiliaryGrowth.lean` derives
  the source-shaped auxiliary-value growth bound from the general-forcing
  result, with a separate zero-discount identity. Its combination with the
  concentration recursion is proved separately; see the
  [independent review](critic-policy-evaluation-auxiliary-growth.md).
- `Formalization/Generative/PolicyEvaluationGeneralForcing.lean` extends
  the true-policy variance resolvent bound to any nonnegative forcing.
  `PolicyEvaluationResidualRecursion.lean` proves the conditional residual
  recursion using actual empirical resolvent order. The concentration event,
  sharp growth and final sample bound are assembled separately; see the
  independent reviews of [general forcing](critic-policy-evaluation-general-forcing.md)
  and the [recursion](critic-policy-evaluation-residual-recursion.md).
- `Formalization/Generative/EmpiricalResolventOrder.lean` proves positivity,
  order preservation, the row-sum identity and absolute-value domination for
  the actual empirical policy resolvent; see the
  [independent review](critic-empirical-resolvent-order.md).
- `Formalization/Generative/PolicyEvaluationAuxiliary.lean` constructs the
  true and empirical recursive variance-value vectors, their defining matrix
  equations and a conservative growth bound.
  `PolicyEvaluationAuxiliaryBernstein.lean` proves an actual-sampling
  simultaneous Bernstein event over finitely many true auxiliary levels. The
  sharper recursion and statistical guarantee are proved separately; see the
  independent reviews of the [vectors](critic-policy-evaluation-auxiliary.md)
  and [event](critic-policy-evaluation-auxiliary-bernstein.md).
- `Formalization/Generative/PolicyEvaluationEmpiricalResolvent.lean` proves
  an empirical-versus-true policy resolvent identity and an actual-sampling
  Bernstein bound for the first auxiliary variance vector. The higher-order
  variance analysis and sharp rate are established separately; see the
  [independent review](critic-policy-evaluation-empirical-resolvent.md).
- `Formalization/Generative/PolicyEvaluationRecursiveUnroll.lean` proves
  a conditional finite unrolling of the source’s auxiliary recursion and a
  deterministic small-sample bound that repairs an omitted case in the
  source derivation. The high-sample concentration branch and full theorem
  are proved separately; see the [independent review](critic-policy-evaluation-recursive-unroll.md).
- `Formalization/Generative/PolicyEvaluationVarianceResolvent.lean` proves
  the true-policy matrix resolvent identities and a square-root variance
  budget bound, including a scaled zero-discount case. The empirical
  comparison and sharp statistical guarantee are proved separately; see the
  [independent review](critic-policy-evaluation-variance-resolvent.md).
- The current pinned Lean integration compiled 386 project modules; its
  transitive axiom audit checked 4,633 project declarations, allowing only
  `propext`, `Classical.choice`, and `Quot.sound`. A separate clean-copy check
  passed on the same source hashes. These checks do not replace
  source review. Current builder work and independent critic findings are
  recorded separately in `builder-*.md` and `critic-*.md`.
- The [trajectory critic review](critic-trajectory-review.md) checked path
  weights, reward order, terminal marginalization, and two concrete Lean
  examples. Its reviewer authored the imported basic MDP dependencies, whose
  separate review remains necessary. The review also confirms that the
  singleton-action obstruction depends on the source interpretation.
- A separate [fixed-point critic review](critic-fixedpoint-review.md) checked
  the source-facing model fields, finite supremum norms, Bellman contractions,
  fixed-point selection, and the γ = 0 boundary. It passes those scoped
  infrastructure claims while leaving source trajectory semantics and policy
  iteration open.
- The [finite-Q critic review](critic-finite-q-review.md) checks the indexed
  policy Bellman equations against the actual action-conditioned trajectory law.
  Whole-chapter and infinite-horizon completion remain open.

## Teams and ownership

| Role | Owned work | Current objective |
|---|---|---|
| Lead builder/integrator | project configuration, checking, analysis infrastructure | reproducible proof environment and integration |
| Source builder | `scripts/inventory.py`, `docs/source-inventory.*` | complete source traversal and explicit coverage checklist |
| MDP builder | `Formalization/MDP/Basic.lean`, `FiniteHorizon.lean` | faithful finite tabular model and Bellman foundations |
| Independent critic | `docs/critic-initial-review.md` | reconstruct claims from source and challenge semantics and coverage |

## Required coverage

1. Introduction: mathematical conventions and substantive claims.
2. Preliminaries: MDP semantics, policies, value/Q functions, occupancy,
   Bellman and planning theory, concentration and testing inequalities.
3. Generative-model model-based algorithms, upper and lower bounds, and appendices.
4. Generative-model model-free algorithms, TD, Q-learning, and appendices.
5. Online RL, bandits, UCB-VI, MVP, model-free methods, lower bounds, and appendices.
6. Offline RL, pessimism, model-based/model-free methods, lower bounds, and appendices.
7. Robust, competitive multi-agent, federated, inference, and human-feedback extensions.
8. Concluding mathematical claims and all externally cited substantive inputs.

Every chapter remains open. Algorithm and trajectory semantics must be
connected to probabilistic guarantees; abstract helper bounds alone do not
certify an RL theorem. Externally cited mathematics is an obligation to prove
or instantiate from an audited dependency, not a new project axiom.
