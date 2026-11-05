# Corrected MVP decoupling and main-regret verification

Sources: Lemma 5.14 `lemma:decouple`, `chapters/onlineRL.tex:1722–1744`, and
the main `thm-mvp-regret`, `:1339–1352`. No unverified ordinal is assigned to
the latter. Full definition-only index Props and applying wrappers are
`Lemma5_14_corrected` / `Lemma5_14_corrected_holds` and
`MVP_regret_corrected` / `MVP_regret_corrected_holds` in Ch5/Ch5Proofs.

Lemma 5.14 proves T1≤W4, the printed W4 radius, and the signed W3 radius on
one event of strict probability >1−δ′ under the actual sequential law.
The retained empirical rows, frozen pre-episode values, iid reset law and
conditional transition law are the learner's actual objects. The source
K≥SAH log₂K condition is retained, with all positive horizons/episode counts,
δ∈(0,1], c₁≥4 and c₂≥c₁². K=1 is proved directly with I=0 and H actual
transitions. Final exports assume no family-membership, law-transfer,
concentration, rank-bound or confidence certificate.

The main theorem proves a universal C=100 before all finite environment
parameters, with universal c₁=4,c₂=16. For all H,K>0 and 0<δ<1 it gives
R≤100 max(1,I) min(√(SAH³K),HK) with probability at least 1−δ, where
δ′=δ/(100S²A²H²K²) and I=40000(log₂K)³log(3SAH)log(1/δ′).
R uses the actual true value of the same deployed frozen episode policy
and the true-environment greedy optimal comparator. Small regimes and K=1
use the deterministic cap; the large branch derives eligibility and the
actual decoupling probability internally. No hdecProb premise remains.

Corrections are finite zero-count completion/analysis charge (C8), K=1
handling (C12), power-of-two triggers (C13), ceiling profile cover (C15),
reciprocal confidence allocation (C16), and terminal-zero auxiliary family
(C17), together with one fixed maximizing tie. These are corrected results,
not author approval of the printed formulas. The printed generic C16
counterexample and C17 argument gap remain recorded separately.

Focused qualification covered the analytic/K=1 cohort (22 providers,
67 exports), family/radius/path cohort (25 providers, 100 exports), actual
image-law and tail providers, the conditional main cohort (20 providers,
33 exports), the final unconditional main source, and both complete Ch5
files with 20 applying-proof probes. All successful actual-export probes
used only the permitted standard axioms. Failed private attempts remain
preserved and do not certify later source bytes. The fresh check below
builds the exact final assembly rather than relying on old private OLeans.

The actual command `python3 scripts/check.py` completed successfully in a
fresh private project tree containing all 913 project modules. Every project
module was rebuilt; zero project OLeans were reused. The whole-library axiom
audit checked 8,162 declarations and permits only `propext`,
`Classical.choice`, and `Quot.sound`. Source, OLean and log hashes for every
module are recorded in the guarded manifest. Guarded manifest SHA-256:
`750510fd73526d1592be0e61dd64f468fc1b286f50012c44037a3a15ae05de81`. Original checker manifest SHA-256:
`d116a5ed691c07a66f8a589d4452f37f412174a82223abd55e985644c55373cf`. Check log SHA-256:
`47235ef53612bb2f89d69f48b8edfdfba5ec83cb3dd5899b4dfdf6b372c1f2e0`.

The compiler binary SHA-256 is
`2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`.
Lean and Mathlib pins are unchanged. Existing pinned dependency caches were
used without a rebuild. Their paths and path/size/mtime metadata were equal
before and after; this is not a package-byte seal or a clean dependency build.
The run bound 447 prior evidence files and the exact 913-source assembly
before and after. No historical project-artifact reuse ancestry is needed
for this fresh project check.

[Independent review](critic-online-MVP-main-decoupling.md). Whole-chapter and monograph closure remain open.
