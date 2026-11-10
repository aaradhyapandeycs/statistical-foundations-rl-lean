# Corrected MVP T6 variance verification

Source: arXiv:2610.41903v1, `chapters/onlineRL.tex:1822–1833`,
`lem:bound-T6-ucb-mvp` (Lemma 5.15). Source SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The actual export `StatisticalRL.OnlineRL.mvpActualT6_source_confidence`
proves T6 ≤ 4H T2 + 4H W4 + KH²I with probability at least 1−4SAHKδ′.
It uses the direct sequential episode/reset law, the actual retained-history
MVP table and its continuation values on that same realized path. H,K>0,
0<δ≤1, c₁≥4 and c₂≥c₁² remain explicit. K=1 is proved directly; K≥2 uses
an actual predictable process, conditional variance domination, fixed-time
Freedman/peeling, greedy episode telescope and scalar closure. No stochastic
or decomposition certificate is assumed by the final export.

The complete self-contained Prop is
`StatisticalRL.Statements.Ch5.Lemma5_15_corrected`, proved by
`StatisticalRL.Statements.Ch5.Lemma5_15_corrected_holds` using the export.
Its direct imports contain definitions only. Five statement-facing
variance/charge/history definitions were extracted with unchanged bodies;
successor definitions with a theorem-dependent history index remain in a
proof-side module. All 30 canonical provider modules retain raw bodies,
with mapped imports and uniquely named local instances as recorded by the
independent transformation review.

Corrections remain explicit. C8 supplies T2's zero-count analysis charge H;
positive stored counts use the printed bonus. C13 selects power-of-two
triggers. C16 uses δ′=δ/(100S²A²H²K²), while the source prints the numerator
100 allocation. One fixed maximizing greedy tie rule is used. This result
is a corrected variant, not a proof of the literal uncorrected formulation.

- Canonical qualification: 30 fresh targets, 45 actual export axiom probes,
  receipt `26665c0d930e72504bbcaeacca00b17aea7c0ddc55ff938dda71f2dcaa1cea14`.
- Complete Chapter 5 qualification: two fresh targets and 15 actual applying
  proof exports, receipt
  `b98aff7ad1c612720fe38d14888d7b823a888dda8ce46640ed5165fc1cab6cd4`.
- Affected integration: **34 rebuilt + 760 verified reused = 794
  modules**, whole-project axiom audit **7,417 declarations**. Only
  propext, Classical.choice and Quot.sound are permitted, including subsets
  and the empty axiom set.
- Run: `20261104T211708111013Z`.
- Manifest SHA-256: `1502da30b6298f37dabf028f04d7c43a6e7e0f5f5259f4d3d97254ce69b3f4c1`.
- Driver SHA-256: `a5a3c9b55547b29cd66ff470f35cc795b15c955756ddeee6919b5dd936d4948a`.

The guarded local command rebuilt the affected closure with the repository
compiler wrapper and ran Audit.lean. It is **not** a new clean
`python3 scripts/check.py` over all 794 files. All 16 retained baseline
ancestry edges and source/OLean reuse hashes were checked:
794→764→740→723final→723preformat→684→671→668→666→659→566→520→513→477→453→447→438→clean418.
Compiler binary/package paths and dependency metadata were checked before
and after. Historical clean418 did not bind its historical OLean/package
bytes; later reuse receipts bind inherited artifacts. Focused failures and
stale-count preflight failure remain preserved and were not reused as proof
evidence. No dependency pin or package artifact was changed.

Public full checks remain `lake build` and `lake env lean Audit.lean`;
local full checking remains `python3 scripts/check.py`. The preceding
740-module and 764-module commits passed their independent GitHub full CI
runs 41896730085 and 41903345055. This new commit's CI outcome is separate.

Size: 82,034 Lean lines including comments/blanks in 794 files. The named
ledger contains 20 original entries with existing disclosures and 10
corrected variants. Actual learner-family decoupling, Lemma 5.14, full MVP
regret, every chapter and the monograph remain incomplete.
