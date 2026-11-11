# Corrected MVP uniform concentration verification

Pinned source: arXiv:2610.41903v1, `chapters/onlineRL.tex:1696–1712`,
Assumption X at `:1670–1685`, source SHA-256
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The actual export is
`StatisticalRL.FiniteHorizonGenerative.mvp_corrected_sourceUniform_full`.
Its complete indexed statement is
`StatisticalRL.Statements.Ch5.Lemma5_13_confidence_corrected`, proved by
`StatisticalRL.Statements.Ch5.Lemma5_13_confidence_corrected_holds`.

This is the reciprocal-allocation correction δ′=δ/(100S²A²H²K²), not the
printed numerator 100 allocation refuted by C16. The finite continuation
families include h+1 at the terminal endpoint and have no generic zero-only
terminal restriction. The theorem proves both displayed inequalities,
coefficient 40000, all source noninitial dyadic levels, every profile and
every family-member vector sequence, under the actual expanded product law.
Its full strictly-future data dependence and monotone ceiling profile cover
are stronger than the printed empirical-summary/profile classes (C15).
K=1 is handled by the empty level type. Covering, logarithmic absorption,
variance bounds and concentration are proved rather than extra premises.

- Qualified compilation: 17 new providers plus both Chapter 5 index files,
  all 19 targets and the ordered 31-export axiom probe passed. Exact receipt
  SHA-256: `3146a5bca757a8d5606c0ca46d6004f23e130a1634f1c299838c62d22eb6262a`.
- Qualification map SHA-256:
  `6932267ef065f5e8a93931ede60f619d5a209cf7cc053ae4e47e2faba2441cb5`.
- Affected integration: **21 rebuilt+719 verified reused=740
  project modules**, **6,951 declarations** allowing only propext,
  Classical.choice and Quot.sound.
- Run: `20261104T191201004806Z`.
- Manifest SHA-256: `e74d4454e8b4417fb01f8facd3981ddd72673dfdf68523f362a546b4faffded3`.
- Driver SHA-256: `bbc894f2e2f8dd669eaab62fc22583d08cdebbe52b9079490425802fae2c7754`.

The guarded affected driver used the pinned compiler/wrapper and repository
checker/parser, rebuilding every changed/reverse-imported module and Audit.
This was not a new clean `python3 scripts/check.py` run over all 740 files.
Reuse ancestry: 740→723final→723preformat→684→671→668→666→659→566→520→513→477→453→447→438→clean418.
All current source/OLean hashes, fourteen retained baseline ancestry edges,
compiler/package paths and dependency metadata were checked before/after.
Historical clean418 did not record OLean/package byte hashes; later reuse
receipts bind those inherited artifacts. Public full checks remain
`lake build` and `lake env lean Audit.lean`; local full checking uses
`python3 scripts/check.py`. CI is reported separately.

The original wrapper attempt timed out at its broad dependent simplification.
A private diagnostic isolated the proof body as the cost; a type-only
admission was used solely as a performance control, never as proof evidence
or a dependency. The actual proof replaces the broad simplification by
pointwise event inclusion and a proved scalar radius identity. The default
heartbeat bound and source statement were preserved. Failed earlier runs
were retained; only the successful actual run supplies qualification evidence.

Project size: 77,558 Lean lines including comments/blanks in 740 files.
Ledger: 20 original entries with existing disclosures and nine corrected
variants. Actual learner-family membership, online probability transport,
MVP regret, all complete chapters and the whole monograph remain open.
