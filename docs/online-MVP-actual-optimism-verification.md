# Actual-law corrected MVP optimism verification

Source: arXiv:2610.41903v1, `chapters/onlineRL.tex:1480–1487`, displayed
`eq:optimism-Q-V-geq-mvp`; algorithm at `:1256–1310`. Source SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The complete self-contained index is
`StatisticalRL.Statements.MVP_optimism_corrected`, proved by
`StatisticalRL.Statements.MVP_optimism_corrected_holds` using
`StatisticalRL.OnlineRL.mvp_sourceOptimismCorrected_holds`.

The final theorem proves Q*/V* domination simultaneously for every episode,
stage, state and action under the actual sequential episode/reset law. It
retains H,K>0, 0<δ<1, c₁≥4, c₂≥c₁² and probability at least 1−2SAHKδ′.
The stronger strict probability estimate is consumed by the final proof.
The actual batch event, per-row count bound, retained empirical-row identity,
completed-history table identity, reset marginal and sequential law transfer
are proved dependencies, not assumptions added to the source statement.

Corrections are explicit: C8 gives Q=H and the uniform row at zero count;
C13 chooses power-of-two triggers; C16 uses δ′=δ/(100S²A²H²K²), replacing
the printed numerator 100 allocation; greedy ties use one fixed maximizing
rule. Between triggers the committed tables and recursion remain unchanged,
so the functional recomputation equals the source cache behavior. There is
no separate formal imperative cache interpreter claimed here. The row-stack
experiment is not treated as iid at a random visit count: fresh-coordinate
and transcript-law identities supply the bridge to online interaction.

Nine model definitions were extracted into MVPModelDefinitions without
changing their commands or mathematical meanings. Proof files import that
definition module; the index directly imports only definition modules.
All raw proof sources remain retained privately; canonical theorem bodies
and source declarations are preserved.

- Model qualification: seven fresh targets and all 50 public theorem exports,
  receipt `e1e40a0892828b6b252ee8c5a03bc2289d968bc5b3b1d0911266f7a75c97495b`.
- Optimism qualification: seventeen fresh targets and all 26 public theorem
  exports, receipt `262b8892eaeaa3d96e342dd89e182b3e5ed5fc22757e022a8fcdcaa48062dfe2`.
- Complete Chapter 5 qualification: both targets and all 14 applying proofs,
  receipt `ae3debca5fa003bae36004375b32875388173f0d54d596b7951cc1287f7e5865`.
- Affected integration: **28 rebuilt+736 verified reused=764
  modules**, **7,269 project declarations**, permitting only propext,
  Classical.choice and Quot.sound (some exports need a subset or none).
- Run: `20261104T195122243707Z`.
- Manifest SHA-256: `aadad74746631e7ce7bb4b1067aca0a2a137522f3aeeb96c91ed3dee8545973c`.
- Driver SHA-256: `25cbb23ae94579453e661dfdb1252dafbbca242d25655bebe4817bba5770da22`.

The first model qualification reached successful compiles/probe but its
parser rejected Lean's valid no-axioms message; the exact empty-set case
was added and a fresh qualification passed. The first full integration
found a generated declaration-name collision from anonymous local measurable
instances. The four new instances received distinct explicit local names,
with unchanged types/bodies; fresh optimism and index qualifications and
this fresh integration passed. Failed runs were retained and never counted
as verified baselines. No theorem statement or proof was changed by that fix.

This local validation is a guarded affected rebuild with the pinned compiler
and repository checker/parser, not a new clean `python3 scripts/check.py`
run over all 764 files. Reuse ancestry is
764→740→723final→723preformat→684→671→668→666→659→566→520→513→477→453→447→438→clean418.
All fifteen retained baseline ancestry edges, current source/OLean hashes,
compiler/package paths and dependency metadata were checked. Historical
clean418 did not record OLean/package byte hashes; later reuse receipts bind
those artifacts. Public full checks remain `lake build` and
`lake env lean Audit.lean`; local full checking is `python3 scripts/check.py`.
CI outcomes are reported separately.

Project size: 79,918 Lean lines including comments/blanks in 764 files.
This displayed claim adds no numbered ledger entry (20 originals with their
existing disclosures, nine corrected variants). Fixed-profile learner-family
membership, Lemma 5.14, full MVP regret, every chapter and the whole monograph
remain incomplete.
