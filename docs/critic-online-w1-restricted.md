# Independent review of the restricted W₁ clause

## Source correspondence and scope

The reviewed statement is `Lemma5_7_W1_K2_corrected` in
`Formalization/Statements/Ch5.lean` (source SHA-256
`3dc2d738571ca3b22d49ea5ed01de196620c73241777ada272bb57b59f001fa1`). It
formalizes only the W₁ clause of the source's W₁/W₂/W₃ lemma at
`source/upstream/tex/chapters/onlineRL.tex:928–953`, with W₁ defined at
lines 910–922 and its logarithmic factor at lines 726–733.

The statement keeps the source sample law, pre-episode history, fixed greedy
planner, and actual visited state-action-stage rows. Its T₆ policy and
difference quantities use the true transition row and the same selected
episode policy/capped continuation as the source definitions. The W₁ event
contains the source's three right-hand terms: both square-root coefficients
are `S*A*H`, the additive coefficient is `S*A*H^2`, and the confidence is
`1 - 12*S^2*A*H*K*δ′`.

This is a disclosed restricted/corrected variant. It assumes `K ≥ 2`, because
the printed `iota` is zero at `K = 1` (Candidate C12 in
[`SOURCE-ISSUES.md`](SOURCE-ISSUES.md)). It uses the finite zero-count
completion and fixed deterministic tie rule documented under Candidate C8.
The result proves neither W₂ nor W₃, and it does not prove the full source
lemma or a regret bound.

## Proof and focused evidence

The applying proof is `Lemma5_7_W1_K2_corrected_holds` in
`Formalization/Statements/Ch5Proofs.lean` (source SHA-256
`e5fc45a06dbc677d8a221f30fbe4f2968a065b931e4c86ecf4b2fa9d60555bb8`). It
consumes the source-allocated restricted W₁ export. That export gives the
stronger failure coefficient `6*S*A*H*K*δ′`; the wrapper weakens this to the
printed `12*S^2*A*H*K*δ′` using `S ≥ 1`. No concentration or variance bound is
assumed by the statement.

The qualified preview preserved 34 theorem command/proof bodies across 23
proof modules and added one seven-definition module with no theorem
declarations. It reuses existing public regret definitions and the actual-row
theorem rather than declaring duplicates. All 24 qualified modules compiled
in the focused run. The four-export probe exited successfully and reported
only `propext`, `Classical.choice`, and `Quot.sound`. The focused index check
compiled the Chapter 5 statement and proof modules and their probe; all three
commands exited successfully, and the probed export reported the same three
axioms.

The affected whole-project integration check passed: 28 modules were rebuilt
and 449 reused from the verified 453-module baseline. The complete 477-source
freeze and all 477 current source/OLean hashes match the successful candidate;
the whole-library audit covered 5,240 declarations and found only the three
standard axioms. The successful integration record is run `20261104T075344964449Z`; its
manifest SHA-256 is
`3e0dc0bc0958019e9fd344cea5dbfbccc6032086feb1ac4590235aebc77e29f5`.
This is an affected rebuild, not a fresh 477-module clean build. Its provenance
chain is 453→447→438→clean418; the historical clean418 manifest did not pin
OLean or external package bytes, while later reuse receipts pin inherited
project artifacts. This review still makes no claim that the complete
W₁/W₂/W₃ lemma or regret analysis is proved.
