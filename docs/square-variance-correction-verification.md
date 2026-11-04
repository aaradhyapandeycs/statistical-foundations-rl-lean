# Signed square-variance correction and counterexample

Source: arXiv:2610.41903v1, Lemma 5.22, `lemma:sqv`,
`chapters/onlineRL.tex:3612–3615`; centered-moment proof 3627–3631.
Pinned chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

- General exports: `StatisticalRL.GeneralVariance.variance_square_le_four_of_abs_bound`
  and `StatisticalRL.GeneralVariance.variance_centeredSquare_le_four_of_abs_bound`.
- Full corrected statement: `StatisticalRL.Statements.Lemma5_22_corrected`;
  applying proof: `StatisticalRL.Statements.Lemma5_22_corrected_holds`.
- Exact general-variance refutation:
  `StatisticalRL.SourceCounterexamples.centeredSquare_measure_coefficient_one_false`.
- The original second coefficient 1 fails for the signed two-point law
  P(X=1)=1/8, P(X=−1)=7/8: mean−3/4, VarX=7/16, VarcenteredSquare=63/64.
  The actual finite product measure sample is measurable and |X|=1.
- The repair proves both factor4 inequalities on an arbitrary probability
  space from measurability and the pointwise absolute bound alone. The first
  printed factor4 stays unchanged; the second factor changes1→4. There is
  no extra integrability hypothesis or finite-space restriction.
- Focused qualified checks passed for both providers and their seven actual
  exports, the exact-measure counterexample and its four exports, and the
  combined Ch5/Ch5Proofs with ten actual statement-proof exports. All permit
  only the standard three axioms. The mixed focused index overlay excluded
  the facade/Audit and was not a full project integration claim.
- Guarded affected integration then passed **7 rebuilt+
  664 verified reused=671 modules**. Full audit: **6,484 declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`.
- Run: `20261104T154754690164Z`.
- Manifest SHA-256: `22db88489b141ab493ad3f1fa7a24ca8869e18770b7e3399c54e198715d961ea`.
- Driver SHA-256: `e22e42f24d15f7bb88f1129830e6d968c85b4219da6d176854498b0c2b2b132a`.
- Ch5 statement SHA-256: `895fd593b8b9e0d01bc66d89585122df404e9a51bb9f8d728ecb58db3a14ade8`.
- Ch5 proof SHA-256: `7c34f64a40c6f13413a9acd2b9ac966f7b0beab8d2efc76d575f13d46c4eb0d0`.

This executed the guarded affected-check driver using the pinned Lean wrapper
and repository checker/parser, not a new clean `python3 scripts/check.py` run
over 671 files. Reuse ancestry is 671→668→666→659→566→520→513→477→453→447→438→clean418.
Current source/OLean hashes, retained ancestry edges and compiler/package
paths/metadata were checked. The historical clean418 record did not pin
OLean/package bytes; later receipts bind those inherited artifacts.
Public full-checkout commands remain `lake build`, `lake env lean Audit.lean`;
local full checking uses `python3 scripts/check.py`.

Project size: 73,559 Lean lines including comments/blanks in 671 files.
The ledger has 19 original named entries with disclosed limits plus seven
corrected variants; the false original Lemma5.22 is uncounted. SOURCE-ISSUES
C14 and the independent review explain why current UCBVI use remains valid.
This does not certify other remaining source results or a complete chapter/book.
