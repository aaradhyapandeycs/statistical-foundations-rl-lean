# MVP actual-product probability and confidence counterexample

Pinned source: arXiv:2610.41903v1, `chapters/onlineRL.tex`, SHA-256
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The 39 new providers prove actual independent-product conditional moments,
reverse reveal order, predictable variance, batch empirical-error identities,
Freedman concentration, finite unions, simultaneous masks, positive-part
projection, finite family enumeration, profile/vector-choice coverage and
source dyadic levels with an explicit logarithmic cardinality budget.
They do not assume a concentration or conditional-law certificate.
Their finite-family premises are stated explicitly. They remain generic
probability infrastructure; the final corrected source-constant comparison
and MVP regret theorem are not certified by this checkpoint.

The necessary-event counterexample is
`StatisticalRL.SourceCounterexamples.MVPUniform.printed_uniform_probability_false`
in `Formalization/Counterexamples/MVPUniformConfidence.lean`.
It uses S=2,A=H=1,K=4, the actual expanded law, the second sample in each
row, family {0,e0,e1}, ε=(320000 log6)⁻¹, δ′=exp(−ε) and δ=(16/25)δ′.
The allocation is exact; iota=1; K≥SAH log₂K and K≥SAH·iota hold.
An allowed data-selected vector choice gives deviation sum1 and variance
sum1/2 for every sample tuple, exceeding sqrt(1/8)+1/4. The necessary event
is empty, but 1−δ′>0. Source C16 explicitly retains the H/H+1 endpoint
ambiguity and the natural bounded continuation-family interpretation.
This is not a refutation of the main MVP regret theorem.

C17 is independently checked source-level evidence of the terminal-value
identification gap. No complete Lean execution comparison of the two
algorithms is claimed. The proposed terminal and confidence corrections
remain visible obligations for the downstream source theorem.

- Focused raw counter: target and 19 actual exports passed with standard axioms.
- Qualified providers: all 39 module compiles and the ordered 73-export
  probe passed, using an isolated library with 684 pinned baseline OLeans.
  The first preflight mapping omitted a private mask provider; it was
  retained, fixed and independently rechecked before the successful run.
- Affected integration: **9 rebuilt+714 verified reused=723
  project modules**, **6,876 declarations** with only propext,
  Classical.choice and Quot.sound.
- Run: `20261104T175908349662Z`.
- Manifest SHA-256: `e680c9d04b2f2425c67172cb3464c5dcb1510e2804ee4bf5f7a9f65097514c0b`.
- Driver SHA-256: `532a94e6f37a297b1903763b1dbbf0faa60544cdf428bc93321dd130c0ef240e`.
- Qualified receipt SHA-256:
  `9f2425dfd7d51e6d7b50f40bcf5a08566e18ca1f128a45c7f5f6a1922f8de589`.

This local validation executed the guarded affected-check driver with the
pinned Lean wrapper and repository checker/parser. It is not a new clean
`python3 scripts/check.py` run over 723 files. Reuse ancestry is
723→verified723→684→671→668→666→659→566→520→513→477→453→447→438→clean418. All current
source/OLean hashes, retained reuse edges, compiler/package paths and
metadata were checked. Historical clean418 did not record OLean/package
byte hashes; later receipts bind those inherited artifacts. Public full
checks remain `lake build` and `lake env lean Audit.lean`; local full checking
uses `python3 scripts/check.py`. CI results are reported separately.

Project size: 76,666 Lean lines including comments/blanks in 723 files.
No source certification is added to the 20-entry/eight-variant ledger.
Every chapter and the whole monograph remain incomplete.

Final formatting follow-up: one trailing space was removed from a new proof
line. The original check of 723 files rebuilt 41 modules with 682 reused;
the final whitespace-clean check rebuilt 9 affected modules with 714 reused.
Both audited 6,876 declarations. The executed final driver's prose says
"twelve" retained ancestry edges; its actual 14-snapshot loop checks all 13.
Independent review checked the full loop and source/artifact edges. The
raw executed driver and receipt remain pinned; this note corrects that
metadata wording without changing proof evidence.
