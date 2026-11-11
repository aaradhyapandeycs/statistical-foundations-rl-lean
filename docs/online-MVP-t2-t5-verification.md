# Corrected actual MVP T2 and T5 verification

The source displayed estimates are `eq:T2-ub-analysis-mvp` and
`eq:T5-ub-analysis-mvp` (onlineRL.tex:1793–1810). The complete statement
Props are `StatisticalRL.Statements.Ch5.MVP_T2_K2_corrected` and
`StatisticalRL.Statements.Ch5.MVP_T5_corrected`, with corresponding `_holds`
wrappers. They use the actual retained-table path and sequential law.

T2 uses the source bonus for positive counts and analysis charge H at zero
(C8), the power-of-two trigger (C13), reciprocal confidence allocation (C16),
fixed 4/16 coefficients and one deterministic greedy tie. Its K≥2 scope is
explicit (C12). T5 retains the source natural-log probability coefficient,
uses the same corrected conventions, and proves K=1 directly for arbitrary
positive H. Neither displayed result increments the numbered-result ledger.

Qualification: six T2 providers and eight actual-export axiom checks, eleven
T5 providers and fourteen checks, followed by two full Chapter 5 targets and
seventeen applying-proof checks. Affected integration rebuilt 21 and
verified reuse of 790 = 811 modules, auditing 7,489 declarations
for the standard axioms. This is not a new clean full build. Run
`20261104T220311973277Z`, manifest SHA-256 `44ace97c0162bcc4a193cc8c3caa8cbf94875dd76379d229bfb517b5cb5c8c6f`,
driver SHA-256 `a097e041bfa5daeaf87739ccab37760a43854c561fd4ca87fdeb353f4e15b69b`. Size 83,076 Lean lines including
comments/blanks. Ledger remains 20 original entries plus 10 corrected variants.
MVP Lemma 5.14 and full MVP regret remain open.
