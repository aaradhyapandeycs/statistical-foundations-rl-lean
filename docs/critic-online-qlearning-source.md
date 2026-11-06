# Online Q-learning: independent source-review record

Source: arXiv:2610.41903v1, `chapters/onlineRL.tex`;
Theorem 5.16 at 1911–1922, algorithm at 1930–1979, and Lemma 5.18 at 2121–2150.
Chapter SHA-256: `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

This record summarizes independently authored reviews of the proof and its
canonical integration. It is not a new self-certification by the release preparer.
The source audit has SHA-256
`9925acf73a5523145fe516940ddbe298aa9986531b550214903befcb1ed4ff8a`;
the subsequent raw-map qualification addendum has SHA-256
`755baaf5654d28e84bd504a248e321bc9d5516b5ba675b765cbf3e668d89ed73`.
The final canonical consolidation review has SHA-256
`2030f6ff865877c721a4a9484a334def4f7de75b8188b78fd3fc3335cddc193d`.

The reviewers checked the actual sequential iid-reset/selected-row transition
law, completed Q/V update, fixed maximizing policy, previsit counts, observed
successor noise, policy-value regret, weighted stage recursion, confidence
allocation, constants and all positive H,K with 0<delta<1. The expanded
final-type audit found no extra mathematical premise or assumed correctness,
concentration, centering or algorithm-law certificate. The endpoint uses only
`propext`, `Classical.choice` and `Quot.sound` transitively.

The scope remains one fixed deterministic maximizing tie implementation and
the nonterminal V initialization described in [C20](SOURCE-ISSUES.md#C20).
The beta-index equality, signed-stage-weight and confidence bookkeeping in the
printed proof are repaired. These observations do not refute the printed
regret rate. The formal theorem gives a specific universal constant and a
specific logarithmic factor, rather than hiding them in soft-O notation.

The canonical review checked all 20 existing Ch5 proof wrappers plus the two
new wrappers, full statement ascriptions, and preservation of the existing
mathematical declarations after extracting definition-only imports. Its scope
is 665 modules, using qualified reuse; it is not a fresh full-project build.
Comment-only release cleanup preserves every Lean code character outside
comments. A subsequent independent source-only review checked the exact proposed public
tree, and the fresh full checker and axiom audit passed as recorded in the
[verification record](online-qlearning-source-verification.md). The bounded
canonical evidence and the later fresh full build remain separate records.

The entire monograph is **incomplete**.
