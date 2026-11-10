# Chapter 2 value/policy iteration verification

Source: unlabeled Lemma 2.1, `chapters/prelim.tex:339–343`, with the iteration
definitions at `:319–336`. There is no invented LaTeX label. The full source
index and applying wrapper are `StatisticalRL.Statements.Ch2.Lemma2_1` and
`StatisticalRL.Statements.Ch2.Lemma2_1_holds`.

Both convergence clauses retain the printed factor γ^k and k≥1. VI allows
every initial Q table. PI allows every initial stationary randomized policy
and every maximizing deterministic update, including all tie choices. The
model includes discount zero. `policyFixedPoint` and `optimalityFixedPoint`
represent actual trajectory Q by proved characterization and optimality
theorems; neither equality nor optimality is assumed in the source Prop.

Four genuine definition/existence modules separate the direct source-index
imports from VI/PI proof providers. Existing library declaration names,
signatures and proof bodies are preserved. Choice-defined fixed points use
a transitive proved existence module, as required for their construction;
the definition module does not import the convergence result.

The focused closure rebuilt 25 targets and checked nine actual exports with
standard axioms. Its status SHA-256 is
`95c1b57bc1d1ae34660a21238db027ae72898ffe105ecddaa3c94e45a6dcf2b4`.
The later fresh full-project check validates all affected consumers.

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

[Independent review](critic-ch2-vi-pi.md). Only this source lemma is certified.
