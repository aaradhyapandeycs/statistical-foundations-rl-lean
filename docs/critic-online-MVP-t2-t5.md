# Independent review: corrected MVP T2 and T5 bounds

## Scope

This review covers the displayed claims `eq:T2-ub-analysis-mvp` and
`eq:T5-ub-analysis-mvp` in `onlineRL.tex` lines 1793–1810, their Lean
statements and applying wrappers, focused compilation and axiom evidence, and
the affected 811-module integration. It does not close the later MVP
Lemma 5.14 or the full MVP regret theorem.

## Source and statement review

The T2 statement is restricted to K≥2, where the source reciprocal-count
argument applies. Its proof uses the actual same-history retained-row count,
the corrected factor-four reciprocal budget, and fixed constants c₁=4 and
c₂=16. The displayed T5 statement holds for all K≥1 on the actual sequential
episode law. For K≥2, it composes the pathwise T5 decomposition, actual T8 tail
confidence, and the source-radius absorption. It retains the manuscript's
natural-log failure coefficient. For K=1 and every positive H, the proof
handles the zero-iota endpoint directly: with no prior observations the
capped continuation values are state-constant, so T5=W3=0, and T2≥0 closes
the event. This is not an empty-trajectory argument; the single episode still
contains H transitions.

The result uses the corrected MVP conventions disclosed in the source record:
C8 charges H at zero count, C13 uses the power-of-two trigger, C16 uses the
reciprocal confidence allocation, and the greedy planner uses one fixed
deterministic tie rule. T2 uses K≥2; T5 uses K≥1. The coefficients remain fixed
at (4,16). These displayed estimates do not add a numbered named-result entry.

## Compilation and integration evidence

The T2 provider run compiled six targets and checked eight actual exports;
run status SHA-256 is
`62ecaa78903e85435e665ff82e9b9f9d1197e4f66af9ed7bdff667e3c8e37c9b`.
The T5 provider run compiled eleven targets and checked fourteen exports;
status SHA-256 is
`937d540b45ab2e39c67b125dc5b803cb8046053f5aac47008194fd4d2ec9edf5`.
The combined Chapter 5 run compiled both index files and checked seventeen
actual exports; status SHA-256 is
`c0b3e88ce2a2d40be912b865afec46a9cd509f29e8e091c2b0ab5a45f966ef22` and the
probe log SHA-256 is
`194cc615740d88addeb740484c2a57dd7bc192597855d1810fdf324f8ddcd133`.
All requested exports report only `propext`, `Classical.choice`, and
`Quot.sound`.

The affected integration rebuilt 21 modules and verified reuse of 790 modules,
for 811 total. The whole-project axiom audit covered 7,489 declarations and
reported only the permitted standard axioms. The successful manifest
SHA-256 is
`44ace97c0162bcc4a193cc8c3caa8cbf94875dd76379d229bfb517b5cb5c8c6f`.
This is an affected rebuild with verified baseline reuse, not a fresh clean
811-module build. The named-result ledger remains at 20 original entries and
10 corrected variants.

## Remaining scope

The T5 right-hand side still contains W3, T2, and T6UCB; this result does not
by itself establish their later source bounds. The separate source T6 and
Lemma 5.14 assembly remain open. A pointwise range bound `0≤U≤H` alone gives
only a KH³ bound for a sum of squared values, not KH²; the published
martingale/telescope argument remains necessary.
