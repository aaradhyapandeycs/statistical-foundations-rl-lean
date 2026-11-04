# Independent review: corrected UCBVI regret theorem

I compared `StatisticalRL.Statements.Thm5_2_corrected` and its applying proof
with Theorem 5.2 (`thm-ucbvi-regret`) in
`source/upstream/tex/chapters/onlineRL.tex:470–482`; the proof's iota is at
726–734 and its T0 definition is at 1027–1033. The pinned source chapter SHA-256
is `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The Lean statement quantifies finite state/action spaces, positive horizon,
every `K≥1`, an initial distribution, and `0<δ<1`. It measures regret at
each observed episode initial state, comparing the true optimal stage value
with the true value of the policy actually deployed that episode. The
probability is under the actual iid reset-vector and causal sequential
transition law. It makes the source's existential bonus-constant choice
explicit as `c₁=4`, `c₂=16`, and states the stronger explicit rate
`20 (√(SAH³K) + S²AH³) (1+iota)` with probability at least `1−δ`.
The printed source uses `\widetilde O`; the Lean rate records a concrete
bound for that claim. The iota formula is the one defined by the source.

The applying proof instantiates the actual high-probability producer at the
fixed constants, unfolds the source-facing regret event, and weakens its
strict probability conclusion to the indexed `≥1−δ` form. The producer does
not take concentration, variance, optimism, or regret estimates as
hypotheses: the large-sample branch consumes the proved actual T0/T56
confidence chain and scalar closure. `K=1` and the small-sample branch use
the deterministic `regret≤KH` bound. Thus the auxiliary K≥2 restrictions
tracked by C12 do not restrict Theorem 5.2.

This is explicitly the corrected finite zero-count implementation under
C8, with one fixed deterministic maximizing tie rule. It does not certify
the literal source algorithm where the zero-count bonus is undefined, nor
does it claim the rest of Chapter 5 or the monograph is complete.

## Integrated build evidence

The final statement SHA-256 is
`8f1dbb2dac9dfa504513985c219ac255d7a3e8e00f55d68b7542f606a732d726`; the
applying proof SHA-256 is
`ed84ada595d2ab2cb530f6aca4516fbcc40e8e3b6ef42329775c047ea13c9ab5`. The
qualified main source modules and both full Chapter 5 index modules passed
focused builds and actual-export probes before integration.

For the final integration, I independently recomputed all 666 frozen source
hashes and corresponding OLean hashes in both the candidate and synchronized
workspace; every source and artifact matched. The terminal manifest records
success, 11 rebuilt modules, 655 verified reused modules, zero exits for all
rebuilt targets and for `Formalization` and `Audit`, and an axiom audit of
6,443 project declarations. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound`.

The run is `20261104T143612216885Z`; its manifest SHA-256 is
`104ff5105977167d1d9b5641111f6460b8d7728433327b9705ca6f7d1d382678`.

This is an affected rebuild against the verified 659-module baseline, not a
fresh clean 666-module build. The retained source/artifact ancestry is
666→659→566→520→513→477→453→447→438→clean418. Compiler and dependency paths,
compiler binary, and shared-package metadata matched the recorded checks.
The historical clean418 record did not pin OLean/package byte hashes; later
reuse receipts bind those inherited artifacts. Full build and source review
supports the corrected main theorem entry; it does not imply that the C8
algorithm correction has been adopted by the paper's authors.
