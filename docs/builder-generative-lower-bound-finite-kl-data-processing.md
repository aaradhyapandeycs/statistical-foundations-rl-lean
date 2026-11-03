# Finite-law KL data processing

Staged source: `.local/GenerativeLowerBoundFiniteKLDataProcessing.lean`, SHA-256 `42266d3ed4e3d29502071f84ebb5faebaeb13772b19a130f9ca9862701103b67`. Its staged export compiled; `#print axioms` for the main inequality and the finiteness lemma reports only `propext`, `Classical.choice`, and `Quot.sound`. Independent review is pending.

`finite_klDiv_map_le` states the oriented inequality KL(map f μ || map f ν) ≤ KL(μ || ν), with `toReal` on both sides, for finite measurable spaces, actual probability measures μ and ν positive on each input atom, and an arbitrary deterministic decoder f. It uses the genuine measure pushforwards. Fibers can be empty, so output laws need not have full support. The proof applies the compiled finite-cell log-sum inequality to each fiber and sums across all outputs.

`finite_klDiv_eq_expression_of_ac` proves the actual KL atomic formula under absolute continuity, including a zero reference atom: absolute continuity also forces the corresponding first-law atom to zero. `finite_klDiv_ne_top_of_ac` records finiteness for any absolutely continuous finite probability laws. For the main theorem, full support gives input absolute continuity and it is preserved by the map; thus both finite-law KLs satisfy this finiteness lemma. The lower-bound family laws may instantiate this generic result once their input full-support property has been connected explicitly.

This result does not yet construct the finite-mixture entropy bound, show the log K or log 2 constants, derive Fano, or establish a multi-hypothesis lower bound. Its dependencies include staged `.local` imports; this compilation does not establish a production export.
