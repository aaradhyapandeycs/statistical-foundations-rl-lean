# Independent review: deterministic Freedman variance peeling

**Verdict: pass for the stated deterministic dyadic coverage and square-root comparison.** The file does not prove Freedman's inequality or any stochastic tail bound.

The source `prelim.tex:1056–1073`, `lem:Freedman-prelim` / `eq:Freedman-random`, states a fixed-n martingale concentration bound whose radius contains `√(8 max(Wₙ,σ²/2^K) log(2K/δ))` and an additional `(4/3)B log(2K/δ)` term. It assumes K≥1 and an upper bound `0≤Wₙ≤σ²`; the variance is random and remains inside the radius. This module is only the real-number step needed to replace a selected deterministic bin scale by that random variance and its bottom cutoff.

For K positive, `0≤w≤v`, `dyadic_variance_bin_cover` proves some natural j<K satisfies `w≤v/2^j≤2 max(w,v/2^K)`. It uses the K upper scales `v/2^j`, j=0,…,K−1. Induction handles the top half by j=0 and recurses on v/2 otherwise; the shifted exponent identity is separately proved. The lower comparison is correctly `w≤` the selected upper scale, and the upper comparison has the factor 2 needed for the radius. Bin boundaries may overlap, which does not affect this existential coverage or a later union bound.

The edge cases are covered: at K=1, j=0; at w=v, j=0; at w=0<v, the last upper scale is `2v/2^K`; at the bottom cutoff w=v/2^K, that same endpoint is valid; and v=w=0 gives zero everywhere. No division by w or v appears. The additional assumption L≥0 in `dyadic_variance_radius_cover` justifies multiplying the bin inequality, yielding exactly `√(4(v/2^j)L)≤√(8 max(w,v/2^K)L)`. Source `L=log(2K/δ)` is positive when K≥1 and `0<δ<1`; the helper does not itself assert a logarithmic or probability statement.

The factor 4 on the left is a numerical input to this comparison. To obtain the source theorem, a later proof must establish an actual variance-restricted martingale tail inequality with a compatible radius and linear term, construct measurable events for all K bins and both tails, allocate the `log(2K/δ)` confidence budget, and handle the source filtration and conditional moments. This file provides neither that stochastic premise nor a Freedman, TD or Q-learning theorem.

Staged SHA-256 `010f97d59be568ea443fe38f40e51ac83b4cd95ebcde8f118bb3fb76935b15da`; pinned `prelim.tex` SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. An exact unchanged source copy with original imports and three appended axiom checks compiled independently, exit 0. All three theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production import/export verification remains separate.

## Integrated export verification

Production `Formalization/Probability/FreedmanVariancePeeling.lean` is byte-identical to reviewed SHA-256 `010f97d59be568ea443fe38f40e51ac83b4cd95ebcde8f118bb3fb76935b15da`. The actual module compiled and import-only checks of all three theorems used only `propext`, `Classical.choice`, and `Quot.sound`. This remains a deterministic prerequisite, not stochastic Freedman.
