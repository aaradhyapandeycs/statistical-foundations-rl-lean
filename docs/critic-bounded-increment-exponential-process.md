# Independent review: bounded-increment exponential supermartingale

**Verdict: pass for the actual restricted-range quadratic exponential supermartingale.** This is a preliminary stochastic ingredient; it does not prove the source's sharp Freedman inequality or any tail estimate.

The source `prelim.tex:1056–1073`, `lem:Freedman-prelim`, concerns a centered bounded martingale-difference sequence and its actual sum of conditional second moments. The staged definition takes a genuine filtration `ℱ : Filtration ℕ m₀`, ambient measure μ, increments X and real t, and constructs

    Z₀=1,
    Zₙ₊₁=Zₙ exp(tXₙ−t² E[Xₙ² | ℱₙ]).

The separately proved closed form is literally `exp(t Σ_{k<n}Xₖ−t² Σ_{k<n}E[Xₖ²|ℱₖ])` pointwise. Index n=0 corresponds to the source's first increment X₁ revealed at time 1; no increment is dropped from the shifted convention. The compensator is the actual conditional expectation under μ, not an assumed deterministic proxy. Z is strictly positive at every outcome.

The full supermartingale theorem assumes μ is a probability measure, B≥0, each Xₙ is strongly measurable at ℱₙ₊₁, `|Xₙ|≤B` a.e., conditional mean `E[Xₙ|ℱₙ]=0` a.e., and `|t|B≤1`. These are assumptions on the actual chosen filtration; it does not infer centering with respect to a larger filtration from centering given only a smaller history. There is no independence, pre-assumed integrability, exponential-supermartingale hypothesis or target tail event.

Adaptedness is proved by induction using filtration monotonicity and strong measurability of each conditional second-moment representative at ℱₙ. Conditional nonnegativity and the increment bound yield `Zₙ≤exp(n|t|B)` a.e.; positivity and finite μ then give integrability at every finite n. For the one-step bound the proof factors the actual Zₙ₊₁ into an ℱₙ-measurable compensated prefix and `exp(tXₙ)`, proves the latter integrable, uses the valid conditional pull-out theorem, and applies the separately reviewed conditional MGF bound. `supermartingale_nat` upgrades the derived one-step inequalities and integrability/adaptedness to the full Mathlib `Supermartingale` structure. The same fixed t is used at every time; negative t, t=0, B=0 and zero increments are covered.

The compensator coefficient is **t²** and the tuning range is `|t|B≤1`. The theorem does not assert the sharper Bernstein coefficient, variance-restricted tail, stopped process, union over dyadic bins, or the exact source `√8` and `4/3` constants. Those are separate obligations; the deterministic peeling module cannot supply them by itself. An application to TD/Q-learning must separately construct the filtration and verify the actual conditional centering/variance identities.

Staged source SHA-256 `5bead892af3f42dd581d80b8625581ad7fee6d71654c1135382da55b8cc1bea0`; staged conditional-MGF dependency SHA `b8680a852d7e27875ae277481959efffbcb570c0421ac9fcc1252f615fdffa8d`; source `prelim.tex` SHA `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. The unchanged source with original imports and six appended axiom checks compiled independently, exit 0, after the conditional-MGF dependency was freshly built in an isolated project-owned directory. The definition and all five theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production export verification remains separate.

## Integrated export verification

Production `Formalization/Probability/BoundedIncrementExponentialProcess.lean` SHA-256 `05b31069722ad934b2ffc9d7f45404f087807225dd526c6bef2dbf12c2b9e98e` differs from the reviewed staged source solely by qualification of the conditional-MGF import. The actual module compiled and import-only checks of all six declarations used only `propext`, `Classical.choice`, and `Quot.sound`.
