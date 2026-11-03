# Source review of Chapter 7 candidate issues

Source-only review of the two candidate concerns noted in
`docs/SOURCE-ISSUES.md`. No Lean command was run and no source statement was
changed.

## Model-based algorithm: reward convention

Reviewed `source/upstream/tex/chapters/robust_RL.tex` SHA-256
`95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9` and
`source/upstream/tex/chapters/prelim.tex` SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

The source is internally consistent on the reward convention. The preliminaries
say at `prelim.tex:42` that rewards are deterministic, in `[0,1]`, and fully
known to the learner a priori; `robust_RL.tex:25` repeats the `[0,1]` reward
model and expressly says the chapter focuses on transition uncertainty rather
than reward uncertainty. The model-based algorithm constructs the empirical
model only from
transition frequencies (`robust_RL.tex:204–216`) and retains the same reward
function in the empirical model; the Bellman update also uses that same `r`
(`robust_RL.tex:230–253`). That matches the stated global convention.

Accordingly, I found no source-internal reward-convention contradiction in
the model-based algorithm subsection. A separate citation check may still be
needed to confirm that the
cited TV upper-bound result applies when rewards are known and only transitions
are sampled. That would be citation/proof compatibility, not evidence that the
manuscript's own reward assumptions conflict.

## Chi-squared guarantees: chi-squared radius and confidence scaling

The command file `source/upstream/tex/chapters/commands.tex`, SHA-256
`78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3`, defines
`\ror` to expand to `\sigma` (line 254). The Chapter 7 model sets `\ror>0` as
the radius in the generic uncertainty set (`robust_RL.tex:32–43`). Thus the
different appearances of `\ror` and `\sigma` in the chi-squared discussion are a
notation change, not different parameters.

The upper theorem assumes `γ ∈ [1/4,1)` and the lower theorem assumes
`γ ∈ [3/4,1)`; comparisons of the two bounds apply on their common domain.
The lower theorem also omits an explicit `ε > 0` assumption even though its
sample expression contains `ε²` in a denominator. Positivity is natural for
an accuracy parameter but should be stated explicitly in a formal target.

The chi-squared upper bound at `robust_RL.tex:437–449` has sample factor
`(1 + max{√ρ, ρ}/(1−γ))`; the lower bound at `:461–479` has factor
`(1 + ρ/(1−γ))`. The three regimes discussed at `:493–500` follow these
expressions: for `ρ ≤ (1−γ)^2`, both factors are bounded by constants; for
`(1−γ)^2 ≤ ρ ≤ 1`, the upper factor is `O(√ρ/(1−γ))` and the lower factor is
`Ω(ρ/(1−γ))`, leaving at most an `O((1−γ)^{-1/2})` ratio; for `ρ ≥ 1`, both
factors scale linearly in `ρ/(1−γ)`. I found no radius-scaling contradiction
in these displayed formulas and regime claims.

The theorem's confidence guarantee is `1−δ`, with `log(SAN/δ)` in its sample
threshold (`:438–447`); it does not define a separate confidence radius. The
remark's planning-error scale `O(log(SAN/((1−γ)δ))/N²)` (`:453–457`) has an
additional discount-factor term inside the logarithm, but is a separate
algorithmic accuracy condition; the theorem states it as a sufficient planning
condition, not as an equality to the theorem's sample-threshold logarithm.
Without checking the cited result and its proof, I would not classify this
minor logarithm difference as a source error.
