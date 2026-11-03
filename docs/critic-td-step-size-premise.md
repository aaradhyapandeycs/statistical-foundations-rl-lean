# Source review: TD step-size lemma omits an essential premise

Reviewed `lemma:TD-step-size` at `source/upstream/tex/chapters/generative_model_model_free.tex:317–327` and its appendix proof at lines 2288–2320. Source SHA-256: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. This is a source/math review; no Lean lemma for this result is currently staged and no compiler was used.

## Premise gap and counterexample

The standalone lemma assumes the rate interval

`1/(1+c₁(1−γ)T/log²T) ≤ ηᵢ ≤ 1/(1+c₂(1−γ)i/log²T)` for `1≤i≤T`, `c₁≥c₂>0`, `c₁c₂≤1/8`, and `t≥T/(c₂ log T)`. It claims `η₀^(t)≤1/T²` for `0≤k≤t/2` (and the stated late-index bound). But appendix step (i) requires

`(1−γ)ηᵢ ≥ log²T/(2c₁T)`.

From the lower rate bound, this follows only if

`T ≥ log²T/[c₁(1−γ)]`;

indeed, this is exactly the condition making `1+c₁(1−γ)T/log²T ≤ 2c₁(1−γ)T/log²T`. The printed standalone lemma does not assume this. Its proof later uses the same missing condition explicitly at Appendix C, line 2309. The separate condition `T≥c₁⁻¹log²T` used in step (iii) does not imply it when `1−γ` is small.

Concrete counterexample: choose `c₁=c₂=1/4`, `T=t=100`, and `γ=1−10^{-6}`. Then `c₁c₂=1/16≤1/8`, and `t≥T/(c₂ log T)` because `log 100>4`. Set every `ηᵢ` equal to the interval's lower endpoint

`η = 1/(1+(1/4)(1−γ)100/log²100)`.

Since `i≤T` and `c₁=c₂`, this rate satisfies both interval bounds for every `1≤i≤T`. But `η≤1`, so

`η₀^(100)=∏_{i=1}^{100}(1−η(1−γ)) ≥ γ^{100} ≥ 1−100·10^{-6}=0.9999 > 1/10000=1/T²`.

Thus the early-index conclusion is false under the printed standalone premises. The omitted premise fails here by orders of magnitude: `log²(100)/[(1/4)10^{-6}]` is about `8.5×10^7`, not at most 100.

The schedule is stated only for `1≤i≤T`; the lemma also says “any t≥…” without explicitly `t≤T`. Because the product and rate bounds use indices only defined through T, the intended source domain must include `t≤T` (likely implicit from iterates in a T-step algorithm). A formal standalone statement should include this upper time domain explicitly.

## Relationship to the main TD theorem

This is a gap in the standalone auxiliary lemma, not by itself a counterexample to the main TD theorem. The main theorem also assumes

`T ≥ c₃ log³(T) log(ST/δ)/[(1−γ)³ ε²]`, with `0<δ<1` and `ε≤1/(1−γ)`.

Writing `h=1−γ`, its range implies `h³ε²≤h`, hence

`T ≥ c₃ log³(T) log(ST/δ)/h`.

For `S≥1`, `T≥2`, `δ<1`, both `log T` and `log(ST/δ)` are at least `log 2`. Thus choosing the universal sample constant large enough that `c₃(log 2)²≥1/c₁` implies the missing `T≥log²T/(c₁h)` in the theorem's application. The cited appendix explicitly says this is ensured by the main sample-size premise for sufficiently large `c₃`. It does not make the isolated Lemma 4.3 statement valid for arbitrary admissible `T,γ`.

**Verdict:** add the missing gamma-dependent T premise and `t≤T` to a standalone formalization, or state the lemma conditionally under the main-theorem sample-size regime and prove that implication. Do not use the current standalone wording as a valid general lemma. The main theorem may still be sound because its stronger sample threshold supplies the extra condition.
