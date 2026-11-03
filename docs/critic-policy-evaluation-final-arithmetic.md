# Independent review: final policy-evaluation arithmetic

**Verdict: pass for the stated conditional high-sample arithmetic.** The result proves the source's final displayed radius from explicit recursive, value-growth and terminal estimates. It does not itself establish those estimates for the statistical experiment, or the complete policy-evaluation theorem.

In `generative_model_model_based.tex:500–634`, the source introduces `b₁=γ√(β/N)`, `b₂=√(2β/((1−γ)N))+β/((1−γ)N)`, `b₃=√2/(γ√(1−γ))`, unrolls the recursion, controls the terminal term, and obtains `3√(8β/((1−γ)³N))`. In the Lean theorem, set `h=1−γ` and `a=√(β/N)`. The binder h is actually an independent positive number at most 1, so the theorem proves a more general real arithmetic statement; its source specialization must supply h=1−γ. The hypotheses include `0<γ≤1`, `β≥0`, `N>0`, `N≥64β/h`, the explicit level depth, `0≤V₀≤1/h`, and the following three inputs:

- `E_l≤b₁E_(l+1)+b₂V_l` for each l<m;
- `V_l≤b₃^l V₀` for each l≤m;
- `E_m≤(γ/h)(a+a²)V_m`, exactly the source Step 4 intermediate terminal inequality.

These are genuine antecedents, not conclusions supplied implicitly by the underlying definitions. In particular, level m must be controlled, even though recursion itself only requires l<m. The theorem quantifies over arbitrary real sequences E and V and makes no claim that they represent actual estimation errors without a separate instantiation.

The proof correctly unrolls the recursion, bounds its finite geometric sum using nonnegative coefficients and `q=b₁b₃≤1/2`, and controls the terminal by `q^m≤h`. The high-sample condition yields `a≤√h/8`, hence q≤1/4≤e⁻¹; `m≥−log h` then gives the claimed tail. The independent ceiling lemma proves the paper's `m=⌈log(e/h)⌉₊` satisfies that depth. There is no division by γ at zero: the source-shaped result requires γ>0, and the separately reviewed zero-discount auxiliary identity supplies the relevant endpoint when connected by a future theorem.

The coefficient arithmetic uses nonnegative factors and derives `6√2√(β/N)/(h√h)`, then proves exactly its equality to `3√(8β/(h³N))`. Thus the numerical constant and powers match the source final display. The sufficient condition is explicitly `N≥64β/h`: the source later writes the weaker `N≥β/h`, and this file does not silently make that transition. The independently reviewed small-sample bound is not composed here. No claim is made that the logarithm β is the source's eventual `C₀ log(Sm/δ)` or that a simultaneous event has already been instantiated.

## Verification

Reviewed staged SHA-256 `d061e921165f62a43bde0b04b38e2ef52ac7eefafd11089987a5b122503dbfeb`; staged recursive-unroll dependency SHA-256 `65c60bebfc05de1b07abd78569e1d9f19f0363e72a3d31990e29044693451109`; source TeX SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. The staged dependency was freshly rebuilt into an isolated project-owned directory. An exact unchanged copy of the source with the original imports and eight appended `#print axioms` commands compiled independently, exit 0. All eight declarations, including the source radius and ceiling lemmas, use only `propext`, `Classical.choice`, and `Quot.sound`. Integrated export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyEvaluationFinalArithmetic.lean` SHA-256 `c713a1b21128b99a8fb15bd7d2115fa46e70777c6d58c34d6776d65b2243d361` differs from the reviewed staged source solely by qualification of its recursive-unroll import. The actual integrated module compiled, and an import-only axiom audit checked all eight exports successfully; each uses only `propext`, `Classical.choice`, and `Quot.sound`.
