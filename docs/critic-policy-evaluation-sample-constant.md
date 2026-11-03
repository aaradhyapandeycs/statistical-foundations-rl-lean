# Independent check: sample-threshold constant in the recursive policy-evaluation proof

Reviewed 2026-11-02 against `docs/builder-policy-evaluation-recursive-unroll.md` and raw `source/upstream/tex/chapters/generative_model_model_based.tex`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. No Lean compilation was needed or performed. This reviewer owns only this report.

## Conclusion

The displayed recursive chain proves its intermediate estimate under `N≥64β₁/(1−γ)`. The source then states the final bound under `N≥β₁/(1−γ)` without printing the required case split or a redefinition of β₁. That is an omitted justification in the displayed derivation, **not evidence that the final bound or theorem is false**.

The final bound is repaired with exactly its printed constants by the elementary deterministic value range in the omitted sample regime. No extra sampling argument, changed β₁ or author correction of the theorem statement is needed for that repair. The same patch does not establish every preceding intermediate displayed inequality throughout that regime; those should retain their stronger hypotheses unless separately proved.

## Exact source chain and constants

Write h=1−γ>0, β=β₁, and E=‖Vhat^π−V^π‖∞. The source sets β=C₀ log(Sm/δ) at line 478, with C₀ sufficiently large, and later recalls that same definition at line 634. There is no explicit factor-64 renaming between those lines.

The coefficients at lines 504–509 are

`b₁=γ sqrt(β/N)`, `b₂=sqrt(2β/(hN))+β/(hN)`, `b₃=sqrt(2)/(γ sqrt(h))`.

For γ>0, their product is `b₁b₃=sqrt(2β/(hN))`. Thus N≥8β/h would already suffice for b₁b₃≤1/2; the printed sufficient N≥64β/h at line 589 is conservative, not algebraically wrong. Step 4 additionally uses N>2e²β/h at line 582. The stronger common threshold 64β/h safely implies both requirements.

Step 5 explicitly retains N≥64β/h at line 606. Step 6 combines the estimates and again retains that threshold at line 622. Its bound is

`E ≤ e^(−m) (2/h²) sqrt(β/N) + sqrt(8β/(h³N)) + 2β/(h²N)`.

Setting m=ceil(log(e/h)) controls the terminal term as printed at lines 624–627. The resulting first line is

`E ≤ 2 sqrt(8β/(h³N)) + 2β/(h²N)`.

Absorbing the linear term into one additional copy of the square-root term is valid already when N≥β/h (in fact N≥β/(2h) suffices). That validates the **last arithmetic simplification**, but does not retroactively discharge the stronger sample conditions used to obtain the first inequality.

The source then states

`E ≤ 3 sqrt(8β/(h³N))`

at lines 628–629, with success probability exceeding 1−δ and only N≥β/h at lines 632–633. The earlier high-sample argument alone does not logically permit this weakening. Enlarging a previously fixed C₀ without explicitly tracking old and new β would not be a precise justification for the literal displayed inference.

## Deterministic repair of the omitted sample range

The source reward function lies in [0,1] (`prelim.tex:43`), the discount in [0,1) (`:45`), and its actual discounted trajectory value satisfies `0≤V^π(s)≤1/h` (`:94–105`). The empirical policy evaluation model uses exactly the same known rπ and γ and a normalized empirical transition row (`generative_model_model_based.tex:78–106`). Since π-averaging preserves [0,1], the empirical model's actual value also satisfies `0≤Vhat^π(s)≤1/h` for every outcome. Its inverse expression is that same empirical value by the separately justified Bellman/inverse semantics. Therefore

`E ≤ 1/h`

pointwise, with no concentration event. The difference bound is **1/h**, not 2/h, because both values lie in the same interval [0,1/h].

For the claimed final radius C=3sqrt(8β/(h³N)), its nonnegative square is `C²=72β/(h³N)`. Hence C≥1/h whenever `N≤72β/h`. In particular every omitted case

`β/h ≤ N < 64β/h`

is covered by the deterministic range bound; indeed C>sqrt(9/8)/h there. At N=64β/h either the high-sample case applies or the deterministic bound still suffices.

A rigorous proof of the final printed bound can therefore split as follows:

1. If N≥64β/h, apply the source's displayed recursive/concentration proof, then its terminal and linear-term estimates.
2. If β/h≤N<64β/h, use E≤1/h≤C for every outcome.

This preserves the exact final constant 3sqrt(8), the stated weak threshold and the same β. It also reveals the final statement can be extended to still smaller positive N whenever C≥1/h; such an extension is not required for this repair.

This patch uses the actual reward range and empirical-model value semantics. It would not be available for arbitrary unbounded auxiliary sequences merely satisfying the recursive inequalities. Therefore a generic recursive-unrolling lemma should not silently absorb the factor 64 without these additional genuine MDP facts.

## Why the first intermediate line still needs care

The final-radius repair does not automatically prove

`E ≤ 2sqrt(8β/(h³N)) + 2β/(h²N)`

on the entire weak regime. Put x=Nh/β. Its right-hand side divided by 1/h is `2sqrt(8/x)+2/x`. Near x=64 this is approximately 0.738, less than 1, so the mere value-range bound cannot imply that intermediate estimate there. It may hold for other reasons, but they are not supplied by this patch. A faithful formalization should retain N≥64β/h on that intermediate result and introduce the case split only for the final 3sqrt(8) estimate.

## Probability strictness and theorem status

In the low-sample branch the final success event is the entire sample space, so its probability is exactly one. With δ>0, this is strictly greater than 1−δ, matching line 632. There is no loss from a weak probability estimate in this branch.

In the high-sample branch the simultaneous Bernstein event is stated with probability exceeding 1−δ at lines 471–491. The deterministic recursive estimates hold on that event. Even though Step 3 and Step 6 phrase their conclusions as “at least,” the original strict event can be retained throughout by event inclusion; one must retain that underlying event rather than infer strictness from the isolated weaker probability wording. Thus the patched final strict statement is justified by the source's stated initial concentration event.

The universal constant c₀ in the main theorem (`:142–155`) also gives latitude to require a sufficiently strong sample threshold in a direct theorem proof; its ε≤1/h domain is compatible with doing so. That is a separate route and is not an explicit absorption of the factor 64 in the same fixed-β displayed calculation. Care is still needed to prove the logarithm comparison with β=C₀log(Sm/δ); this report does not certify the entire sharp theorem or its other prerequisites.

The builder note is correct that the weaker threshold does not follow from the displayed preceding chain alone, and correct that this does not refute the theorem. Its claim that constants need “a separate argument or a precisely justified redefinition” can be made concrete: the separate deterministic low-sample case above suffices with **no constant change**. Record this as an omitted proof step with an explicit repair, not as a false source theorem or a required alteration of the final stated sample bound. Zero discount is separately exact; the source auxiliary definitions involving 1/γ require their own positive-discount handling and are not resolved merely by this sample-constant check.
