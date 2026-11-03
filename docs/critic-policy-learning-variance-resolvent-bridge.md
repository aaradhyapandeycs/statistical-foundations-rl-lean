# Independent review: empirical variance through true-policy resolvent

**Verdict: pass for the stated deterministic bridge.** The file does not assert a probability event or a finished policy-learning theorem.

The source at `generative_model_model_based.tex:1379–1415,2637–2715` applies the positive true-policy inverse to the empirical-value variance expansion and combines the result with an all-row residual event. Put `h=1−γ>0`, `W=H.trajectoryExpectedValue π`, `z=(P_H,π−P_M,π)W`, `σ=Var_{P_M,π}(W)` and `R=(I−γP_M,π)⁻¹`. M,H are valid finite discounted MDPs, π is any stationary randomized policy, and the general deterministic results explicitly assume the same reward and discount. They do not assume anything about the sign of `r+γz` or that π is independent of data.

The first bound applies proved nonnegative inverse order to the already proved **pointwise empirical** variance inequality. With `A=I−γP_M,π`, it rewrites the signed term as `−A(W²)`, applies R to both sides, cancels the genuine invertible matrix R A, and drops `−W²`. The constant-vector identity `R1=1/h` and nonnegativity of `Rσ` and `R|z|` justify the finite sup-norm step. The exported inequality is exactly

    γ² ‖Rσ‖∞ ≤ 2/h² + (2γ²/h) ‖R|z|‖∞.

The next bound uses the independently proved generic Jensen inequality for arbitrary nonnegative σ, not the true-value-only variance result. It squares nonnegative sides and obtains

    γ² ‖R√σ‖∞² ≤ 2/h³ + (2γ/h²) (γ‖R|z|‖∞).

This retains a factor γ that the source can weaken using γ≤1. In particular, the true-kernel forcing of empirical W may be negative; see the explicit positive-probability example in `critic-policy-learning-empirical-variance-self-bound.md`. The code does not use the nonnegative-forcing theorem on that W.

For general nonnegative a,b and the explicit statewise residual premise `|z|≤a√σ+b`, the source bound follows from positive R, its row sum, generic Jensen and the preceding variance inequality. The β specialization uses N>0 and β≥0, `a=√(β/N)` and `b=2β/(Nh)`. Its scalar manipulation correctly bounds the extra γ by 1, obtains the previously checked `S≤A+2B+√(2BS)` with `S=γ‖R|z|‖∞`, `A=√(2β/(Nh³))`, `B=β/(Nh²)`, and concludes the precise source radius `2√(2β/(Nh³))+6β/(Nh²)`. The row premise is exposed explicitly; the module does not present it as a proved good event.

The separate true-inverse identity derives `(I−γP_M,π)(W−V_M^π)=γz` from both actual Bellman equations, then proves `W−V_M^π=γRz` using proved invertibility. Nonnegative R gives `|Rz|≤R|z|`, so the same bound holds for the actual empirical-minus-true policy value error. Its final specialization uses H equal to the actual sample-built empirical MDP and the point-mass policy selected by the same sample, with same-reward/discount equalities by reflexivity. This is a pointwise deterministic statement: an all-action event must still supply the chosen policy's row premise after selection. No independence of the fitted policy is claimed.

All displayed inequalities hold at γ=0; denominators use only h>0. N=1, β=0, zero variances and zero residual are admitted by the corresponding explicit hypotheses. The source's probability bound, postselection bridge, comparison with the true-optimal policy and final sample complexity remain separate.

Staged SHA-256 `ddc7b3c954362ffad70c249d9ac37c2aa5b726be402a0d733f5471bbb800741b`; staged Jensen SHA-256 `0adf2b1d01b4c4463f5c6fec291e1fe549afc76be242374a2d744f72b2d00a2e`; staged self-bound SHA-256 `55c8045d77c988c70228066f28f485e134de5ca1a78ebf8ce6a760bd7e24c95c`. An exact unchanged source copy with original imports and nine appended axiom checks compiled independently, exit 0, after both staged dependencies were freshly rebuilt in an isolated project-owned directory. All nine theorem exports use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningVarianceResolventBridge.lean` SHA-256 `f10905404436e92d5c0afe97b8221c7831d200a34dcd6c7998875d4e8d5b6b22` differs from the independently reviewed staged source only by qualification of its two staged imports. The actual integrated module compiled, and an import-only audit of all nine theorem exports used only `propext`, `Classical.choice`, and `Quot.sound`.
