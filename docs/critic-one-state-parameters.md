# Independent review: one-state numerical feasibility

Source: `source/upstream/tex/chapters/generative_model_model_based.tex`, Theorem `theorem:azar`, lines 1443–1464; SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. Reviewed exact staged source `.local/OneStateParameters.lean`, SHA-256 `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`. This review is limited to numerical feasibility; it does not certify a counterexample, estimator, MDP lower bound, or an author-approved frozen theorem.

## Independent reconstruction

The printed numerical requirements are `2/3 ≤ γ < 1`, `0 < ε < 1/(32(1−γ))`, `SA ≥ 16`, and `N ≤ c_N log(SA)/((1−γ)^3 ε²)` for a positive small universal constant `c_N`. A proposed one-state witness may choose `S=1`, `A=16`, `γ=2/3`, and the positive natural sample count `N=1`. At these values, `SA=16`, the source accuracy interval is `0<ε<3/32`, and the sample bound becomes `1 ≤ 27 c_N log(16)/ε²`. The endpoint γ=2/3 is allowed; γ=1 is excluded. The source size and sample-count inequalities are inclusive, and both accuracy bounds are strict.

For every c>0, write x=27c log(16)>0 and choose ε=min(1/64,x). Then ε>0, ε≤1/64<3/32, and ε≤1. Hence ε²≤ε≤x and, since ε²>0, `1≤x/ε²`. This works for every positive c, including arbitrarily small c, so it also works for any positive universal constant selected by the theorem.

## Verdict and binder audit

`oneState_parameter_feasible` proves exactly the preceding ε and N=1 sample inequality with ∀ c∈ℝ, 0<c, ∃ ε∈ℝ. Its `min` construction matches the independent argument; `Real.log_pos` is justified by 16>1, the divisor is shown positive, and no bound or existential premise is silently introduced. `oneState_theorem37_hypotheses_feasible` retains the same outer quantifier and witness, adds the inclusive lower discount endpoint and strict upper endpoint, and proves the literal `16 ≤ card (Fin 1) * card (Fin 16)` and the literal sample-size inequality. The initial state/action carriers are concrete finite nonempty types with cardinalities 1 and 16. The N=1 and logarithm values are numerals rather than free parameters; the source permits this specialization. The Lean comparison of N is over reals, after coercion, and does not lose a natural-number restriction because the selected value is exactly 1.

This proves numerical compatibility only. It does not establish the source's independent generative sampling construction, analyze a policy or Q estimator, prove zero policy error, or refute either lower-bound conclusion; those require separately checked MDP and algorithm semantics. The result is a specialization for one γ, not a claim that the same ε works for every γ.

## Verification

`bash scripts/lean-local.sh .local/OneStateParameters.lean` compiled the exact reviewed staged file. A temporary exact source copy with appended `#print axioms` checks was compiled via `bash scripts/lean-local.sh <temporary-probe>`. Both `oneState_parameter_feasible` and `oneState_theorem37_hypotheses_feasible` depend only on `propext`, `Classical.choice`, and `Quot.sound`. This audit did not build an integrated library export or certify the full source theorem. The temporary copy was removed.
