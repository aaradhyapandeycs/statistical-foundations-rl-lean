# Independent review: policy-evaluation recursive unrolling

**Verdict: PASS for the stated real-sequence unrolling, geometric bound, and deterministic small-sample trajectory-value estimate.** The small-sample estimate provides a mathematically valid way to cover the source's omitted sample-size interval, conditional on separately proving the large-sample probabilistic branch. It does not establish the source's recursive concentration event, terminal error bound, γ=0 treatment, or sharp theorem. This is a staged review, not an author-approved source correction.

Reviewed `.local/PolicyEvaluationRecursiveUnroll.lean`, SHA-256 `65c60bebfc05de1b07abd78569e1d9f19f0363e72a3d31990e29044693451109`, and `docs/builder-policy-evaluation-recursive-unroll.md`. Pinned source is `source/upstream/tex/chapters/generative_model_model_based.tex`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. The recursive comparison is `eq:upper-bound-Vl-Vhatl`, the auxiliary norm estimate `eq:Vl-inf-norm-bound-0`, and unrolling `eqn:Chopin` around lines 435–546; Step 5 and the final displayed condition are around 589–634.

## Exact recursion and geometric bound

For all `l<m`, the staged `auxiliary_error_recursion_unroll` takes the **explicit** prior statements `E_l≤b₁E_{l+1}+b₂V_l` and `V_l≤b₃^l V_0`, with `b₁,b₂≥0`. It proves

```text
E_0 ≤ b₁^m E_m + b₂ (Σ_{l=0}^{m−1}(b₁b₃)^l) V_0.
```

Induction uses `b₁^n≥0` and `b₂≥0` to preserve inequality directions. The exponent and indices, terminal error, and finite sum match `eqn:Chopin`, including m=0. No sign of `b₃` or V₀ is needed for this first statement because the input `hvalue` is directly quantified; the proof does not smuggle in the desired norm estimate. E and V are arbitrary real sequences, so the lemma is a conditional algebraic bridge, not a construction of the source's auxiliary values or a concentration theorem.

`auxiliary_geometric_sum_le_two` checks `0≤q≤1/2` and gives `Σ_{l<m}q^l≤2`. `auxiliary_error_recursion_unroll_half` requires in addition `V_0≥0` and `0≤b₁b₃≤1/2`, exactly what is needed when multiplying the geometric inequality by `b₂V_0`. It retains `b₁^m E_m`; no terminal term is discarded or bounded by an unstated premise. Source meanings are `E_l=‖V̂^(l)−V^(l)‖∞`, `V_l=‖V^(l)‖∞`, and its displayed b₁,b₂,b₃. For positive γ, β and N these are nonnegative, but connecting the source definitions, actual models and concentration events to the abstract hypotheses remains separate work.

## Source threshold and the proposed repair

Write `h=1−γ>0`, `β=β₁`. The source's Step 5 and its immediately combined estimate explicitly require `N≥64β/h` (lines 589–622), but the final `eqn:ice-cream` is presented under `N≥β/h` (lines 624–634). The latter condition alone does not imply the displayed geometric-step hypothesis: the source ratio is `b₁b₃=sqrt(2β/(hN))`; at `N=β/h` it is `sqrt 2>1/2`. This identifies a missing justification in the displayed proof chain, not a counterexample to the final theorem. The source's earlier terminal estimate also has a stricter large-N requirement, which is covered by the stated 64 threshold; all relevant large-branch hypotheses still have to be proved.

`trajectoryValue_difference_le_horizon` establishes `‖V̂−V‖∞≤1/h` for the **actual infinite-trajectory values** of two admissible MDPs with the same discount and any common stationary policy. This uses each value's genuine `[0,1/h]` bound; equality of the MDPs' rewards or transitions is not required. The integrated empirical plug-in estimator can only be substituted after its separately proved `valueEstimator_eq_trajectory` and discount identity are used; the generic lemma does not itself assert that substitution.

`trajectoryValue_small_sample_bound` then proves, for `β≥0`, `N>0`, and `N≤72β/h`,

```text
‖V̂−V‖∞ ≤ 1/h ≤ 3 sqrt(8β/(h³N)).
```

The constant 72 is exact for this comparison: after squaring positive sides, `1/h²≤72β/(h³N)` is equivalent to `N≤72β/h`. The endpoints are included. This deterministic branch covers the entire interval below the 64 threshold and overlaps the large branch. Consequently, a **separate case split** can support the source final radius throughout its weaker condition if the large-sample bound, actual model substitution, shared probability event, β definitions, and remaining arithmetic are all established. The staged helper alone does not prove those premises or the probabilistic theorem.

The source's displayed recursive constants include `1/γ` (in b₃), so the γ=0 endpoint cannot be justified by those expressions without separate treatment. The present generic algebra does not claim otherwise; the small-sample deterministic estimate itself remains valid at γ=0. A source-level proof covering all γ in `[0,1)` needs an independently justified γ=0 branch for any remaining regime.

## Independent validation and integration boundary

The exact staged source was copied unchanged to a temporary probe with five `#print axioms` commands and compiled against the integrated `Formalization.Generative.PolicyEvaluationVarianceResolvent` dependency using `bash scripts/lean-local.sh`. Compilation succeeded without diagnostics. `auxiliary_error_recursion_unroll`, `auxiliary_geometric_sum_le_two`, `auxiliary_error_recursion_unroll_half`, `trajectoryValue_difference_le_horizon`, and `trajectoryValue_small_sample_bound` each use only `propext`, `Classical.choice`, and `Quot.sound`. No Lean source was modified in this review.

This check supports landing these helper declarations after the usual import/build audit. It does not resolve the source's unspoken constant/threshold intention, prove the auxiliary vectors or uniform Bernstein event, remove the terminal error, or certify the chapter's sample-complexity theorem.

## Integrated export recheck

`Formalization/Generative/PolicyEvaluationRecursiveUnroll.lean` is byte-for-byte identical to the reviewed staged file; both SHA-256 values are `65c60bebfc05de1b07abd78569e1d9f19f0363e72a3d31990e29044693451109`. The actual integrated source was compiled to the previously absent project-owned module artifact with `bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationRecursiveUnroll.olean Formalization/Generative/PolicyEvaluationRecursiveUnroll.lean`, with no diagnostics. A separate import-only probe of `Formalization.Generative.PolicyEvaluationRecursiveUnroll` printed axioms for all five exports named above; all again contain only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the actual integrated declarations and preserves the source-scope qualifications above; a complete project-wide integration audit remains separate.
