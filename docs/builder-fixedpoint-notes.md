# Builder notes: Bellman fixed points

`Formalization/MDP/FixedPoint.lean` extends the actual operators in
`Formalization/MDP/Basic.lean`. It is infrastructure for Chapter 2 of
arXiv:2610.41903v1; this builder record does not replace independent review.

## Results

- `qBellman_contracting` and `qOptimality_contracting` use the existing
  supremum-norm inequalities, with contraction constant exactly the source's
  discount `γ`. Nonnegativity and `γ < 1` come from the actual MDP fields.
- `policy_fixedPoint_exists_unique` and
  `optimality_fixedPoint_exists_unique` prove exact existence and uniqueness
  in the complete finite function space. No fixed-point existence premise is
  added to the source model.
- `policyFixedPoint` and `optimalityFixedPoint` are defined only after these
  existence-and-uniqueness results. Their `_spec` theorems prove the complete
  defining equations, and their `_characterization` theorems prove that a
  function solves the equation if and only if it equals the selected object.
  Choice is therefore independent of the witness.
- `value_iteration_error` proves the exact bound
  `‖T^[n] Q₀ - optimalityFixedPoint‖ ≤ γ^n * ‖Q₀ - optimalityFixedPoint‖`
  for every natural `n`, using the actual optimality Bellman operator and any
  initialization. `tendsto_value_iteration` proves actual norm-topology
  convergence.
- `policy_evaluation_iteration_error` and
  `tendsto_policy_evaluation_iteration` prove the corresponding results for
  repeated evaluation backups with one **fixed** randomized policy. These
  are not the source's policy-improvement algorithm `PI`.
- Both Bellman maps preserve the interval `[0, 1 / (1 - γ)]`. Starting from
  the zero function, every iterate lies in that interval. Passing to the
  proved limit gives `policyFixedPoint_bounds` and
  `optimalityFixedPoint_bounds` with exactly those endpoints.

## Source correspondence and remaining semantic obligations

Source file: `source/upstream/tex/chapters/prelim.tex`.

| Source | Implemented mathematics | Status boundary |
|---|---|---|
| Lines 188–209, `eq:bellman_consistency_operator`, `eq:bellman_consistency` | Actual policy Bellman map has exactly one fixed point. | Identification with the independently defined expected discounted trajectory return `Q^π` remains open. |
| Lines 235–245, `eq:bellman_optimality_operator`, `eq:bellman_fix_point` | Actual optimality Bellman map has exactly one fixed point. | Identification with the trajectory-optimal `Q*`, and existence of an optimal deterministic policy, remain open. |
| Lines 316–321, `eq:value_iteration`; lines 339–355, VI part of the linear-convergence lemma | Actual optimality-operator iterates satisfy the exact geometric error bound relative to their unique fixed point. | The whole lemma is not complete: its target is the trajectory-optimal `Q*` and it also includes policy iteration. |
| Lines 95–109: return interval, with normalized rewards and `0 ≤ γ < 1` from lines 31–45 | Both selected Bellman solutions lie in the same exact interval. | This does not by itself prove that an expected path-return object equals the selected solutions. |

No main source result should be marked fully formalized on the basis of this
module alone. The trajectory law, infinite discounted expectation,
Bellman/trajectory equivalence, optimal deterministic policy, and actual `PI`
algorithm are separate obligations.

## Validation

Focused compilation uses the pinned toolchain and read-only dependency cache:

```sh
bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/MDP/FixedPoint.olean Formalization/MDP/FixedPoint.lean
```

The module contains no custom axioms or proof placeholders. Integration and
independent source review remain separate gates.

Focused compilation succeeded. An ephemeral `#print axioms` probe checked
both exact existence-and-uniqueness results, both defining equations, both
complete characterizations, the value-iteration error and convergence results,
and both fixed-point interval bounds. The probe exited successfully and every
closure contained only `propext`, `Classical.choice`, and `Quot.sound`.
The transient probe was removed afterwards.
