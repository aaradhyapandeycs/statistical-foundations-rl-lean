# Two-state hard MDP builder handoff

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines
1730–1785 and 1844–1985; SHA-256
`b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
Staged implementation: `.local/HardMDP.lean`; SHA-256
`bec68af1868f1465cbd3048b71e71e8196a5352a8789113958de25dc94043b31`.
This is bounded infrastructure for the correction analysis in
`docs/critic-theorem37-correction.md`, not the source statistical lower bound.

`hardMDP θ good` is an actual `DiscountedMDP Bool Action` with the same finite
global action set at both states: `true` has reward 1, stays with probability
`q=p+α` under `good` and `p` under every other action; `false` has reward 0
and is absorbing under every action. `HardParameters` explicitly enforces
valid transition probabilities and `0 ≤ γ < 1`. `sourceHardParameters_valid`
and `sourceHardParameters` prove and construct those fields from the source's
exact `γ ∈ [2/3,1)`, `0<ε<1/[32(1−γ)]`,
`p=(4γ−1)/(3γ)`, `α=32(1−γ)^2 ε/(9γ²)` without an extra probability-validity
premise. `sourceAlpha_relation` verifies the alternate source α expression.

`hardQ_fixed` proves the candidate equals the model's actual **optimality
Bellman fixed point**, via the actual model operator and its proved uniqueness.
The subsequent source-facing pointwise consequences give

```text
Q_Bellman(true, good) = 1/(1−γq),
Q_Bellman(true, bad)  = 1 + γp/(1−γq),  for bad ≠ good,
Q_Bellman(false, a)   = 0,              for every global action a.
```

The bad first-action value follows optimal continuation; it is not the source
proof's erroneous `1/(1−γp)` formula. `hardValue_gap` proves the exact
algebraic separation and `sourceHardValue_gap_gt_two` proves it is `>2ε`
under the exact source range. `badPolicyQ_fixed` separately proves the real
Bellman fixed point of the deterministic policy which continues choosing a
specified bad action. `hardPolicy_loss_good` gives exact loss
`γq (1/(1−γq)−1/(1−γp))` at the *forced good initial action*; the theorem
`sourceHardPolicy_loss_gt` proves this loss is `>ε` under the source ranges.
Existence of a bad action is not assumed globally: it is supplied explicitly
with proof `bad ≠ good` precisely where this policy is discussed.

**Semantic scope:** the project currently lacks a general theorem that the
optimality Bellman fixed point is the source's optimal infinite-trajectory
`Q*`; this file does not disguise that gap. The results above are proved
Bellman-fixed-point statements; source trajectory identification, the
multi-state/multi-hypothesis sample experiment, testing inequalities, and the
statistical corrected lower bound remain separate work. The two-state model
alone does not cover the general S-state hard family.

Validation: `bash scripts/lean-local.sh .local/HardMDP.lean` passed. A copy
of the exact final staged file with `#print axioms` compiled via the same
wrapper. The ten checked exports `hardMDP`, `hardQ_fixed`,
`optimalityFixedPoint_good`, `optimalityFixedPoint_bad`,
`optimalityFixedPoint_absorbing`, `sourceHardParameters_valid`,
`sourceHardValue_gap_gt_two`, `badPolicyQ_fixed`, `hardPolicy_loss_good`, and
`sourceHardPolicy_loss_gt` use only `propext`, `Classical.choice`, and
`Quot.sound`. The temporary audit file was removed. Independent source review,
publication/export integration, and whole-project build remain for the lead.
