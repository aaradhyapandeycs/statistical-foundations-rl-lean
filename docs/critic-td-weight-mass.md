# Independent review: TD weight-mass telescope

Reviewed staged source `.local/TDWeightMass.lean`, SHA-256 `83079db47744cf71da4166252576af2f916ec7a4ee87a9ced95174f3e80871db`. Its production dependency `Formalization/ModelFree/TDLearningWeights.lean` has the same SHA as the staged helper, `45cebbdcb5ff62d586b28932803ae727ec2f1d31bb814346c7e5886e3c19a59f`.

## Source and semantic review

The recurrence is correctly indexed: on advancing terminal time from `t` to `t+1`, every already-active weight `k≤t` gains exactly the contraction factor at index `t+1`; the new diagonal weight is `η (t+1)`. The double-sum step uses `Finset.Icc 1 (t+1)` as the previous interval plus its top endpoint. The `k=0` weight uses the initial branch and evolves by the same contraction recurrence.

The induction proves the exact identity
`w(t,0) + (1−γ) * Σ_{k=1}^t w(t,k) = 1`.
It includes `t=0`, where the reward sum is empty and the initial weight is one, and does not require `γ<1` or any schedule assumptions. For the finite reward-mass bound, `0≤γ<1` makes the denominator positive; nonnegativity of the initial weight and the exact identity yield `Σ w≤1/(1−γ)`. Schedule bounds concern only positive indices `1≤i≤t`; no condition is imposed on the unused `η 0`.

The squared-mass theorem uses the explicit pointwise envelope premise `w(t,k)≤A` on positive active indices, together with `A≥0` and weight nonnegativity, to derive `w²≤A w` termwise. It then applies the proved total-mass bound. Thus the theorem does not assume its desired squared-sum conclusion, but it does require a separate proof of the supplied envelope `hcap`; it claims no stochastic or Freedman result.

## Fresh compile and axiom probe

The exact target source compiled to `.local/td-weight-mass-independent-audit-83079db4/TDWeightMass.olean` using `bash scripts/lean-local.sh`, with the production `TDLearningWeights` dependency checked at the exact hash above. The import-only axiom probe used the same pinned `.local/lean` executable with the temporary output directory added to `LEAN_PATH` because the wrapper resets that path for each invocation. All five exported theorems (`tdRateWeight_succ`, `tdRateWeight_sum_succ`, `tdRateWeight_mass_identity`, `tdRateWeight_sum_le_horizon`, and `tdRateWeight_sq_sum_le`) depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This is independent staged evidence, not a production integration claim.

## Production integration

The reviewed result is now integrated as `Formalization/ModelFree/TDWeightMass.lean`. Its proof and declaration bodies match the reviewed staged source; imports and status comments were adjusted. The complete project check compiled 234 modules and audited 3,148 project declarations, using only `propext`, `Classical.choice`, and `Quot.sound`. This does not change the scope or imply the final source theorem.
