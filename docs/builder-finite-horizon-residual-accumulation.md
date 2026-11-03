# Deterministic finite suffix-residual accumulation

Stable staged `.local/FiniteHorizonResidualAccumulation.lean`, SHA-256 `95aea77cc0f68596895543a453c1073fa1e8cd2e0d76275d708ca02f23536f17`.

Direct staged import: `FiniteHorizonPolicyPerturbation.lean` SHA `546b25ca13cc72ed182cc55999a85a4655e39e6636948bfd257fe144f06ed4ea`, plus pinned Mathlib ordered finite-list sum API. The actual finite sampling/trajectory dependencies are recorded in the perturbation handoff.

## Nine completed exports

`policyResidualCharges` lists one actual row-residual supremum norm per stage in chronological order. At paired stage(E,F), its continuation is the comparison-model **actual policy suffix trajectory value**, and its row residual is (P_F−P_E) applied to that value. The policy shifts by one stage in the recursive tail. This is not a list of assumed error estimates or a definition of the target whole-episode value error. `policyResidualCharges_length` proves its length equals the paired episode length, and `policyResidualCharges_sum_nonneg` proves its sum nonnegative.

`propagatedPolicyResidual_abs_le_charges` derives the pointwise absolute propagated-residual bound by induction, using only triangle inequality and nonamplification of a uniform bound by actual policy/true-transition probability expectations. `propagatedPolicyResidual_norm_le_charges` takes the finite state supremum norm. Neither theorem requires reward equality because they bound the explicitly defined residual propagation itself.

`trajectoryValue_difference_norm_le_charges` then consumes the proved exact trajectory perturbation identity to obtain actual comparison-minus-true policy-value norm≤sum of those residual charges, under the known-reward equality for each paired stage. Same policy and true kernels are used throughout; no inverse operator, discount or statistical assumption occurs.

`policyResidualCharges_sum_le_uniform` proves that if every actual charge is≤r, their sum is≤episode_length·r. The premise is an explicit intermediate row-residual bound, not the desired policy-value conclusion. `empiricalTrajectoryValue_norm_le_charges` applies the unconditional accumulation to the actual frequency-model/original environment pair built from identical sample data. Known rewards and equal horizon are already discharged by construction in the imported actual identity. `empiricalTrajectoryValue_norm_le_uniform` concludes actual same-policy evaluation error≤H·r under the corresponding uniform charge bound.

## Algorithmic and source scope

The policy is an arbitrary nonstationary randomized Markov policy; after any data outcome it may be instantiated with the realized fitted policy. The proof makes no independence claim about that policy or its future decisions. The actual comparison-model continuation for such a policy can depend on current/past data; no fixed-policy concentration theorem is applied to it here.

This completes the bounded **deterministic residual accumulation** option in the finite-horizon frontier. It does not prove an H⁴ actual-algorithm sample theorem, and it does not certify the source-sharp H³ per-tuple theorem. If a suitable common event yields a uniform residual scale on the order of H/sqrt(N), this additive H factor is the deterministic mechanism behind a coarse H⁴ sample dependence; the needed event, planner-optimality equivalences and simultaneous confidence are not asserted in this file.

The separately staged `FiniteHorizonContinuationBernstein` controls canonical empirical-optimal next-stage values one row at a time. To combine it rigorously, still prove the all-stage/state/action event, relate actual selected empirical-optimal suffix policy values to those canonical values at every suffix, and provide any additional fixed true-optimal-policy event/performance decomposition. Do not assume independence of the fitted policy, substitute a canonical value for an arbitrary policy's continuation without equality, or intersect two separate1−δ events while retaining1−δ confidence.

Empty horizon has empty charge list and zero error. Terminal continuation contributes zero residual through the imported `policyRowResidual_zero`, although the conservative length factor H does not remove that final zero charge. r is not separately assumed nonnegative: for a nonempty charge list its uniform upper-bound premise enforces compatibility with nonnegative charges, and at empty horizon H·r=0 for every r. All finite carriers, stage-varying kernels, known [0,1] rewards and the source policy time shifts are preserved.

## Validation

Fresh exact perturbation source compiled into isolated `.local/finite-horizon-build`, then the new source was checked. A final exact-source-copy `.local/finite-horizon-build/ResidualAccumulationAudit.lean` appended all9 export axiom probes; it compiled exit0 without diagnostics. Every export reported only `propext`, `Classical.choice`, `Quot.sound`; no placeholder or custom axiom occurs. Dependency artifacts were preserved, and the compiler slot was released immediately after completion.

Independent source/semantic review, qualified production landing and actual export/project validation remain separate gates. The full referred finite-horizon proof and sharp sample theorem remain outside this bounded handoff.
