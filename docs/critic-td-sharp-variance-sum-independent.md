# Independent review: fixed-terminal TD late-window variance sum

Status: exact quarantined draft independently source-reviewed, freshly
compiled, and axiom-probed. No production Lean file was changed.

## Exact hashes and scope

| Item | SHA-256 |
|---|---|
| `.local/TDSharpVarianceSumDraft.lean` | `3189c7e0f856312a820c36810b497bd5e40a73e09b9104d1f05aad32358314f8` |
| `.local/TDSharpPropagatedVarianceDraft.lean` | `f7b909fadd1c4ded5bc22e831f5aa0bd151afdd8157f4fac714454993e072132` |
| `Formalization/ModelFree/TDVarianceSum.lean` | `95b9fb946b306f81eefd07df33d877d7b5346f6e3a01902eb156d144ec813488` |
| `Formalization/Probability/FreedmanExactAssembly.lean` | `8914080eb48351a84b53d23d361430e6b9b5beff9feda4b3af483517b56a5c4c` |
| `Formalization/ModelFree/TDPropagatorRows.lean` | `da421810c1087e83b134d1781d4be3dcd430a9f6c7da5b4b4461460c3ef6884e` |
| `Formalization/ModelFree/TDLinearRowVariance.lean` | `0bffeb5bb20a5219933a04edd12ad18b9a24e03cefc4a00ebf3308d5bc5c7214` |
| Source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The staged module imports the exact propagated-variance draft above; that in
turn imports the staged late-window, square-covariance and actual fresh-square
variance results plus production propagator/row-variance APIs. The variance
sum uses the actual `tdSampleFiltration` and `predictableSecondMomentSum`
provided through the existing production filtration/conditional-variance
imports. This note covers the four declarations exported by the exact staged
target; it does not certify production integration.

## Source review

The source's random proxy `\overline W_t` is defined at
`eq:TD-variance-proxy`, lines 630–636, as
`\overline\eta\,\gamma^2` times a sum over
`floor(t/2)+1≤k≤t` of `η_k`, the actual deterministic tail propagator
`A_{k+1:t}`, and the actual old-iterate row variances. Equation
`eq:TD-square-martingale`, lines 684–694, defines centered-square increments
only for `k>t/2`. The later variance calculation, lines 2404–2444, bounds
each conditional variance and sums over precisely that late window.

In the draft, zero-based `n` corresponds to source update `k=n+1`; `range t`
contains `n=0,…,t−1`, and `t/2≤n` is exactly
`floor(t/2)+1≤k≤t`. The inactive early indices are padded with zero. The
conditional sigma-field `tdSampleFiltration T n` is the genuine used-prefix
history through `n=k−1`; the actual increment uses the fresh update at
`n+1`, its predictable old iterate `V_n`, and the fixed terminal `t`. The
explicit `t≤T` premise keeps all such draws inside the finite experiment.
The empty terminal `t=0` is handled by the empty sum and zero padding.

The exact row-variance result from the propagated-variance draft is summed
over the late window, with `4H²` factored outside and the random proxy on the
right carrying `barη * η(n+1) * γ²`, the actual tail row, and the realized
true-row variances of `V_n`. Thus it matches
`4/(1−γ)² · \overline W_t` when `H=1/(1−γ)`. Its explicit premise `hbar`
requires `η_k≤barη` only on the source late window; the source step-size
lemma supplies that instance. The all-positive-time `[0,1]` rate premise is
used for nonnegative actual propagator rows, not to posit the variance bound.

The increment-centering theorem proves conditional mean zero under the same
used-prefix filtration. Consequently the predictable conditional second
moments summed by `predictableSecondMomentSum` are the conditional variances
in the source martingale calculation. No target-shaped bound on
`\overline W_t`, deterministic cumulative-variance cap, Freedman event,
terminal union bound, or final accuracy claim is assumed or proved here.
No mismatch was found in late-window indexing, conditioning, or the random
proxy's row/variance terms.

## Independent compile and axiom evidence

The exact target compiled with pinned `.local/lean` into fresh isolated output
`.local/td-square-variance-sum-independent-3189c7e0f856/`. Its compile log is
empty. The fresh target artifact SHA-256 is
`d12f657f5b0aa37b5f9ad94d27c6a05aafbb2af91364cc3b00320ba4c47bbb68`.
The independent probe source SHA-256 is
`f5ef33e9eb6edc727727107bcb1595644f44b576d4d403423c539b1fde38af59`; the
probe artifact SHA-256 is
`416fc945cfbe16320173057914798ce3aef81aebe4458a8f76da1f30b8bbf15d`.
The probe checks all four exports:
`tdSquareLateWindowPredictableVariance`,
`tdSquareLateWindowRandomProxy`,
`tdSquareLateWindowIncrement_condExp_zero`, and
`tdSquareLateWindowPredictableVariance_le_randomProxy`. Each reports only
`propext`, `Classical.choice`, and `Quot.sound`. The exact target and probe
source contain no `sorry`, `admit`, or custom `axiom`.

The isolated search path used the exact staged propagated-variance artifact
from the prior independent audit, its staged covariance/late-window/fresh
variance/martingale/pairwise prerequisites, and existing project and pinned
package libraries. No package or production module was rebuilt or overwritten.
This is fresh evidence for the exact quarantined staged target and imports;
it does not establish downstream deterministic proxy control or production
landing.

## Production integration

The reviewed actual late-window conditional variance sum and random proxy bound are integrated as `Formalization/ModelFree/TDSharpVarianceSum.lean`. Sharp proxy control and the final TD theorem remain separate. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 278 modules and audited 3,623 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
