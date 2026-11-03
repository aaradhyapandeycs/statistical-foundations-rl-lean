# Independent review: TD sharp energy/proxy draft

Status: independent source review and fresh isolated compile completed. The
review concerns only `.local/TDSharpEnergyProxyDraft.lean`; it does not certify
production integration or the later Freedman/rate argument.

## Hash-bound scope

| Item | SHA-256 |
|---|---|
| Reviewed draft `.local/TDSharpEnergyProxyDraft.lean` | `e9edac9419a53eacc544750cbb0aa08e75c0c6a1738eaa50a36799b431f13158` |
| Source `source/upstream/tex/chapters/generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |
| `.local/TDSharpVarianceSumDraft.lean` | `3189c7e0f856312a820c36810b497bd5e40a73e09b9104d1f05aad32358314f8` |
| `.local/TDSharpPropagatedVarianceDraft.lean` | `f7b909fadd1c4ded5bc22e831f5aa0bd151afdd8157f4fac714454993e072132` |
| `.local/TDSharpLateWindowDraft.lean` | `e353b996e0b2e44920863d0f01dffbcfb04480a88360a35223865f6a63850df5` |
| `Formalization/ModelFree/TDSquareEnergy.lean` | `8b846ebc5738515e18a9c5e6cff8a043ae9adf84ec6b0baa804fa9675c40a3be` |
| `Formalization/ModelFree/TDSharpEnergy.lean` | `4e32c66f2b5a55a8068fab511026fa7791fd63800270ad9d61d2d7a56cfc494c` |
| `Formalization/ModelFree/TDPropagatorRows.lean` | `da421810c1087e83b134d1781d4be3dcd430a9f6c7da5b4b4461460c3ef6884e` |
| `Formalization/ModelFree/TDWeightMass.lean` | `83079db47744cf71da4166252576af2f916ec7a4ee87a9ced95174f3e80871db` |
| Fresh isolated probe `.local/td-energy-proxy-critic-e9edac94/AxiomProbe.lean` | `6a9a2dc8f1b4a2bd2ab897bf2575b0187b593442eccde2ece5cc5adf4dd91dff` |

The build wrote `.local/td-energy-proxy-critic-e9edac94/out/TDSharpEnergyProxyDraft.olean` and did not overwrite the source or any production module.

## Source correspondence

The target is `eq:TD-variance-energy-bound` (source lines 704–710), built
from `lemma:TD-square` and the three-sum decomposition in
`eq:overline-Wt-three-sums-TD` (lines 643–680). The input to the random term
is the actual centered square
`V_k∘V_k − E_{k−1}[V_k∘V_k]`; the actual deterministic tail propagator acts
after update `k`. The staged definitions use that same square innovation and
tail row. The `tdSharpEnergyWindow` is
`Icc (t / 2 + 1) t`, exactly the integer form of `t/2 < k ≤ t`, while the
zero-padded source sum maps `n=k−1` without changing the update count.

The one-step conditional energy bound is applied to the actual sampling law.
`henergyAt` supplies an almost-everywhere fact for each update and coordinate;
`ae_all_iff` assembles one common event over the countable update index and
finite state space before the operator inequalities and finite sums are used.
Outside the active late window the implication is vacuous, so the event
construction does not add a stochastic or target-shaped premise.

The resulting random quantity remains sample-dependent: the theorem bounds
the actual `tdSquareLateWindowRandomProxy` by the constant `3H²` plus the
actual late-window centered-square sum. It does not replace that sum by a
pre-assumed bound. The telescope uses the actual arbitrary-sequence energy
identity; the endpoint and constant-vector terms use actual propagator rows
and the source learning-rate mass bound.

The theorem's direct assumptions are `t≤T`, `V₀∈[0,H]`, positive-time rates
in `[0,1]`, `0≤barη≤1/2`, and `η_k≤barη` on the active late window. This
matches the displayed source reduction once the schedule lemma supplies
`barη`; the source's sample-size and time-threshold conditions are not proved
or hidden in this helper and remain a consumer obligation. No premise asserts
the desired proxy inequality or its conclusion.

## Fresh compile and axiom probe

Fresh compile command used the pinned `.local/lean` (`Lean 4.27.0-rc1`) and a
new output directory, with the existing project/Mathlib dependency outputs and
the listed staged import outputs on `LEAN_PATH`:

```text
.local/lean -o .local/td-energy-proxy-critic-e9edac94/out/TDSharpEnergyProxyDraft.olean .local/TDSharpEnergyProxyDraft.lean
```

Compilation succeeded. It emitted only linter warnings (unused `hj`, `ht`,
`hη`, and an unused simp argument); there were no proof errors. The separate
probe was compiled with the same import path and printed axioms for:

- `tdSharpSquarePotential`
- `tdSharpSquarePotential_telescope`
- `tdSharpSquarePotential_endpoint_le`
- `tdSharpEnergyProxy_remainder_le`
- `tdSquareLateWindowRandomProxy_le_energy`

Each reports only `propext`, `Classical.choice`, and `Quot.sound`. The probe
output is `.local/td-energy-proxy-critic-e9edac94/axioms.log`.

The draft is not production-integrated. This audit does not establish a
Freedman event, deterministic proxy cap, final TD rate, or whole-source
coverage. The older builder note's initial draft hash is stale; this review is
bound to the current requested SHA above.

## Production integration

The reviewed late-window TD energy/proxy inequality is integrated as `Formalization/ModelFree/TDSharpEnergyProxy.lean`. Its positive-time rate premise is global; source-schedule instantiation and sharp concentration remain separate. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 283 modules and audited 3,694 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
