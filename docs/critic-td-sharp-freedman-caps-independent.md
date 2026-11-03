# Independent review: TD square Freedman caps

## Exact reviewed artifacts

The review is bound to the unchanged staged source
`.local/TDSharpFreedmanCapsDraft.lean`, SHA-256
`4e2f4cac3cefeabd0e1ef053f75904f91fe72dbeaed5bc5b5f51f14e7c6e221a`, and
the monograph chapter
`source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
All staged and production dependencies listed below were also rehashed and
matched their handoff values at review time:

| Dependency | SHA-256 |
|---|---|
| `.local/TDSharpVarianceSumDraft.lean` | `3189c7e0f856312a820c36810b497bd5e40a73e09b9104d1f05aad32358314f8` |
| `.local/TDSharpPropagatedVarianceDraft.lean` | `f7b909fadd1c4ded5bc22e831f5aa0bd151afdd8157f4fac714454993e072132` |
| `.local/TDSharpLateWindowDraft.lean` | `e353b996e0b2e44920863d0f01dffbcfb04480a88360a35223865f6a63850df5` |
| `.local/TDSharpSquareCovarianceDraft.lean` | `0391af8b931384927f28fb9abcff12ba363deb245e01f099f521bcaf2e93db54` |
| `.local/TDSharpFreshVarianceBridgeDraft.lean` | `34686d029e51a1739ae0891095e4212208a56ac5693882a65afc401583d308cc` |
| `.local/TDVariancePairwiseDraft.lean` | `eddac49017762311a11b0f86590414c8d21ed6279cff2d7b0df2b792c5bea022` |
| `.local/TDSharpVarianceDraft.lean` | `c02b90230640c79603e38a7f8b7a0211537ab341c3b27f289b06099292e0845a` |
| `.local/TDSharpMartingaleDraft.lean` | `eeeee6f405bcc819cb4d609dc9fb83bc27fbc4e15612506502a27ab535961c68` |
| `.local/TDSharpEnergyDraft.lean` | `258e5936a583596c682b02682944aaf72da2e6ed26952dbe212c2e8b63f4d50d` |
| `Formalization/ModelFree/TDTerminalCaps.lean` | `ce674f6f6b54edd6e6fb155b0eeaed5267b71d844ee04c4d27cd1b09a52f9682` |
| `Formalization/ModelFree/TDPropagatorRows.lean` | `da421810c1087e83b134d1781d4be3dcd430a9f6c7da5b4b4461460c3ef6884e` |
| `Formalization/ModelFree/TDSquareEnergy.lean` | `8b846ebc5738515e18a9c5e6cff8a043ae9adf84ec6b0baa804fa9675c40a3be` |

## Source-level findings

The late-window increment cap matches the source indexing. Draft index `n`
maps to source update `k=n+1`; its active predicate `t/2 ≤ n < t` is exactly
`floor(t/2)+1 ≤ k ≤ t`. The propagated centered-square bound is
`2 η_k γ H²`, and the tail propagator row is nonnegative with mass at most
one. The supplied active-window cap `η_k≤barη` therefore yields
`2 barη H² = 2 barη/(1−γ)²`, matching the source bound for
`\widetilde Z_k`. Early and post-terminal increments are zero by definition.

The pointwise proxy is the source `\overline W_t` with the same late indices:
the draft's `n` uses the old iterate `V_n=V_{k-1}`, its terminal row is the
actual propagator product, and the variance is under the true policy
transition row. Each row variance is bounded by `H²`; the nonnegative row
weights sum to the actual propagator row mass. The rate-weight row-mass
identity and `\sum_{k=1}^t tdRateWeight_k≤H` then give
`barη γ H³≤barη H³=barη/(1−γ)³`. This is the source's stated coarse
deterministic proxy bound, not the later sharp `16 barη H²` estimate.

The proofs use actual synchronous-sampling conditional expectations and true
transition-policy rows. There is no target-shaped premise for either cap.
The increment proof requires only an explicit late-window upper bound on the
actual learning rates plus the usual `[0,1]` range for rates used in the TD
iterate and propagator lemmas. The proxy theorem's `ht : t≤T` binder is unused
(compiler warning); its rate hypothesis is stated globally for every
positive index rather than only indices through `T`. That is stronger than
needed for this finite-horizon statement and is a statement-tightening
opportunity, not a proof of the source schedule itself. Consumers must still
derive the active-window `barη` bound from the source step-size schedule.

This draft proves only deterministic helper caps. It does not prove a
Freedman event, the source's random sharp variance estimate, a sample-size
consequence, or production integration.

## Fresh isolated compile and axiom probe

Compiled the exact source hash into a new isolated output directory using
the pinned Lean 4.27.0-rc1 binary and the listed staged dependency outputs.
The command succeeded; the only diagnostic was the unused `ht` warning at
line 292. The output was
`.local/td-freedman-caps-independent-20261103/out/TDSharpFreedmanCapsDraft.olean`,
SHA-256 `edacc295e3bfd5a04846448975ce70f94d00a6938e57bd2902d7be128a9e65fc`.
The captured compile log is
`.local/td-freedman-caps-independent-20261103/compile.log`.

A separate fresh import probe at
`.local/td-freedman-caps-independent-20261103/TDSharpFreedmanCapsAxiomProbe.lean`,
SHA-256 `d3c2c13063d0f0bcc0bb7e6f6325cf72ca226d6e71f511cb9abd1cf44a0ac9fa`,
probed all five exports. Each has exactly the transitive axioms
`[propext, Classical.choice, Quot.sound]`. Full output is in
`.local/td-freedman-caps-independent-20261103/axioms.log`. The reviewed source
contains no `sorry`, `admit`, or custom `axiom` declaration.

The compilation and probe establish proof evidence for these helper exports
at the bound hashes only. This independent review does not certify any later
consumer or integrated theorem.

## Production integration

The reviewed late-window increment and coarse variance caps are integrated as `Formalization/ModelFree/TDSharpFreedmanCaps.lean`. Sharp concentration and the final TD theorem remain separate. The proof and declaration bodies match the reviewed staged sources; imports and status comments were updated. The full project check compiled 288 modules and audited 3,756 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
