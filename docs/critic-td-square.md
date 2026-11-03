# Source review: TD squared-iterate energy

## Hash-bound scope

Reviewed staged draft `.local/TDSquareEnergyDraft.lean`, SHA-256
`366117641f23acd8884da94bcaa7b12c3d53c8e07a33c2133b7ae63602846591`,
against source Lemma `lemma:TD-square` / `eq:TD-square-energy` in
`source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The lemma statement is at lines 643–659 and its proof at lines 2325–2395.
The source inventory identifies this as Lemma 4.4. This is an independent
source and mathematical review; the exact source was also freshly compiled
and its three exports axiom-probed in an isolated directory, as recorded
below.

Reviewed dependency sources relevant to the sampling semantics:

- `Formalization/ModelFree/TDSynchronousSampling.lean`, SHA-256
  `eefb37396308721f28a33ef29b90001f3934f954d7b2c330e36cda22b60fe182`.
- `Formalization/ModelFree/TDCausality.lean`, SHA-256
  `8c8cfdf1271c2bd9736b9ec0eb8b3da7896f8f3f9c4bfd03ca33af1a6249fb29`.
- `Formalization/ModelFree/TDConditionalMoments.lean`, SHA-256
  `82c1ad9cf6e8ae6f12173255af3ecbc29fd3c179334922073b80c010cfd45f7b`.
- `Formalization/ModelFree/TDIterateBounds.lean`, SHA-256
  `76f62a155ac303d82bea3395487e9c54cb729eceba3ba84042414bc499bfb637`.

## Source statement and assumption correspondence

The Lean target `tdSquaredIterateEnergy` is the coordinatewise form of the
source vector inequality. Its left side is
`η_k(1−η_k)γ² Var_{Pπ}(V_{k−1})(s)`. Expanding the source operator
`I−η_k(I−γPπ)` at coordinate `s` gives exactly
`(1−η_k)V_{k−1}(s)^2 + η_k γ E_{Pπ(s)}[V_{k−1}^2]`, which is the first two
terms on the Lean right side. The remaining terms are the actual conditional
expectation of `V_k(s)^2` and `2η_k/(1−γ)`. The signs and coefficient placement
match `eq:TD-square-energy`.

The source proof uses `η_k∈[0,1]`, `0≤γ<1`, `0≤rπ≤1`, and
`0≤V_{k−1}≤H=1/(1−γ)`. The draft carries the source initial bound
`0≤V₀≤H` and rate bounds only at positive indices through `T`; it requires
`1≤k≤T`. The rate wrapper changes the unused `η(0)` to zero only while
invoking the existing interval invariant, then proves the iterate is
unchanged because the recurrence starts at index one. The target theorem
itself imposes no condition on `η(0)`. This is a sound finite-horizon
specialization of the source's every-`k≥1` statement: for each source time k,
choose any finite T≥k. The `DiscountedMDP` and stationary-policy structure
provides finite state/action sets, probability rows, `0≤γ<1`, and rewards in
`[0,1]`; `policyReward` is the policy-average reward and `policyTransition`
is the policy-induced row `Pπ`. The proof does not strengthen these with a
sample-size, concentration, or global schedule premise.

## Sampling history and three declarations

The actual experiment stores independent draws for every `(state,time)` at
times `0,…,T`; time zero is unused by the TD recurrence. `tdPastSigma T t`
records all used state-coordinate draws at source times `1,…,t`. The helper
`tdFresh_predictable_square_condExp` conditions on this complete past through
time t and evaluates the actual fresh coordinate `(s,t+1)`. Its conditional
law is the true row `Pπ(s)`, derived from the product sampling law and
independence, not supplied as an assumption. In the main result t is `k−1`,
so the conditioning includes exactly source times 1 through k−1, and the
fresh synchronous update uses time k. The finite experiment's extension
outside its horizon is irrelevant because k≤T.

The declarations were checked individually:

1. `tdFresh_predictable_square_condExp` extends the existing fresh conditional
   sum identity to the square of an arbitrary past-measurable coordinate
   function. The finite sum of fresh-coordinate indicators is the actual
   squared predictable value at the sampled coordinate, and the conditional
   expectation becomes the row expectation of that square.
2. `tdIterate_bounds_of_positive_rates` is a technical form of the existing
   pathwise interval theorem. Its replacement of `η(0)` is proved
   recurrence-preserving and introduces no source-relevant constraint.
3. `tdSquaredIterateEnergy` first expands the actual update square using
   `((1−η)x+ηy)^2=(1−η)x²+ηy²−η(1−η)(y−x)^2`. Fresh-coordinate conditional
   formulas identify all three conditional squares under `Pπ(s)`. The
   target-square estimate follows by expanding `(rπ+γV)^2`, using
   `rπ≤1`, `0≤V≤H`, `γ²≤γ`, and `1+2γH≤2H`. The residual-square lower
   estimate uses variance invariance under constant shifts, affine scaling
   `Var(rπ+γV)=γ²Var(V)`, and `Var(f)≤E[(f−c)^2]`. Combining the estimates
   with nonnegative `η_k` and `η_k(1−η_k)` yields precisely the source
   inequality.

The source's derivation conditions on the history through iteration k−1,
then averages the row-wise synchronous draw at k; the formalization uses that
same filtration and indexing. It does not accidentally condition on the
fresh sample, use a sample-dependent row, or assume independence of the
iterate from itself. The iterate is past-measurable and only the fresh draw
is averaged.

## Verdict and validation boundary

The target inequality and its assumptions/indexing are source-faithful. The
two helper declarations support the source proof without changing its claim.
No source mismatch or unmodeled stochastic independence premise was found.
Production integration and all downstream weighted-variance/Freedman
consequences are outside this draft and this review.

## Independent fresh compile and axiom probe

The exact source hash above was rechecked immediately before compilation. It
was compiled to a new project-owned isolated directory with:

```sh
bash scripts/lean-local.sh -o \
  .local/td-square-independent-audit-36611764/TDSquareEnergyDraft.olean \
  .local/TDSquareEnergyDraft.lean
```

The command exited successfully without diagnostics. The fresh artifact
`.local/td-square-independent-audit-36611764/TDSquareEnergyDraft.olean` has
SHA-256 `c5ed1f04a36f88be40a4504bc21f7ca39442153bd5b05deba445c5513e2fff4a`.
No production module or dependency artifact was written.

An import-only probe at
`.local/td-square-independent-audit-36611764/ImportAudit.lean` imported that
artifact and ran `#print axioms` for all three declarations. The probe
completed successfully; each declaration reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The probe source hash is
`6c0731e0277491c9432d632abed889680fdf7478ea5a9d6c3d5669f2a5292d18` and
the output hash is
`47c408aa5606263485667f9efc6431444560d3f0266293594b567a1ad23b526d`.

The repository wrapper resets `LEAN_PATH`, so the first attempt to run the
import probe through that wrapper could not see the isolated artifact. The
successful probe used `.local/lean` directly with the isolated output,
project build, and pinned package directories on `LEAN_PATH`. This was only a
probe-path correction; it did not modify the source or built artifact. The
compiler slot is released. This remains staged-source evidence rather than a
production integration check.

## Production integration

The reviewed energy inequality is now integrated as `Formalization/ModelFree/TDSquareEnergy.lean`. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
