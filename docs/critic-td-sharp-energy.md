# Independent review: TD sharp-energy deterministic helper

## Identity and validation boundary

Reviewed exact source `.local/TDSharpEnergyDraft.lean`, SHA-256
`258e5936a583596c682b02682944aaf72da2e6ed26952dbe212c2e8b63f4d50d`.
The source chapter is
`source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The source-level target is the deterministic chronological telescope and
endpoint cap used after Lemma 4.4 (`lemma:TD-square`), especially the first
sum in `eq:overline-Wt-three-sums-TD` and the endpoint estimate immediately
following it. This draft does not formalize the stochastic energy inequality,
the square martingale, its variance, or Freedman concentration.

## Source review

The actual definition in `TDActualErrorDecomposition.lean` is
`tdErrorTransition i U = (1−ηᵢ)U + ηᵢ γ Pπ U`, and the recursive
`tdErrorPropagate start finish` applies updates `start+1,…,finish` in
chronological order. The draft's `tdErrorPropagate_comp` preserves that
orientation: it propagates `start→mid` first and then `mid→terminal`, with no
commutation premise. Consequently
`tdErrorPropagate k t (tdErrorTransition k (X (k−1))−X k)` has exactly the
source tail updates `k+1,…,t`, leaving update `k` outside the tail.

The telescope theorem is deterministic and quantified over an arbitrary
sequence `X`; this is the right algebraic generality for substituting
`X k = V_k ∘ V_k` later. Its terminal step separates the new top summand,
uses linearity of the actual transition, and cancels the propagated
`X_t` term. Its index window is `m+1,…,t`, matching the source window
`floor(t/2)+1,…,t`; the `m=t` base case is empty and the right side is zero.
No stochastic chronology, filtration, or conditional-expectation claim is
smuggled into this identity.

The order and interval helpers retain rate assumptions only on used positive
indices. The endpoint cap uses nonnegative propagation and the actual
contraction on constants, then subtracts the nonnegative terminal `X_t`.
The premise `_hH : 0 ≤ H` is unused; the proof obtains the bound through
`H²`, which is nonnegative without that premise. This is harmless but can be
removed in a future statement cleanup if statement changes are separately
approved. These helpers do not establish the source's `V_k∈[0,H]`; their
endpoint theorem explicitly requires `0≤X_n≤H²` for every `n`.

The source derivation applies Lemma 4.4 coordinatewise almost surely and
adds/subtracts `V_k∘V_k`, producing both the deterministic telescope and a
centered square fluctuation. Neither that use of Lemma 4.4 nor the conversion
to the source's full `3H²` energy cap is included here. In particular, this
file is not evidence for `eq:TD-variance-energy-bound` as a whole.

## Fresh isolated compile and axiom probe

The exact source hash above compiled successfully, exit code 0, to
`.local/td-sharp-energy-independent-review/TDSharpEnergyDraft.olean` using
`bash scripts/lean-local.sh`; the file was not modified for this check. A
separate `AxiomProbe.lean` imported that isolated output and probed all seven
exports. Each reports only `[propext, Classical.choice, Quot.sound]`:

- `tdErrorTransition_mono`
- `tdErrorPropagate_mono`
- `tdErrorPropagate_comp`
- `tdErrorPropagate_succ_start`
- `tdWeightedSquareEnergy_telescope`
- `tdErrorPropagate_le_const_of_interval`
- `tdWeightedSquareEnergy_endpoint_le`

No `sorry`, `admit`, or custom axiom is present. The probe is at
`.local/td-sharp-energy-independent-review/AxiomProbe.lean`, with output in
`.local/td-sharp-energy-independent-review/axioms.log`. This is isolated
compile/axiom evidence for the staged helper only, not production integration
or closure of the source lemma.

## Production integration

The reviewed deterministic propagator and energy-telescope helpers are now integrated as `Formalization/ModelFree/TDSharpEnergy.lean`; the centered-square variance and concentration bounds remain separate. The declaration and proof bodies match the reviewed staged source; imports or status comments were updated where required. The project-wide check compiled 250 modules and audited 3,333 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
