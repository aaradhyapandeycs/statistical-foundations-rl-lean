# Independent critic: TD square proxy positivity and scalar absorption

Status: **source review and fresh isolated build/probe completed** for the two declarations in the exact local draft listed below. This does not establish the second-Freedman event or the full TD variance-proxy lemma.

## Hash-bound inputs

| Artifact | SHA-256 |
|---|---|
| `.local/TDSharpSelfBoundScalarDraft.lean` | `2a0d937aec7ef5b7788e33cd311e6d5cc0d3f96da622f67f00536eed9bc15bf7` |
| Imported `.local/TDSharpFreedmanCapsDraft.lean` | `4e2f4cac3cefeabd0e1ef053f75904f91fe72dbeaed5bc5b5f51f14e7c6e221a` |
| Imported `.local/TDSharpVarianceSumDraft.lean` | `3189c7e0f856312a820c36810b497bd5e40a73e09b9104d1f05aad32358314f8` |
| Source `source/upstream/tex/chapters/generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |
| Probe `.local/td-self-bound-scalar-independent-20261103/AxiomProbe.lean` | `6a7a22f5ce4e32cc4f230a82763f4941794ad1f2a0f440472f7b05ea8b46c2d0` |

The source target is `lemma:TD-variance-proxy-bound`, especially the second Freedman/self-bound step at lines 2398–2489.

## Fresh compile and axiom probe

The exact draft was independently compiled to
`.local/td-self-bound-scalar-independent-critic-20261103/out/` using the
repository `.local/lean` binary and the exact staged dependency outputs before
the project and pinned Mathlib outputs. The first invocation did not resolve
the transitive `TDSharpVarianceSumDraft` import because its isolated output
directory was missing from `LEAN_PATH`; after adding the already built exact
staged dependency directories, the focused compile succeeded. No dependency
was rebuilt. Lean emitted one warning: `hH0` is unused.

Fresh output `.olean` SHA-256:
`571315381c51b019e5f98a27fb2fa2e5c6b7fbe3d4fa69d256d9f9bc10a139f7`.

The probe imported the newly compiled module. Both
`tdSquareLateWindowRandomProxy_nonneg` and
`tdSquareProxy_scalar_absorption` have exactly the transitive axioms
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, custom axiom,
or tactic hole occurs in the source file.

## Source-level findings

* **Actual late-window proxy:** The positivity proof unfolds the actual finite sum over `n∈range t`, keeps the active condition `t/2≤n`, and uses the existing chronological tail-row mass lemma and true policy-row variance nonnegativity. The coefficient is nonnegative from `barη≥0`, the relevant `η_(n+1)≥0`, and `γ²≥0`. It does not assume a proxy upper bound or the conclusion of the energy theorem. It is a positivity helper, not a Freedman or variance assertion.
* **Finite-horizon premise mismatch:** In the draft, `hη` requires `0≤η_i≤1` for every positive natural `i`; it has no `i≤T` hypothesis, and the theorem has no `t≤T` premise. The proof only uses `i=n+1≤t`. In the source argument, terminal times are within the run horizon and the rate schedule is guaranteed only on indices through `T`. Thus the helper is valid under its stated stronger global schedule assumption, but the source assumptions do not directly discharge it as written. Before consumption, narrow `hη` to `i≤T` and add/use `t≤T` (or prove a source-authorized extension of the finite schedule). This is the only statement-level scope mismatch found in the proxy helper.
* **Scalar assumptions and constant:** The abstraction maps `a=barη`, `H=1/(1−γ)`, and `L=log(4STK/δ)`. Its premises are `0≤a≤1/2`, `H≥0`, `L≥0`, `W≥0`, `aL≤1/64`, and the exact intermediate self-bound
  `W≤a/(1−a)(3H²+sqrt(32H²(W+aH²)L)+(8/3)aH²L)`.
  These match the scalar inputs documented in the source proof. The proof first uses `a/(1−a)≤2a`, absorbs the square-root term using `aL≤1/64`, bounds the linear term by `(1/12)aH²`, and compares the remaining root against `W/2+(3/2)aH²`; rearrangement yields exactly `W≤16aH²`. It does not assume that conclusion. The `H≥0` premise is harmless but unused by Lean; only `H²` appears in the scalar inequalities. `W≥0` is necessary for the nonnegative-side square-root comparison and must come from the actual proxy positivity result at consumption.
* **Integration boundary:** This draft does not derive the intermediate self-bound from the energy inequality and Freedman event, does not establish the schedule premise `barη L≤1/64` from the sample-size assumptions, and does not perform the state/time union bounds. Its pure scalar theorem is source-faithful once those inputs are separately proved and the finite-horizon proxy premise is repaired.

No production Lean file or coverage ledger was changed.

## Production integration

The reviewed proxy nonnegativity and scalar absorption helper is integrated as `Formalization/ModelFree/TDSharpSelfBoundScalar.lean`. Its global rate assumption remains explicit; the finite extension below is a separate consumer ingredient. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 293 modules and audited 3,811 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
