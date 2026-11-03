# Source review and combined verification: TD terminal caps, envelope, Freedman

**Verdict:** Source correspondence passes for the stated conservative, scalar, fixed-terminal results. One docstring overstates a sufficient condition as an equivalence. These results do not establish the main TD accuracy theorem or the source's sharper variance bound.

## Exact files and hashes

The reviewed staged inputs were:

| Staged source | SHA-256 |
|---|---|
| `.local/TDTerminalCaps.lean` | `a050cf5f01bc4797786b1b5b8a928d1dee0cb9a5c0028638bb49bfbcec7b39e0` |
| `.local/TDTerminalWeightEnvelope.lean` | `970eb83db6cabaed7c305cce7383fb2fa9b177a58cfdf05a6807e924424e04d6` |
| `.local/TDTerminalFreedman.lean` | `4e4bd225cb60b13399cb2f51e5003f968de8c8a60932b95742cc6ca1387622fb` |

The combined compile used temporary copies under `.local/td-qualified-audit/Formalization/ModelFree/`. Compared with the staged files, these copies changed only the five imports listed in `docs/landing-td-terminal-caps-freedman.md`; declaration bodies and hypotheses were preserved.

| Qualified compile copy | SHA-256 |
|---|---|
| `TDTerminalCaps.lean` | `ce674f6f6b54edd6e6fb155b0eeaed5267b71d844ee04c4d27cd1b09a52f9682` |
| `TDTerminalWeightEnvelope.lean` | `6a99d28c87c178301ea0e77c0c49c4e3705f81ddaaea245d48ff597e4284f9dd` |
| `TDTerminalFreedman.lean` | `b5efd0b9d3c2a78451502ad0227a5b710adbc0603a74b32beead15e23f77c821` |

The source chapter is `source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

## Source review findings

- The actual TD update and `Z_k` use source update times 1 through fixed terminal t, with the innovation at k using the fresh row draw at k and the previous iterate. The Lean sequence uses zero-based natural index n for source time n+1 and pads n≥t by zero. The finite-sum reindexing to `Finset.Icc 1 t` is source-correct, including t=0.
- Conditioning is on the actual used-sample prefix: at sequence index n, the increment is measurable after source sample n+1 and conditionally centered on the prefix through n. `tdSampleFiltration T` is a genuine filtration for the finite product sampling experiment. No arbitrary filtration or independence premise is introduced by the terminal Freedman theorem.
- The predictable variance is the actual raw-prefix conditional second-moment sum. The cap proof uses the actual squared-row identity and cancellation across independent next-row samples, then bounds the nonnegative propagator row by its total mass and each iterate variance by H². The resulting `γ²H³A` variance ceiling and `2γHA` increment ceiling follow from a deterministic envelope `w(t,k)≤A` and the finite positive-time rate range; they are conservative and do not assert the source's sharper early-plus-late variance estimate.
- The common envelope `A=max(T⁻², 2 log³(T)/((1−γ)T))` matches the two branches of the source TD weight lemma (chapter lines 317–325) under the actual schedule (lines 180–185), late-terminal condition, `c₁c₂≤1/8`, and the explicit large-T premise used in the appendix proof (lines 2286–2319). The early estimate genuinely uses `log²(T)≤c₁(1−γ)T`; the draft retains that premise and derives it from the stated sample budget with an explicit sufficient universal-constant relation.
- The terminal Freedman theorem is one state and one fixed terminal with failure probability δ, using the actual random predictable variance and the dyadic floor `σ²/2^K`. It does not claim the source's union over S states and T terminal times, a chosen source K, or a final accuracy theorem.

**Wording correction:** `td_final_terminal_is_late` proves `1≤c₂ log T → T/(c₂ log T)≤T`, a sufficient condition for the final terminal to be late. Its docstring says “exactly when,” which states an equivalence the theorem does not prove. Change that phrase to “a sufficient condition,” or strengthen the statement and prove the converse under the positive denominator conditions.

No other source mismatch or assumption drift was found in the stated scope. In particular, this review does not assess or certify the separate variance-energy recursion later in the chapter.

## Combined compilation and axiom probe

I followed the import-only transformation in `docs/landing-td-terminal-caps-freedman.md` to avoid the staged collision between unqualified `TDLearningWeights` and `Formalization.ModelFree.TDLearningWeights`. The qualified copies compiled in order: Caps, WeightEnvelope, Freedman. A fresh probe imported both `Formalization.ModelFree.TDTerminalFreedman` and `Formalization.ModelFree.TDTerminalWeightEnvelope` together and checked all 13 declarations in those three files. Every export reported only `propext`, `Classical.choice`, and `Quot.sound`.

The copies were placed in the project build namespace so qualified imports resolved against the ordinary project dependencies; the staged unqualified schedule module was excluded from `LEAN_PATH`. This verifies that the import-only landing transformation resolves the collision and that the three proof bodies elaborate together. It does not itself verify a source-file merge, aggregate build, or production export landing.

## Production integration

The reviewed cap, weight-envelope and fixed-terminal Freedman results are now integrated in `Formalization/ModelFree/TDTerminalCaps.lean`, `TDTerminalWeightEnvelope.lean`, and `TDTerminalFreedman.lean`. The misleading “exactly when” docstring was corrected to state the proved sufficient condition. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
