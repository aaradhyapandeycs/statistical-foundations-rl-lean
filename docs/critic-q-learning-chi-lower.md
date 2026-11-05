# Independent review: concrete χ² lower witness

## Exact files reviewed

| File | SHA-256 |
|---|---|
| `QLearningChiLowerDraft.lean` (private staged draft, not shipped) | `7c3c610082d13523ac7f34f89dded65e96ba5e9eeb630ae200d7cea5aa35e4e8` |
| `QLearningChiUpperDraft.lean` (private staged draft, not shipped) | `a1a11cbd1debd8e26bd3bcedd0f13339cd0ae8858d7ab3f6823f23e33d7e2280` |
| `QLearningRobustComparatorDraft.lean` (private staged draft, not shipped) | `f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70` |

These hashes were checked immediately before an independent fresh build. The audit output is isolated in a local audit directory (not shipped); no production Lean file was modified.

## Source and mathematical review

The target is the lower inequality in source `lemma:Q-comparison-facts` (i), `eq:Q-comparison-support`, at `source/upstream/tex/chapters/generative_model_model_free.tex` lines 1350–1359, with its witness proof at lines 2610–2635. The pinned chapter SHA is `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

The draft constructs the actual finite row
`q(x) = p(x) * (1 + c * (v(x) - E_p[v]))`.
It derives centered expectation zero from the actual finite distribution, obtains the centered absolute bound from pairwise span, and uses `c ≥ 0` and `cH ≤ 1` for coordinate nonnegativity. Normalization follows from the centering identity. At nominal zero atoms the new mass is definitionally zero. The χ² calculation cancels the nominal mass only on the positive-support finset; the variance identity restores the omitted zero-mass terms. The expectation increment is exactly `c * Var_p(v)`.

The final support-function proof first establishes boundedness using the previously proved upper bound and feasibility of the nominal row. At `ρ = 0` it uses the nominal row, with no variance division. When `sqrt(ρ) H ≤ sqrt(Var)`, `ρ > 0` and `H > 0` imply positive standard deviation, so the choice `c = sqrt(ρ)/sqrt(Var)` is defined, satisfies the nonnegativity constraint, has exact χ² cost `ρ`, and gains `sqrt(ρ Var)`. In the other branch, the nominal row gives zero gain and the desired lower radius is nonpositive. Equality at the branch threshold is assigned to the tilt branch; variance zero is handled in the nominal branch.

No target-shaped optimizer or nonzero-variance premise is smuggled in. The generic tilt and its exact identities are established before the parameter choice. This matches the constructive witness argument in the source.

## Scope differences and limits

- The final theorem `qRobustExpectations_sSup_sub_ge_of_centered_span` assumes `H > 0`, `ρ ≥ 0`, and the centered-span form `|v(x) - E_p[v]| ≤ H`. The printed source assumes `ρ > 0` and max-minus-min span at most `1/(1−γ)`. The draft's radius extension to zero is valid; applying it to the printed statement requires instantiating `H = 1/(1−γ)` and deriving the centered bound from the source's finite max-minus-min premise. The pairwise-span helper supports that bridge, but this file does not yet package the entire source-shaped max/min interface.
- The file proves the lower bound for the supremum side only. The source also states the corresponding infimum bound and the shared two-sided statement; derive those separately (for example, by applying the result to `−v`) before claiming the whole source lemma.
- The source's upper support-function inequality is a dependency in `QLearningChiUpperDraft`; this note does not re-audit that proof.
- This result is only a row-level support-function bound. It does not prove the source's robust-Q stability statement (ii), the later Q-learning comparison argument, or a sample-complexity result.

## Fresh compilation and axiom probe

The exact-hash dependency closure compiled successfully into the isolated audit directory, bottom-up: Comparator, ChiUpper, ChiLower. Commands used the existing project dependencies and did not request any dependency rebuild:

> *Historical command, omitted from the public copy.* It ran the pinned Lean compiler on a private staged source and wrote to an isolated local output directory; neither path is shipped, so it cannot be rerun from this checkout. The recorded result is unchanged.

A separate probe imported the isolated lower output and ran `#print axioms` on all nine declarations in the lower draft, including the simp theorem for `qChiTilt_prob`. Every declaration reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The probe is `Probe.lean` (in an isolated local audit directory, not shipped).

This is independent evidence for this staged source hash only. The draft remains quarantined and is not a production export.

## Production integration

The reviewed lower-supremum witness result is now integrated as `Formalization/ModelFree/QLearningChiLower.lean`. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
