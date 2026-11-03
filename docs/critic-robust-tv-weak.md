# Robust-TV weak duality: source review

Source: arXiv:2610.41903v1, robust-RL chapter, the TV branch of
`lemma:dual-form`, lines 291–324, and the event-supremum total-variation
definition in the introduction. Independent AI review compared the source,
actual finite distributions, TV normalization, clipping, and weak-duality
statement. The 332-module project check passed, and its transitive audit
checked 4,099 declarations using only the standard Lean axioms. A separate
clean-copy rebuild with empty project artifacts and pinned dependency cache
passed the same 332 modules and axiom audit with matching Lean source hashes.

`StatisticalRL.RobustRL.tv_dualSup_le_primalInf` uses actual finite probability
rows, the source event-TV ball of radius σ, nonnegative V, and α in the source
interval `[min V,max V]`. It proves only that the supremum of the source dual
objective is at most the infimum of the feasible expectations. The finite
event-TV maximum is separately proved equal to half the L1 distance, including
zero-probability atoms and without support assumptions. The source clip is the
pointwise minimum `min (V s) α`, equal to its printed conditional definition.

The proof centers the clipped value vector and bounds the expectation change
by TV times its range. It keeps the actual clipped minimum in the objective;
the nominal row supplies a feasible candidate. Both the probability carrier and
expectation use the project's actual finite-distribution definitions.

The reverse inequality, primal optimizer, dual maximizer attainment, and the
χ² branch are **not** proved here. Consequently this work does not complete
or count the source strong-duality lemma.

| Module under `Formalization/RobustRL/` | SHA-256 |
|---|---|
| `TVCore` | `d752a89baac4a78952937ca041d8f538ab9725f2d15d91c9cb3bb9c915d15ead` |
| `TVWeakBound` | `a0f61aea545e4717469de41dabb037e1d8875be6e4dd11f59aad699cfc84223d` |
| `TVWeakDuality` | `817eee382b81008376393d3602f8c09e2c3fd826448ba58671c7def9b15882ce` |

The production copies preserve the compiled and independently reviewed
mathematical declarations, with qualified imports and documentation updates.
The working-project evidence is recorded locally in
`verification/20261103T140943408415Z/`.
