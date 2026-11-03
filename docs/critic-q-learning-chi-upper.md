# Independent source review: support-aware χ² upper deviation

## Reviewed artifact and scope

Reviewed `.local/QLearningChiUpperDraft.lean`, SHA-256
`a1a11cbd1debd8e26bd3bcedd0f13339cd0ae8858d7ab3f6823f23e33d7e2280`.
The associated builder note is
`docs/builder-q-learning-chi-upper-draft.md`. This review checks the stated
finite-distribution mathematics against the pinned monograph source. It also
includes the independent staged compile and axiom probe recorded below. It
does not certify a production-module export.

The authoritative source is arXiv:2610.41903v1. The relevant chapter source,
`source/upstream/tex/chapters/generative_model_model_free.tex`, has SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
Lemma `lemma:Q-comparison-facts`, part (i), states the support-function
upper bound in `eq:Q-comparison-support` at lines 1350–1359; its proof's
upper-bound argument is at lines 2591–2605. The finite χ² definition is
`eq:defn-chi2` in `source/upstream/tex/chapters/intro.tex`, SHA-256
`6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a`,
lines 232–235.

## Mathematical correspondence

The source uncertainty set `eq:Q-comparison-ball` requires both
`χ²(q‖p) ≤ ρ` and `q(x)=0` whenever `p(x)=0`. The staged comparator defines
`qChiSquared` as the finite sum of `(q.prob x - p.prob x)^2 / p.prob x` over
exactly the positive-`p` coordinates, and stores the zero-support condition
separately in `qChiBall`. This is the correct discrete expansion of
`∫(dq/dp−1)^2 dp`; no mass is admitted off nominal support and no totalized
division at a zero denominator is used. That dependency is
`.local/QLearningRobustComparatorDraft.lean`, SHA-256
`f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70`.

The five declarations in the reviewed file form a faithful proof chain for
only the source upper direction:

1. `qChi_centered_support_sum` restricts the centered signed difference to
   positive nominal atoms. Normalization cancels the centering constant, and
   the explicit support premise makes every omitted zero-`p` summand vanish.
   This matches the first equality and its explanation in the appendix.
2. `qChi_expectation_sub_sq_le` applies finite Cauchy–Schwarz on that same
   support, with factors `(q−p)^2/p` and `p(V−E_p V)^2`. Its second factor is
   the actual centered-square variance; its first factor is exactly the
   staged χ² definition. The positive-support filter justifies the only
   division used.
3. `qChi_abs_expectation_sub_le` takes square roots using nonnegativity of
   both χ² and variance.
4. `qChiBall_abs_expectation_sub_le` substitutes the feasible-row divergence
   bound and monotonicity of square root.
5. `qRobustExpectations_sSup_sub_le` applies that pointwise inequality to
   every value in the actual robust expectation image and bounds its
   supremum. Nonemptiness is supplied by the nominal row for `ρ≥0`. To use
   `csSup_le`, the Lean proof also needs boundedness above of this expectation
   image; mathematically, every probability-weighted expectation of a finite
   vector lies between its minimum and maximum. This review checks that
   obligation at the mathematical level, not the Lean elaboration mechanism
   or the proof dependency that discharges it.

The resulting conclusion is exactly
`sSup {q.expectation v | q ∈ Uρ(p)} − p.expectation v ≤
sqrt (ρ * Var_p(v))`, the upper inequality in `eq:Q-comparison-support`.
The draft proves the stronger pointwise absolute-deviation bound before
taking the supremum. This proof does not need the source's value-span premise;
omitting that premise is valid for this upper direction because Cauchy–Schwarz
holds for every real-valued finite vector. It also handles `ρ=0` and zero
variance, whereas the source lemma assumes `ρ>0`; these are sound extensions,
not a shift weakening the source claim.

## Verdict and limits

Source correspondence is sound for the upper-deviation result and its stated
support convention. No mismatch or extra mathematical premise was found in
the displayed chain. This does not review the Lean boundedness proof
dependency, certify compilation/axioms, or establish the source lemma as a whole. In
particular, this draft contains no lower-deviation witness, no infimum bound,
no stability statement, and no robust fixed-point or policy conclusion. The
source's separate lower-bound construction still depends on the span bound and
is not discharged here.

## Independent staged compile and axiom probe

After rechecking the source SHA above, I compiled the exact target source to a
new isolated directory, with the staged comparator dependency supplied from
its already audited isolated output. The output path was
`.local/q-chi-upper-independent-audit-a1a11cbd/`; no production module or
production `.olean` was written. The command was:

```sh
LEAN_PATH="$(pwd)/.local/ql-robust-contraction-independent-audit-f4523b6f:$(pwd)/.local/q-chi-upper-independent-audit-a1a11cbd:<project-and-pinned-package Lean paths>" \
  .local/lean -o .local/q-chi-upper-independent-audit-a1a11cbd/QLearningChiUpperDraft.olean \
  .local/QLearningChiUpperDraft.lean
```

The actual project and pinned package paths were assembled from
`.lake/build/lib/lean` and each `.lake/packages/*/.lake/build/lib/lean`.
Compilation exited successfully without diagnostics. The fresh target
artifact SHA-256 is
`1e2c9314321fbb92ea0e30e96d98daf637ca50a9dcd52db76e5a019013cafc1d`.

A fresh import-only probe at
`.local/q-chi-upper-independent-audit-a1a11cbd/ImportAudit.lean` imported the
new artifact and ran `#print axioms` for all five exported declarations. The
probe exited successfully; each reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. Probe source SHA-256:
`3c60c42dbae436805ca8f81d6b525f03f4b32adf546a4ed4297de33b80edabeb`;
axiom output SHA-256:
`023fe6407d4f6c39ba8b6b5d5eaa3b0031e14b95b933fad069ee2fd0d9d5907d`.
This remains staged-source evidence, not integrated production export evidence.

## Production integration

The reviewed upper-deviation result is now integrated as `Formalization/ModelFree/QLearningChiUpper.lean`. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
