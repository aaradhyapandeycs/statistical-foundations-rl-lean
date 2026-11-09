# CRITIC: Theorem 6.13 for externally randomized estimators (`Thm6_13_randomized`)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): integrated into the library on 2026-11-09. F1 was adopted: the measurability premise was dropped, so `offline_minimax_lower_bound_randomized` and `Thm6_13_randomized` have no hypothesis beyond the printed ones, and the bound is the probability under seed⊗data when the failure set is measurable and its outer probability otherwise. Consequently R1's inaccurate sentence ("not defined") is gone from the module doc and the docstring. R2 was applied: the entries are in `Formalization/Statements/Ch6.lean` and `Ch6Proofs.lean`, the module is imported from `Formalization.lean`, the `Thm6_13` docstring points to `Thm6_13_randomized`, and the COVERAGE row and ledger scope were updated. Departing from this report's recommendation to keep `lean_statement` = `Thm6_13`, the Theorem 6.13 ledger record now points to `Thm6_13_randomized`, because it implies `Thm6_13`; `Thm6_13` remains proved and indexed. F3 was applied (Markov-kernel sentence in the docstring). F2 (deriving `lb_fano_core` from `lb_fano_core_sum`) was not done. Passages below that discuss the measurability hypothesis describe the reviewed pre-F1 version. The draft statement file and the probes are private and not published. The review text below is otherwise unchanged.


- Date (UTC): 2026-11-09T05:23Z. Reviewer: independent critic (not the builder).
- Git HEAD `c0d94c4b619426c0c0b2295cff6af707aba31f5f`, branch `recovery-batch-fhlb-thm39-sb2a-20261108`; reviewed files are untracked working-tree state.
- Scope: `Formalization/OfflineRL/LowerBoundRandomized.lean`, the builder's private draft statement file (`DRAFT-STATEMENT.lean`), existing `Thm6_13` (`Formalization/Statements/Ch6.lean`), ledger entry "Theorem 6.13", `docs/critic-thm6-13.md`.

## SHA256

| File | SHA256 |
|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches the pinned hash used by the earlier Thm 6.13 review) |
| `Formalization/OfflineRL/LowerBoundRandomized.lean` | `4e7c743cddb24387b4f25d1d83104bf10e88af0ff4618cf9bb21a8b515ca6e48` |
| builder's draft statement (`DRAFT-STATEMENT.lean`, private) | `32c174946ce62f94f14be22be95791d23abb764a7097408c8c3a8dff0c5a6960` |
| `Formalization/Statements/Ch6.lean` | `19969b06b1982a4e96e1b52594ba0602f9667b0c68defc50b61af795f4a3f372` |
| critic check `CriticCheck.lean` (reviewer's private probe folder) | `41af2c5975d67c73e06d91b50cc8c3ee5dbf8743d6c048c6f20b48b46c742eb7` |

## Independent source reconstruction

`offlineRL.tex:2367–2402`: for `γ ∈ [2/3,1)`, `S > 12`, `C⋆ > 2`, `ε ≤ 1/(672(1−γ))` there exist a class `{M_θ}`
(S states, 2 actions), a test distribution `ρ`, and a batch dataset of `N` independent samples with
single-policy concentrability in `[C⋆, 2C⋆]`, such that `inf_π̂ max_θ P_{M_θ}(V⋆_θ(ρ) − V^π̂_θ(ρ) > ε) ≥ 1/4`
when `N ≤ c₂ S C⋆/((1−γ)³ε²)`, universal `c₂ > 0`. ":2399–2400" says the infimum is "over all policy
estimators"; `P_{M_θ}` is "the probability under `M_θ`". The chapter never defines "policy estimator"
(grep of `offlineRL.tex` for estimator/randomiz: only informal uses at 335, 346, 385, 481 and in the proof
2674–2917, where `π̂` is converted to a decoder `θ̂` that is a function of the data). The prose after the
theorem (":2405–2413", "no algorithm can reliably identify…") reads most naturally as covering randomized
algorithms too. So the printed infimum is ambiguous between deterministic and randomized estimators; for
randomized ones the natural reading is: the estimator's internal randomness is independent of the data and
its law does not depend on `θ`, and `P_{M_θ}` is the joint law of (seed, data). The proof (Fano on the
θ-average of decoding errors) extends because the average error is linear in the seed law.

## Findings on the four questions

### Q1. Fidelity of `Thm6_13_randomized`

Compared clause by clause with the TeX and with `Thm6_13` (the earlier critic's table carries over for every
unchanged clause):

| Item | Verdict |
|---|---|
| `∃ c₂ > 0` outermost, γ/S/C⋆/ε ranges, no `ε > 0` (C9 handling) | identical to `Thm6_13`; exact vs TeX |
| Family, `Fintype.card State = S`, actions `Bool`, shared discount/rewards, `ρ`, `d^b`, concentrability in `[C⋆,2C⋆]` (ℝ≥0∞ ratio) | identical to `Thm6_13` |
| Threshold `(N:ℝ) ≤ c₂ S C⋆/((1−γ)³ε²)`, `∀ N` after the instance | identical |
| Sample law: `Measure.pi` of `∑_t ofReal(d^b(s,a) P_θ(s'|s,a)) • δ_t` on `⊤` | identical |
| Estimator | `Ω : Type u`, any `MeasurableSpace Ω`, any probability `μ`, `π̂ : Ω → data → StationaryPolicy`; quantified after the instance and after `N`, before `θ`. So `μ` and `π̂` cannot depend on `θ` (correct for `inf_π̂ max_θ`). |
| Independence of seed and data | law is `μ.prod P_θ` (product measure); `μ` is θ-free. Correct. |
| Conclusion | `∃ θ, 1/4 ≤ (μ ⊗ P_θ).real {p | ε < ρ-gap of π̂(p.1, p.2)}`. Correct `max_θ` reading over finite Θ. |
| Generality of the seed model | Because the dataset space is finite, any Markov-kernel estimator `κ : data → Prob(policies)` is a seed estimator with `Ω = ∏_D Policy`, `μ = ⊗_D κ(D)`, `π̂(ω,D) = ω D`. So nothing is lost by the seed formulation. |

No quantifier, constant or domain drift. The only change relative to `Thm6_13` is the estimator class and the
added measurability premise (Q2).

### Q2. The measurability hypothesis

- Equivalence claim: correct. Sections measurable ⇒ joint set measurable is proved
  (`measurableSet_of_measurableSet_sections`, countable discrete `D` with `⊤`); the converse is
  `measurable_prodMk_right`. So "equivalent to joint measurability" is true.
- Legitimacy: in ordinary mathematics it is the implicit well-definedness premise of `P(…)`, so it is not a
  hidden weakening of the printed result. It is disclosed in the docstring.
- But: the claim "Without it the failure probability under `μ ⊗ P_θ` is not defined" is false in Lean. A
  Mathlib `Measure` is an outer measure on all sets, so `.real` of a non-measurable set is the outer
  probability. Also, the premise is hard to discharge for a concrete Borel-randomized estimator, since the
  library has no lemma that the policy value is measurable in the policy.
- It can be dropped at small cost, and I compiled this. Replace the events by their measurable hulls
  `toMeasurable (μ ⊗ P_θ) E_θ`. Their sections contain the original sections, so the per-seed Fano sum still
  holds. `measure_toMeasurable` then returns the same value. The hypothesis-free export implies the draft Prop:
  the probe `example : Thm6_13_randomized.{u}` from `_nomeas` compiles. When the event is measurable, the
  two conclusions are literally the same Lean term. When it is not, the hypothesis-free version gives
  outer probability `≥ 1/4`. Inner probability `≥ 1/4` is false in general. Counterexample: take `Ω` with the
  trivial σ-algebra and let the seed pick which θ to play optimally. Then every measurable rectangle inside
  the failure set is null.

### Q3. Dirac special case and averaging lemma

- `offline_minimax_lower_bound_of_randomized` (Ω = Unit, μ = δ_()) compiles, and `example : Ch6.Thm6_13 :=
  offline_minimax_lower_bound_of_randomized` compiles (my probe). An expression diff of `Thm6_13`'s body against
  this theorem's type finds only auxiliary-constant differences (`Thm6_13._proof_1` etc. versus the inlined
  `Nat.instAtLeastTwoHAddOfNat …` / `IsScalarTower.right` instance proofs). These are Prop-valued and
  definitionally equal. So the randomized export genuinely recovers the deterministic theorem.
- `exists_prod_measureReal_ge_of_sum_sections`: correct and general. It assumes a finite nonempty index (needed:
  for empty `I` the conclusion `∃ i` fails), `μ` a probability measure, each `P i` a probability measure
  (s-finite suffices for Tonelli), and measurable events. The proof is a pointwise bound in ℝ≥0∞, then
  `lintegral_finset_sum` with `measurable_measure_prodMk_left` (Tonelli), then `Measure.prod_apply`, then
  pigeonhole by `Finset.sum_lt_sum_of_nonempty`. Sound.
- `lb_fano_core_sum` / `lb_minimax_core_sum`: same Fano call and arithmetic as `lb_fano_core`. In the main
  proof the per-seed bound is applied at `ε₀` and moved to `ε` by monotonicity (`ε ≤ ε₀`), and the `ε < 0`
  branch uses `trajectoryValue_le_optimalGreedy`. Both are sound. Same `c₂ = 1/(36·16·336²)`.

### Q4. Export vs draft Prop; compile and axioms

Commands (tree root, one Lean process at a time, no lake or LSP):

1. `bash scripts/lean-local.sh <probe folder>/CriticCheck.lean`. Exit 0, no
   errors or warnings (about 27 s). The file contains: the full library body (verbatim, lines 2–455); the critic
   lemma `exists_prod_measureReal_ge_of_sum_sections'`; the critic theorem
   `offline_minimax_lower_bound_randomized_nomeas` (the builder's proof with the hypothesis removed and the
   primed lemma used); Part A and Part B of the draft verbatim; the Dirac probe; the "nomeas ⇒ draft" probe;
   an expression diff; and `#print axioms`.
2. `bash scripts/lean-local.sh <probe folder>/DiffProbe.lean`. Exit 0. It shows that
   the existing `Thm6_13` and `offline_minimax_lower_bound` also differ only in auxiliary `_proof_n` constants
   (a baseline for the diff above).

Results:
- `Thm6_13_randomized_holds : Thm6_13_randomized.{u} := offline_minimax_lower_bound_randomized.{u}` type-checks.
  Both have universe params `[u]`. The expression diff (7 entries) consists only of `_proof_n` auxiliary constants
  versus inlined `AtLeastTwo` / `IsScalarTower` instance proofs. There is no binder, type or universe difference.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `Thm6_13_randomized_holds`,
  `offline_minimax_lower_bound_randomized`, `offline_minimax_lower_bound_of_randomized`,
  `exists_prod_measureReal_ge_of_sum_sections`, and `offline_minimax_lower_bound_randomized_nomeas`.
- I grepped the library file and the draft for sorry, admit, axiom, opaque, implemented_by, unsafe,
  native_decide, extern and ofReduceBool: 0 hits.
- Not run: `lake build`, `scripts/check.py`, `Audit.lean`. The import of `Formalization.Statements.Ch6` used the
  existing `.lake` olean, which has the same timestamp as `Ch6.lean`.

## Verdict: ACCEPT WITH DISCLOSURES

### Required

- **R1 (inaccurate disclosure).** The library module doc (`LowerBoundRandomized.lean:24–30`) and the draft
  docstring both say "Without it the failure probability under `μ ⊗ P_θ` is not defined". This is false in Lean,
  where `.real` is the outer measure on every set. Fix either way:
  (a) **preferred: adopt F1**, which removes the hypothesis, so the sentence disappears; or
  (b) replace the sentence with: "It makes the failure event a genuine event of `μ ⊗ P_θ`; without it, Lean's
  `μ ⊗ P_θ` would evaluate the outer probability of the set."
- **R2 (integration, same change).** Do the following together:
  - Add Part A to `Ch6.lean` and Part B to `Ch6Proofs.lean`, plus `import Formalization.OfflineRL.LowerBoundRandomized`.
  - Import the module from `Formalization.lean`.
  - Edit the `Thm6_13` docstring, which currently says "estimators using external randomness are not covered
    literally, though the Fano argument extends". Replace it with: "estimators using an independent external
    seed are covered by `Thm6_13_randomized`, of which this entry is the Dirac-seed special case".
  - Update the COVERAGE row and the `statement_scope` (text below).
  - Run `python3 scripts/check.py` (or `lake build` plus `lake env lean Audit.lean`) and record the result.

### Optional

- **F1 (drop the measurability hypothesis; verified to compile).** Add the lemma below after
  `exists_prod_measureReal_ge_of_sum_sections`:

  ```lean
  /-- Averaging over an independent seed without measurability of the events: the conclusion is about
  the (outer) measure `μ ⊗ P_i`, which equals the probability whenever `E i` is measurable. -/
  theorem exists_prod_measureReal_ge_of_sum_sections' {I Ω D : Type*} [Fintype I] [Nonempty I]
      [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (P : I → Measure D) [∀ i, IsProbabilityMeasure (P i)] (E : I → Set (Ω × D)) (c : ℝ)
      (hsum : ∀ ω, c * Fintype.card I ≤ ∑ i, (P i).real (Prod.mk ω ⁻¹' E i)) :
      ∃ i, c ≤ (μ.prod (P i)).real (E i) := by
    obtain ⟨i, hi⟩ := exists_prod_measureReal_ge_of_sum_sections μ P
      (fun i => toMeasurable (μ.prod (P i)) (E i)) (fun i => measurableSet_toMeasurable _ _) c
      (fun ω => (hsum ω).trans (Finset.sum_le_sum fun i _ =>
        measureReal_mono (Set.preimage_mono (subset_toMeasurable _ _)) (measure_ne_top _ _)))
    refine ⟨i, ?_⟩
    rwa [measureReal_def, measure_toMeasurable, ← measureReal_def] at hi
  ```

  Then make these changes in `offline_minimax_lower_bound_randomized` and in the Part A Prop:
  - Delete the premise `(∀ θ (D : …), MeasurableSet {ω | …}) →`.
  - Change `intro N hN Ω _ μ _ πhat hmeas` to `intro N hN Ω _ μ _ πhat`.
  - Call `exists_prod_measureReal_ge_of_sum_sections'` instead of the unprimed lemma.
  - Delete the argument `(fun θ => measurableSet_of_measurableSet_sections fun D => hmeas θ D)`.

  The Dirac corollary then needs no measurability argument: drop the `(fun _ _ => MeasurableSet.of_discrete)`
  argument. The `change`/`dirac_prod` step still uses `hEm`, which is fine.
  `measurableSet_of_measurableSet_sections` can stay as a public utility. Compiled as
  `offline_minimax_lower_bound_randomized_nomeas` in `CriticCheck.lean`, together with a proof that it implies
  the current draft Prop. Docstring sentence for the Prop: "No measurability of `π̂` in the seed is assumed.
  If the failure event is not measurable, the bound is for its outer probability under `μ ⊗ P_θ`. It is the
  probability whenever the event is measurable, for example when `Ω` is countable, or when `π̂` is measurable
  in the seed and the policy value is measurable in the policy."
- **F2 (duplication).** `lb_fano_core_sum` copies the arithmetic of `lb_fano_core`. A later refactor can derive
  `lb_fano_core` from `lb_fano_core_sum` by pigeonhole. This is not blocking.
- **F3 (docstring precision).** Add one sentence: "Since the dataset space is finite, every estimator given as a
  Markov kernel from datasets to policies is of this form (`Ω = ∏_D Policy`)."

## Recommended ledger classification for "Theorem 6.13"

**Printed result proved (not restricted).** `Thm6_13` states the printed hypotheses and conclusion for
deterministic estimators. `Thm6_13_randomized` extends the same conclusion, with the same constant and
instance, to every estimator with an independent seed. With F1 adopted it has no premise beyond the printed
ones. Without F1, its only extra premise is the implicit well-definedness of the printed probability, which is
disclosed. Neither assumes more than the TeX in substance or concludes less, and the deterministic entry is a
proved special case of the randomized one. So no `_restricted` or `_corrected` suffix and no
`SOURCE-ISSUES` entry are warranted. Keep `lean_statement` = `Thm6_13`. Mention `Thm6_13_randomized` in
`statement_scope`, or add a second ledger row "Theorem 6.13 (randomized estimators)" if the schema allows
only one statement per row.

Draft `statement_scope` (after F1):
> Printed hypotheses and conclusion: ∃ c₂>0 such that for γ∈[2/3,1), S>12, C⋆>2, ε≤1/(672(1−γ)) there are S-state two-action instances with concentrability in [C⋆,2C⋆] on which every estimator has ρ-gap >ε with probability ≥1/4 when N≤c₂SC⋆/((1−γ)³ε²). Thm6_13 covers deterministic maps from the N i.i.d. samples to a stationary policy; Thm6_13_randomized covers estimators using an independent seed of any law (probability under seed⊗data; outer probability if the failure event is non-measurable), with Thm6_13 as its Dirac-seed case. ε≤0 is handled as in C9.

(Without F1, replace the parenthesis with: "(failure event assumed measurable in the seed for each instance and dataset)".)

Draft COVERAGE replacement for the last two sentences of the Theorem 6.13 row (and add
`[LowerBoundRandomized.lean](../Formalization/OfflineRL/LowerBoundRandomized.lean)` to the file list):
> …has ρ-gap >ε with probability ≥1/4 when N≤c₂SC⋆/((1−γ)³ε²), both for deterministic estimators (`Thm6_13`) and for estimators with an independent external seed (`Thm6_13_randomized`, probability under seed⊗data). ε≤0 handled as in [C9](SOURCE-ISSUES.md#candidate-c9-offline-lower-bound-accuracy-endpoint). Independently source-reviewed ([deterministic](critic-thm6-13.md), randomized: public copy of this report).

Draft `Thm6_13_randomized` docstring, second paragraph after F1, replacing the "one hypothesis added" paragraph:
> No measurability of `π̂` in the seed is assumed. The failure probability is `(μ ⊗ P_θ)` of the failure set. When that set is measurable (for instance `Ω` countable, or `π̂` measurable in the seed and the value measurable in the policy) it is the probability. Otherwise it is the outer probability; an inner-probability version is false in general. Since datasets range over a finite set, every Markov-kernel estimator is of this seeded form.

## Process note

The evidence for this review should be published as `docs/critic-thm6-13-randomized.md`, with local paths removed, at integration time.
