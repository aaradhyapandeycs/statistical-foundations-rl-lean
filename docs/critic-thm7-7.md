# CRITIC: Theorem 7.7 (`thm:Q-FTRL`): `Thm7_7_restricted`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review was of the builder's pre-integration snapshot. The builder's modules were integrated under `Formalization/` (for example `Statement.lean` became `Ch7Rest/Marl77Statement.lean`, `Pathwise.lean` became `Ch7Rest/Marl77Pathwise.lean`, `Hedge.lean` became `Online/Hedge/SecondOrderRegret.lean`, `SeqLawTail.lean` became `Probability/SeqLawExpTail.lean` and `NearSuper.lean` became `Ch7Rest/MarlNearSupersolution.lean` plus `Probability/MixtureVariance.lean`), and module names below are given under their integrated names. Required edits R1–R4 of this review were applied at integration: R1 made the docstring-only disclosure edits (the Prop stayed byte-identical, checked by text compare and `rfl`); R2 moved the shared lemmas to `Formalization/Probability/` (`adaptive_prod_le`, `adaptive_prod_sum_eq_one`, `adaptive_markov` and `union_bound_sum` to `AdaptiveProduct.lean` in namespace `StatisticalRL.AdaptiveKL`, with the `Rlhf.*` names kept as aliases; `exp_le_one_add_add_sq` to `ExpQuadraticBound.lean`), so `Online/Hedge/SecondOrderRegret.lean` imports no `Ch7Rest` module; R3 put `sum_sq_sub_mean_le` and `mixture_variance_ge` in `MixtureVariance.lean` (namespace `StatisticalRL`) and renamed `AdaptiveKL.pre` to `AdaptiveKL.seqPrefix`; R4 added the index entry, the wrapper `Thm7_7_restricted_holds` and the imports, deleted the transient builder and critic artifacts, and passed the full axiom audit. The optional items F1–F5 were not done. The review text below is otherwise unchanged.

Independent critic. I did not build this. I wrote only this file and probe files under
`<reviewer probe folder>/`, plus oleans for my independent rebuilt copy of the snapshot.
These probes are transient: they must not be integrated or published. I did not fetch any paper.
I read the source (`marl.tex:13–240`, `:300–316`, `:318–512`; `generative_model_model_based.tex:29–32`)
before I read the builder's docstrings, status notes or plan.

## Verdicts

| Result | Verdict |
| --- | --- |
| `StatisticalRL.Ch7Rest.Marl77.Thm7_7_restricted` (Marl77Statement.lean) and `thm7_7_restricted` | **ACCEPT WITH DISCLOSURES** |
| Index-entry draft `StatisticalRL.Statements.Ch7.Thm7_7_restricted` (builder's draft, now in `Formalization/Statements/Ch7.lean`) | **ACCEPT**. It is the same Prop (`rfl` probe), self-contained, and the docstrings are identical. |
| Library lemmas (F1 Hedge, F2 mixture variance, F3 `evalJ_jvarJ_le`, seqLaw tails) | **ACCEPT**, subject to the placement fixes R2–R3 at integration. |

- No refutation was found.
- The statement matches the printed theorem or is stronger in every quantitative respect. It is restricted only in
  the witness (an explicit reconstructed algorithm, not Q-FTRL), and that is disclosed.
- Integration is blocked only by the documentation fix (R1) and the placement and layering fixes (R2–R4).

## Pins and evidence (commands actually run, repo root, foreground, one Lean process at a time)

- `marl.tex` sha256 is `8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb`. This equals the pin in
  the builder's private plan and the plan check (docs/critic-thm7-7-plan-check.md).
- **Snapshot.**
  - `shasum -a 256` over the builder's reviewed snapshot (`*.lean`) matches the builder's snapshot hash list for all 16
    files.
  - The builder's live working files are identical to the snapshot (`diff` of the hash lists is empty).
- **Dependency oleans.** The oleans of `VPOAdaptive712`, `Marl76Eval`, `Marl76Defs`, `Marl78Defs`, `Marl78Product`,
  `MarlPrinted78` and `AdaptiveKLDefinitions` are newer than their sources. `git status` shows no modified
  `Formalization/` files (HEAD `8db6fe2`).
- **Independent rebuild.** I did not rely on the builder's oleans.
  - I copied the snapshot to `<reviewer probe folder>/` under a separate module prefix and changed only the
    module prefix in its imports.
  - I compiled all 16 modules in dependency order with
    `bash scripts/lean-local.sh -o <reviewer olean path>/<M>.olean <reviewer probe folder>/<M>.lean`.
  - Every module exited 0 with 0 errors and took 1–10 s each.
  - The only warnings are 8 linter warnings: unused variable `hlam` in Marl77Pathwise:119 (snapshot line), and auto-included unused
    section variables in `stage_mean_le`, `stage_mean_ge`, `stage_bonus`, `rew_window` and `fV_window`.
- **Probe.** `bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean` exited 0. It checks:
  - `example : Statements.Ch7.Thm7_7_restricted = Ch7Rest.Marl77.Thm7_7_restricted := rfl`, which passes;
  - `#check (thm7_7_restricted : Thm7_7_restricted)`, which passes;
  - `#print axioms` for `thm7_7_restricted`, for the wrapper `Thm7_7_restricted_holds_critic : Statements.Ch7.Thm7_7_restricted`,
    and for `core_cce`, `gap_margProd_le_two_mul`, `evalJ_jvarJ_le`, `hedge_second_order_regret` and
    `seqLaw_freedman_tail`. Each depends only on `[propext, Classical.choice, Quot.sound]`.
- **Token scan.** `grep -nE 'sorry|admit|axiom|opaque|native_decide|implemented_by|set_option|@[extern|unsafe|macro|elab|partial def|decreasing_by'`
  over the snapshot returns no matches.
- **Import probe.** `HedgeImportProbe.lean` is the Hedge module (now `Online/Hedge/SecondOrderRegret.lean`) with its SeqLawTail
  import (now `Probability/SeqLawExpTail.lean`) replaced by `Formalization.MDP.CoreDefinitions`. It fails. Hedge genuinely uses `AdaptiveKL.exp_le_one_add_add_sq` and the
  `sum_div` name in scope (see R2).
- **Not run.** `python3 scripts/check.py` and the full `Audit.lean`, because the modules are not integrated yet
  (R4).

## Findings

### S1. Quantifier structure and binders: FAITHFUL OR STRONGER (OK)

**Source (my reading).** The theorem reads: "Consider any δ∈(0,1), ε∈(0,H]. There exists a model-based algorithm
(i.e., Q-FTRL) that, with probability ≥ 1−δ" finds the following:

- (a) for two-player zero-sum games, π̂_NE with gap ≤ ε, using Õ(SAH⁴/ε²) samples;
- (b) for general-sum games, π̂_CCE with gap ≤ ε, using Õ(H⁴SΣA_i/ε²) samples.

**Lean.** The Lean statement is
`∃ C > 0, (∀ m S H A, S≥1 → A_i≥1 → ∀ δ ε, δ∈(0,1) → ε∈(0,H] → ∀ rew, rew∈[0,1] on 1..H → ∃ N rule out, N ≤ … ∧ ∀ P, 1−δ ≤ P_law(gapJ ≤ ε)) ∧ (two-player clause)`.

- **Universal constant.** C is existentially quantified first, before m, S, H, A, δ, ε and the reward, so it is a
  universal constant. It does not depend on ε (no ε-dependent C), and it does not depend on m. The proof uses
  C = 20000.
- **Algorithm before the kernel.** The algorithm (N, rule, out) is chosen after the reward, δ and ε, but before P.
  - The rule's type is `(t : ℕ) → (Fin t → Query × Fin S) → FiniteDistribution Query`, and `out` is a function of
    the history only.
  - **No P leak.** Neither type mentions P, and P is bound later.
  - The environment `genEnv ⟨P, rew⟩` returns only `s′ ∼ P_{h+1}(·|s,a)`, which matches `:307–311`.
  - The algorithm sees the known reward, as `generative_model_model_based.tex:31` says ("reward function is fully
    known"). Without that knowledge both clauses would be false.
- **Randomization and adaptivity.** Rule randomization (a `FiniteDistribution` per step) and full adaptivity are
  permitted. `FiniteDistribution` is a genuine probability vector (nonnegative, sums to 1). `interactionLaw` is the
  sequential law built from it, so it is a probability law. No non-measure law can occur.
- **Sample complexity.** "Total sample complexity" is read as a **deterministic** query count N that is the same on
  every run. This is stronger than a random count with a high-probability bound.
- **Probability.** "With probability at least 1−δ" is written as `1 − δ ≤ Σ_hist law(hist)·1[gap ≤ ε]`, for every
  P. This is the same shape as `Thm7_8_corrected`.
- **Domain binders.**
  - `S ≥ 1` and `A_i ≥ 1` are added. They are source conventions (`𝒮={1..S}`, `𝒜_i={1..A_i}`, `:21–23`).
  - In Lean they are necessary. S = 0 makes `FiniteDistribution Query` empty, so no rule exists. A_i = 0 makes the
    output type empty.
  - H ≥ 1 follows from 0 < ε ≤ H.
  - m is unrestricted, and m = 0 is handled honestly (ΣA = 0, the log is `log 0 = 0`, N = 0, gap = 0).
- **Reward window.** Rewards are constrained only on steps 1..H, which are the only steps that `valueJ`/`value` read
  (`valueJ G π i 1 H`). For an upper bound, this assumes less than constraining every h.
- **Zero-sum class.** The class is `rew 0 ∈ [0,1]`, `rew 1 = −rew 0` on 1..H. This is exactly `:50–54` (r₂ = −r₁,
  r₁ ≥ 0, normalization for player 1). The gap is evaluated in the *original* game ⟨P, rew⟩, not in a shifted one.
  Only the algorithm shifts internally (`gapJ_shift`).

### S2. Õ and A: FAITHFUL OR STRONGER (OK)

- **General-sum budget.** `N ≤ C·H⁴·S·ΣA_i/ε²·log(4HSΣA_i/δ)`.
- **Zero-sum budget.** `N ≤ C·H⁴·S·max(A₀,A₁)/ε²·log(8HS·max/δ)`.
- **Õ.** The bounds contain a single logarithm with no ε or log(1/ε) factor. This is the strongest standard reading
  of Õ.
- **Reading of A.** A is undefined in the source (C39). The max reading implies the A₁+A₂ and A₁=A₂ readings,
  because max ≤ sum inside the polynomial and inside the logarithm. I checked that the disclosure states this.
- **Non-triviality.** The bound is not trivially attainable. The already-proved `Thm7_8_corrected` (same adaptive
  generative model, known reward, and the same zero-sum class for m = 2) shows that N ≳ H⁴S·maxA/ε² is necessary
  for ε ≤ H/2048. So no small C or N = 0 witness exists. I argue this in prose only; I did not compile a Lean
  probe of it.

### S3. gap, NE and CCE objects: FAITHFUL (OK)

- **General-sum gap.** `gapJ G π = ⨆ s, ⨆ i, (bestResponseValueJ − valueJ … 1 H s)`. Here:
  - `bestResponseValueJ` is the iSup over Markov `π'_i` of `valueJ (deviate π i π')`;
  - `deviate` is the law of `update a' i b` with a′ ∼ π and b ∼ π′ independent, so the −i part is π's marginal,
    and π′_i is played independently;
  - this is `eq:defn-optimal-V` (:119–126) and `eq:defn-NE-gap` (:326–342), applied to a joint (correlated) Markov
    policy, which is the ε-CCE of :346.
- **No junk values.** The iSup is never a junk 0: for fixed finite rewards, values are bounded by H·max|r|, so the
  set is bounded above. The iSup over `Fin S` and `Fin m` is finite.
- **Zero-sum gap.** Clause (a) outputs a `ProductPolicy` and uses `gap` (product values, `Function.update`
  deviations). An ε-NE is required to be a *product* policy (:345), and it is.
- **Step 1 only.** Both definitions are at step 1 only, as in the book (C45). This does not matter for this
  theorem, because we construct the output ourselves.

### S4. Vacuity hunt: nothing found (OK)

- **Hypotheses are satisfiable.** For example S = H = 1, A ≡ 1, δ = ε = 1/2 and r = 0 satisfy every hypothesis.
- **Output types.** No output type trivializes the gap. `JointPolicy` and `ProductPolicy` are the library's
  objects, and the out-of-window branch of `Alg.out` (h ∉ 1..H) is never read by the values.
- **The conclusion is about the right object.** The gap is computed for `⟨P, rew⟩` with the same P that drives
  `genEnv`, and with the original reward.
- **ε = H is trivial but harmless.** At ε = H the claim is trivial (gap ≤ H), which is harmless for an upper bound.
  The algorithm does not special-case it, so the bound is uniform on (0,H], as `:476` says.
- **D6 tuning re-derived.** η = λ = ε/(80H²), u = L/T ≤ ε²/(2000H³). The bound becomes
  ε/2 + 16H²u + 240H³u/ε + εHu/80 ≤ (0.5 + 0.008 + 0.12 + 10⁻⁵)ε ≤ ε, using ε ≤ H, and ηH ≤ 1/80 ≤ 1/4.
- **Sample count re-derived.** N = HST·ΣA with T ≤ 2000H³L/ε² + 2. Since L ≥ log 4 > 1 and ε ≤ H give
  H³L/ε² ≥ 1, we get N ≤ 2002·H⁴SΣA·L/ε².
- **Number of events.** There are HS(ΣA + 3m) ≤ 4HSΣA events, so `e^{-L}·#events ≤ δ`.
- **Zero-sum budget re-derived.** At accuracy ε/2: 4·2002·2 = 16016 ≤ 20000, and log(4HS(A₀+A₁)/δ) ≤ log(8HS·max/δ).
- **D6, D7, D8 are internal only.** They do not touch the statement. The statement module's hash `7c2c21df…` is
  unchanged, and the `rfl` probe confirms the index entry and the library Prop agree.

### S5. Restriction and disclosure: HONEST, needs one wording fix (R1)

- **The `_restricted` name is right.** The printed claim names its witness ("i.e., Q-FTRL"), which the monograph
  omits (:432). The proof uses a different explicit algorithm. This follows AGENTS.md (an export that does not imply
  the printed result is a source-fidelity finding) and the C32 and C33 precedents.
- **The docstring wording on "model-based" is too soft.**
  - It says only that "model-based" is "not formalized". But the witness builds **no** empirical transition kernel.
    It uses one-sample gains r + V̄(s′) inside Hedge, which is a model-free-style update.
  - The book contrasts its methods with "the model-based methods introduced in previous chapters" (:432).
  - The disclosure should therefore say plainly that the witness is not shown to be model-based, and is not a
    plug-in or empirical-model method (R1).
- **The "single algorithm" remark is correct but prose only.**
  - The overlap of the two classes is m = 2 with r ≡ 0 on 1..H, because r₀ ∈ [0,1] and −r₀ ∈ [0,1] force r₀ = 0.
    There every policy has gap 0, so N = 0 serves both clauses.
  - This fixes plan-check fix 2. The A = (100,1) counterexample to the "A ≤ ΣA" argument is real, and I checked it
    numerically.
  - The ledger must say the remark is not machine-checked (R1).

### S6. Proof soundness: OK

- **Kernel-checked.** The theorem is kernel-checked against the exact Prop, with the three standard axioms only.
  The algorithm types cannot see P, so even an incorrect locality argument could not make the statement unsound.
  Locality is used only inside the proof.
- **Key lemmas.** I spot-checked their statements and found them meaningful, with no hidden hypotheses:
  - `hedge_second_order_regret` (F1) is the standard second-order regret for exponential weights. Its hypotheses
    are η > 0, ηR ≤ 1 and gains in [0,R]. Its conclusion is
    `Σ q_t(b) ≤ log n/η + Σ⟨π_t,q_t⟩ + η Σ Var_{π_t}(q_t)`, which is correct.
  - `mixture_variance_ge` (F2) is correct (the variance is the least second moment about a point).
  - `evalJ_jvarJ_le` (F3) has exactly the hypotheses of plan-check fix 5: 1 ≤ H, 0 ≤ f_t ≤ H on 1..H,
    f_{H+1} = 0, and r ∈ [0,1] on 1..H. Here v = `jvarJ` is the variance over the joint law of (a, s′). The
    conclusion is `Eval(v)_1 ≤ 5H² + 2H·Eval(Δ⁻)_1`.
  - `seqLaw_freedman_tail` assumes mean zero under the step kernel given the prefix, |X| ≤ 1, and predictability
    (`hdep` on entries < k). It concludes `P(L ≤ Σ(X − E X²)) ≤ e^{−L}`, which is valid by e^x ≤ 1 + x + x² on
    |x| ≤ 1 and a supermartingale argument through `Rlhf.adaptive_markov`.
  - `good_prob` is a union bound giving `1 − #Ev·e^{−L}`.
  - `gapJ_le_of_good` and `gap_arith` match the D6 and D9 arithmetic above.
  - `gap_margProd_le_two_mul` is correct. In two-player games, a deviation sees only the other marginal
    (`deviate_sum_two`), so BR_i(⊗marg) = BR_i(π). With V₀ + V₁ = 0 on 1..H, each term is at most
    [BR_i(π) − V_i(π)] + [BR_j(π) − V_j(π)] ≤ 2·gapJ(π).
- **D7.** The upper side is proved for deterministic deviations and applied to `brPolicy` through the existing
  `bestResponseValueJ_eq_brPolicy`. No extra hypothesis enters the main theorem.

### S7. Library quality (R2–R3, F-items)

- **Layering problem.** The SeqLawTail module (intended for `Probability/SeqLawExpTail.lean`) imports
  `Formalization.Ch7Rest.VPOAdaptive712` for `Rlhf.adaptive_markov` and `union_bound_sum`. Through the shared
  helper `exp_le_one_add_add_sq`, the Hedge module (intended for `Online/Hedge/`) depends on it transitively. A generic
  Probability or Online module must not depend on a chapter-specific Ch7 module (R2).
- **Wrong namespace for generic lemmas.** `sum_sq_sub_mean_le` and `mixture_variance_ge` are generic but sit in
  namespace `StatisticalRL.Ch7Rest.Marl77`, while their intended home is `Probability/MixtureVariance.lean` (R3).
- **Too generic a name.** `AdaptiveKL.pre` is a very short public name in a widely imported namespace (R3).
- **Duplicated definitions.** `wmean` and `wvar` duplicate `FiniteDistribution.expectation` and
  `FiniteDistribution.variance` (`Probability/Variance.lean`) on `Fin n` (F2).
- **Placement of F3.** The Markov-game lemmas `bellJ`, `jvarJ`, `evalJ_*` and `evalJ_jvarJ_le` live in namespace
  `Marl77`. Since `evalJ` is `Marl76.evalJ`, namespace `Marl76` (or `Marl`) in `MarlNearSupersolution.lean` would
  fit better (F3).

## Required fixes (R-items)

- **R1. Disclosure text.**
  - Use the exact COVERAGE row text and C39 paragraph given below.
  - In the docstring of both `Marl77Statement.lean` and the index entry, replace the clause
    `it is not shown to be Q-FTRL, and "model-based" is not formalized.` with
    `it is not shown to be Q-FTRL, and it is not model-based in the sense of :355–377 (it builds no empirical
    transition kernel); "model-based" is not formalized.`
  - Also replace the sentence on the single-algorithm remark with one ending
    `(argued in prose; not machine-checked).`
  - These are docstring-only edits. The Prop must stay byte-identical. Re-run the `rfl` probe afterwards.
- **R2. Layering.** Before the modules go to `Probability/` and `Online/`, do **one** of the following:
  - (a) move `Rlhf.adaptive_markov`, `Rlhf.union_bound_sum` and `exp_le_one_add_add_sq` into a `Probability/`
    module (for example `Probability/SeqLawExpTail.lean` itself), and have `VPOAdaptive712` import that module;
  - (b) keep the SeqLawTail and Hedge modules under `Ch7Rest/`, and say so in PROGRESS.

  In either case, `Online/Hedge/SecondOrderRegret.lean` must not import a `Ch7Rest` module.
- **R3. Namespaces and names at relocation.**
  - Put `sum_sq_sub_mean_le` and `mixture_variance_ge` in a generic namespace (`StatisticalRL` or
    `StatisticalRL.FiniteDistribution`), matching their intended file.
  - Rename `AdaptiveKL.pre`, for example to `histPrefix` or `seqPrefix`, or make it `protected`. Check for clashes
    with `grep -rn '\bpre\b' Formalization`.
- **R4. Integration evidence.** After moving the modules:
  - add the index entry, the `Ch7Proofs` wrapper `theorem Thm7_7_restricted_holds : Thm7_7_restricted := Ch7Rest.Marl77.thm7_7_restricted`,
    and the `Formalization.lean` imports;
  - run `python3 scripts/check.py` and the axiom audit, and record the hashes;
  - delete the transient builder and critic oleans and the probes, and confirm that none of them is
    published.

## Optional findings (F-items)

- **F1.** Clean the 8 linter warnings: unused `hlam` in Marl77Pathwise:119 (snapshot line), and the auto-included section variables in
  `stage_mean_le`, `stage_mean_ge`, `stage_bonus`, `rew_window` and `fV_window`. The last group means those lemmas
  carry unused hypotheses. Use `omit … in` or explicit binders.
- **F2.** Express `wmean`/`wvar` through `FiniteDistribution.expectation`/`variance`, or add bridge lemmas, to
  avoid a parallel API.
- **F3.** Put the F3 near-supersolution lemmas in namespace `Marl76` or `Marl`, matching `evalJ`.
- **F4.** Optionally, add a Lean corollary `Thm7_7_restricted_single`: one (N, rule, out) serving both classes, by
  branching on the known reward. That would turn the prose remark into evidence. It is not required.
- **F5.** Optionally, add a Lean non-triviality probe: `Thm7_8_corrected` refutes the 7.7 bound for small enough C
  (for example C·log(·) < c₂). S2 argues this in prose only.

## Required disclosure text

**COVERAGE row (Theorem 7.7, `thm:Q-FTRL`, multi-agent chapter lines 441–467):**

> Restricted variant proved (`Thm7_7_restricted`). It proves the existential guarantee with an explicit
> reconstructed witness, optimistic Hedge (entropic FTRL) with backward induction and per-agent adaptive
> generative queries. The witness is not shown to be Q-FTRL (omitted at :432), and it is not model-based (no
> empirical kernel). The printed rates are proved with one universal constant C = 20000:
> - an ε-CCE with N ≤ C·H⁴S·Σ_iA_i·ε⁻²·log(4HSΣ_iA_i/δ);
> - for two-player zero-sum games, an ε-NE (product output) with N ≤ C·H⁴S·A·ε⁻²·log(8HSA/δ), A := max(A₁,A₂).
>
> The guarantee holds for all δ ∈ (0,1), ε ∈ (0,H] and every transition kernel, with probability ≥ 1−δ. The
> query count is deterministic. The algorithm knows the reward but not P. Added S ≥ 1 and A_i ≥ 1. Rewards are
> constrained on steps 1..H only. See SOURCE-ISSUES C39. Not author-approved.

**C39.** In the existing paragraph, replace "Found by a source preflight and confirmed by an independent source
check; no Lean evidence yet." with "Found by a source preflight and confirmed by an independent source check."
Then append:

> Restricted result (2026-11-08). The monograph omits Q-FTRL (`marl.tex:432`), so the project proves the
> existential claim of Theorem 7.7 from scratch with an explicit reconstructed witness (`Thm7_7_restricted`,
> `Formalization/Ch7Rest/Marl77*.lean`). The witness works as follows:
> - For each step h = H, …, 1 and state s, it plays T rounds of Hedge (entropic FTRL) for every player.
> - In each round, every pair (player i, action b) issues one generative query (h, s, (b, a₋ᵢ)), with a₋ᵢ drawn
>   from the other players' current weights.
> - It forms optimistic values with a variance bonus, clipped at H − h + 1.
> - The output is the average of the round product policies, a correlated joint Markov policy, for the
>   general-sum CCE claim. For two-player zero-sum games, the algorithm shifts player 2's reward internally, runs
>   at accuracy ε/2, and outputs the product of the marginals. In the zero-sum case, gap(⊗ marginals) ≤ 2·gapJ is
>   proved in Lean.
>
> The witness is not shown to be Q-FTRL. It builds no empirical transition kernel, so "model-based" is not
> claimed.
>
> What is proved: one universal constant C = 20000, quantified before all sizes, such that the following holds for
> every δ ∈ (0,1), ε ∈ (0,H], known reward and every transition kernel, with probability ≥ 1 − δ:
> - N ≤ C·H⁴S·Σ_iA_i·ε⁻²·log(4HSΣ_iA_i/δ) adaptive, randomized generative queries give gap ≤ ε for the joint
>   output (`eq:defn-NE-gap`, CCE);
> - N ≤ C·H⁴S·max(A₁,A₂)·ε⁻²·log(8HS·max(A₁,A₂)/δ) queries give an ε-NE product policy for two-player
>   zero-sum games (r₂ = −r₁, r₁ ∈ [0,1]).
>
> Readings:
> - The query count is deterministic.
> - A is read as max(A₁,A₂), which implies the A₁+A₂ and A₁ = A₂ readings.
> - Õ is read as a universal constant times one log(·/δ) factor, with no ε inside the logarithm.
> - The algorithm sees the reward (`generative_model_model_based.tex:31`) but not P.
> - Added domain conditions are S ≥ 1 and A_i ≥ 1. Rewards are constrained on steps 1..H only.
> - The two bullets are separate existentials sharing C. That one algorithm serves both (by branching on the known
>   reward, with N = 0 on the overlap r ≡ 0) is argued in prose only.
>
> Whether Q-FTRL itself attains the rate is not checked. No falsity of the printed statement is known.
> Independently reviewed. Not author-approved.

## Not checked / limits

- I did not read every proof line of Locality, Stage, Events or StageBounds. The kernel check covers soundness, and
  I reviewed the statements only.
- I did not run `check.py` or the full `Audit.lean`, because the modules are not integrated (R4).
- The Lean non-triviality probe (F5) and the single-algorithm corollary (F4) were not built.
- Transient artifacts I created: `<reviewer probe folder>/` (the rebuilt `*.lean` copy, `Probe.lean`,
  `HedgeImportProbe.lean`) and the oleans of the rebuilt copy.
