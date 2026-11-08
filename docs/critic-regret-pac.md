# CRITIC: regret-to-PAC conversion (onlineRL.tex:115–183)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. The all-carriers refutation, which the critic wrote during this review, was independently reviewed (`review-regret-pac-all-carriers.md`) and adopted in its positive-constant form as the primary evidence for [C46](SOURCE-ISSUES.md#C46). The work was integrated into `Formalization/Online/RegretToPAC/{Definitions,StartState,Corrected,PrintedRefutation}.lean` (namespace `StatisticalRL.OnlineRL.RegretToPAC`), with statement-index entries `Eq_PAC_from_regret_conversion_corrected` and `Eq_PAC_from_regret_conversion_restricted` in `Formalization/Statements/Ch5.lean`. Names below are the integrated names, following the builder's rename list:
- the snapshot's fixed-carrier `_printed` Prop and its refutation are now `Eq_PAC_from_regret_conversion_printed_fixedCarrier` and `not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`;
- the critic's all-carriers Prop (without a positivity hypothesis) was strengthened at review with `∀ S A H, 0 < C S A H` and integrated as the main printed Prop `Eq_PAC_from_regret_conversion_printed`, refuted by `not_Eq_PAC_from_regret_conversion_printed`; below, "the all-carriers Prop" means the critic's version without positivity;
- counterexample algorithm `printedCexAlg`, constants `printedCexConst` (positivity `printedCexConst_pos`), reward argmax/argmin `rewardArgmax`/`rewardArgmin`;
- general lemmas `trajectoryValue_pointMass_nonneg`, `optimalValue_le_length`, `optimalValue_le_myopic_of_subsingleton`, `trajectoryValue_withPolicy_cons`, `expectation_of_subsingleton` (these replaced the snapshot's Unit-only lemmas, whose snapshot names are kept in §4); `value_le_optimal` → `trajectoryValue_pointMass_le_greedy`; `rowMeasure_real_setOf_false` → `rowMeasure_real_setOf_eq_zero`.

The snapshot's `Statements.lean` and `Refutation.lean` correspond to the integrated `Definitions.lean` (plus the Ch5 entries) and `PrintedRefutation.lean`; file hashes are those of the snapshot. The review text below is otherwise unchanged.

Independent critic, 2026-11-08. Read-only on builder files. My probes are kept in the reviewer's private probe
folder (oleans in the reviewer's private olean folder).
I did not touch `Formalization/`, `Formalization.lean`, or the project's `Formalization*` build outputs.

## 0. Snapshot integrity

The builder's reviewed snapshot (4 files) matches the builder's snapshot hash list. The builder's live working
files are byte-identical (`cmp`).

```
2d622baf37c1fc306ea941319d7ddcadb669d8cc0b85ed48f79545b1359e9969  Corrected.lean
f79e631cd3dee7647976d2a1a54b25283ced068dd75427a1cf8ebaca6becbcd6  Refutation.lean
5c9329c44b9e7523322427c797fa7daf518bb34b65237fa9b167bdac1dbad548  StartState.lean
de8c8962bcd4d237e8525f06a2af515b3b3092c0d63e47f0cf996360ee1bf4c0  Statements.lean
```

I did not trust the builder's oleans. I copied the four snapshot files to the reviewer's private probe folder
and changed only the import lines (builder's working prefix → reviewer's private prefix; checked with diff).
Then I compiled them one at a time with
`bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean …`. All four compiled with no
errors, in 6s, 2s, 4s and 2s.

## 1. Source, read first

- Protocol, :20–41. The reward is known (:20, and `prelim.tex:682–683`: r_h ∈ [0,1], deterministic, known
  to the learner). (i) s₁ᵏ i.i.d. ~ ρ. (ii) π^k is chosen from episodes 1..k−1 only. (iii) The policy is
  rolled out with a_h ~ π_h^k(·|s).
- Regret, :84–88: Σ_k V⋆₁(s₁ᵏ) − V^{π^k}₁(s₁ᵏ).
- Claim, :115–150. Take an algorithm that "for any MDP with S states, A actions and horizon H" satisfies
  E Regret(K) ≤ C_{S,A,H} K^{1−α}, with α ∈ [0,1] and C_{S,A,H} "some quantity that may depend on
  (S,A,H)". Let π̂ ~ Unif(π¹..π^K). Then w.p. ≥ 1−δ, V⋆₁(ρ) − V₁^{π̂}(ρ) ≤ C_{S,A,H+1} K^{−α} δ^{−1}.
- Proof, :153–183. Markov's inequality for a singleton ρ, which gives C_{S,A,H}. Then a step-0
  augmentation: "a single state s₀, a single action a₀", P₀ = ρ, and the algorithm "applied to the
  augmented MDP without modification", which gives C_{S,A,H+1}.
- The algorithm's inputs include K and r (UCBVI, :293). So letting the algorithm see H, K and r is
  faithful.

## 2. Verdicts

| Entry | Verdict |
|---|---|
| `Eq_PAC_from_regret_conversion_printed_fixedCarrier` + `not_Eq_PAC_from_regret_conversion_printed_fixedCarrier` (snapshot `_printed` and its refutation) | **ACCEPT WITH DISCLOSURES** as a refutation of the *fixed-(S,A)-class reading*. It is **not sufficient alone** to refute the book under the all-classes reading (R1). |
| `Eq_PAC_from_regret_conversion_corrected` / `eq_PAC_from_regret_conversion_corrected` | **ACCEPT WITH DISCLOSURES** (restricted algorithm class, already disclosed) |
| `Eq_PAC_from_regret_conversion_restricted` / `eq_PAC_from_regret_conversion_restricted` | **ACCEPT WITH DISCLOSURES** (same class) |
| `onlineEpisode_startState_independent` | **ACCEPT** |
| Critic probe: refutation of the all-carriers Prop (new) | Compiles, axioms clean. **Recommended as the primary C46 evidence.** |
| Draft C46 | **May be filed after R1–R3**, not as is |

## 3. Fail-closed check 1: is `_printed` at least as weak as the book?

(Here `_printed` is the snapshot's fixed-carrier Prop, now `Eq_PAC_from_regret_conversion_printed_fixedCarrier`.)

Direction of each deviation. A weaker Lean Prop, whose refutation therefore refutes more, needs more
hypotheses, fewer algorithms or a stronger conclusion.

- **Algorithm class (finite `Seed`, deterministic Markov deployed policies, planner sees H, K, r, seed).**
  This quantifies over *fewer* algorithms than the book, so the Prop is weaker and that is safe. The
  counterexample algorithm is seedless and deterministic, and it uses only H and the known reward, so it
  belongs to the book's class. Fine.
- **Carriers fixed outside the hypothesis.** The hypothesis covers every H, K, E, ρ on the *given*
  State/Action types only. The book's "for any MDP with S states, A actions and horizon H" can be read
  in two ways: (a) all MDPs in the given (S,A) class, or (b) every (S,A,H). Under (b) the book's
  hypothesis is strictly stronger than Lean's, so `_printed` is *stronger* than the book under (b), and
  refuting it does not refute (b). The two are not interchangeable: for α > 1/2 no algorithm meets the
  hypothesis on all classes (√K lower bound), but the fixed-class hypothesis can still hold on S = 1.
  The book-level repair argument needs C_{S,A,H} = H on the other classes, and that is not formalized in
  the snapshot. **This is a gap for an "airtight" filing, so R1.**
  **Closed by my probe.** My probe module defines the all-carriers Prop:
  - one algorithm family over *all* carriers `(State : Type u) (Action : Type v) [Fintype] [Fintype]
    [Nonempty Action]`, with a fixed finite seed type;
  - the regret hypothesis for *every* carrier pair, H, K, E and ρ;
  - the same conclusion as `_printed`, for every carrier pair.

  This Prop is at least as weak as both readings (a) and (b), up to the algorithm class, which only
  weakens it further. Its refutation at universe `.{0,0}` compiles with no errors or
  warnings beyond linters. Axioms: `[propext, Classical.choice, Quot.sound]`. It uses **strictly
  positive** constants: `printedCexConst S A H = if S = 1 ∧ H ≠ 1 then 1/4 else H + 1`, and
  `printedCexConst_pos` is proved.
  The algorithm is the argmin of the known reward if H = 1 and the argmax otherwise, on every carrier
  (`Finite.exists_max`/`exists_min`). The hypothesis is proved for every carrier:
  - card S = 1 and H ≠ 1: myopic play is optimal on any subsingleton state type
    (`optimalValue_le_myopic_of_subsingleton`), so the regret is ≤ 0 ≤ K/4;
  - every other case: the regret is ≤ KH ≤ (H+1)K, by `optimalValue_le_length`,
    `trajectoryValue_pointMass_nonneg` and rewards in [0,1].

  The instance is Unit, Bool, H = 1, K = 1, r = (1,0), δ = 1/2. The printed bound is
  C_{1,2,2}·1/δ = (1/4)/(1/2) = 1/2. The gap is ≥ V⋆ − r(argmin) ≥ 1 − 0 = 1 on every sample, so the
  event has probability 0 < 1/2.
- **C : ℕ³ → ℝ arbitrary, C = 0 allowed.** The printed text says only "some quantity". Nothing implies
  C ≥ 1 or C > 0. In any case the probe removes the dependence on C = 0, which supersedes the paper-only
  "C > 0 variant" in the draft. The paper variant is also correct: with C_{1,2,H} = η for H ≥ 2 and
  K = 1, α = 0, the bound is η/δ < 1 iff η < δ.
- **α ∈ [0,1] kept, δ > 0 only.** These match the print. α = 0 and δ = 1/2 are inside every reasonable
  range.
- **π̂ = π^J with J uniform.** The probability is written as E_ν[(1/K) Σ_k P_run(event_k)], which is
  exactly the joint (seed, run, J) probability. Faithful.
- **Regret and values.** V⋆ is `greedyStages` (backward induction, `greedy_trajectoryValue`), and V is
  the exact return of a deterministic Markov policy. The per-episode policy is
  `planner (history.take (k*H))`, the same function `onlineEpisodicChoose` executes
  (`EpisodicSelectorDefinitions.lean:27–33`). Faithful.
- **fallback = `Classical.choice (E 0).state_nonempty`.** It is read only on out-of-budget or impossible
  histories (`onlineEpisodicCurrentState`). It is the same in the hypothesis and the conclusion, and it
  is irrelevant on Unit. Harmless. `_corrected` takes an arbitrary fallback, which is more general.
- **Universe.** Carriers range over `Type u`. Every finite set is in bijection with a `Type 0` carrier,
  and the counterexample algorithm and constants depend only on cardinalities. Not a gap.

## 4. Fail-closed check 2: the refutation instance, recomputed

(Lemma names in this section are the snapshot's Unit-only lemmas; at integration they were replaced by the
general lemmas listed in the post-review note.)

The snapshot uses C_{·,·,1} = 1, C_{·,·,H≠1} = 0, α = 0, K = 1, δ = 1/2. I checked the snapshot proof
`hreg` step by step.

- **H ≠ 1.** The deployed policy is `myopicMax` at every step (`hf`, by `simp` with `H ≠ 1`). With one
  state, the transitions are point masses on (), so E is genuinely arbitrary (any rewards in [0,1], any
  transitions). The proof uses `optimalValue_le_myopic` by induction over all H, with
  `Finset.sup'_le` over actions. The regret is ≤ 0 = C·K.
- **H = 1.** Each term V⋆ − V ≤ 1 − 0 (`optimalValue_le_length`, `value_nonneg_unit`), so the sum is
  ≤ K = 1·K.
- **Instance.** V⋆ ≥ r(true) = 1 (`value_le_optimal`, now `trajectoryValue_pointMass_le_greedy`), and the
  deployed action is `myopicMin`, which gives `false`, reward 0. The bound is 0·1/(1/2) = 0, so the event
  is empty and 0 < 1 − 1/2.

Both branches are proved for every H, K, E and ρ, and the H = 0 case is excluded by `0 < H`. Correct.

## 5. Fail-closed check 3: `_corrected`, `_restricted`, start-state lemma

- **`_corrected`.**
  - The hypothesis holds only at the instance, so it is weaker than printed.
  - The constant is `C` (the regret constant at the actual H), and C is real of any sign. If C < 0 the
    hypothesis is false, since the regret is ≥ 0; C = 0 is handled by `sum_mul_ite_lt_le`, including
    t ≤ 0.
  - The conclusion is the printed shape with C_{S,A,H}.
  - Non-vacuous: any planner with C = H and α = 0 satisfies the hypothesis.
  - The proof chain is start-state independence, then flattened Markov over (seed, J, run), then the
    complement. No hidden hypotheses, and α ∈ [0,1] is unused but printed.
  - Faithful as a `_corrected` entry.
- **`_restricted`.** The text is identical to `_printed` plus `∀ H, C S A H ≤ C S A (H+1)` at the
  instance's cardinalities only (checked by diff). Non-vacuous: C = H with α = 0 works for any algorithm.
  The proof is a two-line corollary of `_corrected` via `measureReal_mono` and `gcongr`.
- **`onlineEpisode_startState_independent`.** For every g,
  E[g(π^k, s₁ᵏ)] = E[ρ.E g(π^k, ·)] under `onlineSequentialEpisodeLaw`. This is correct for the protocol:
  - π^k = `planner (history.take (k*H))`;
  - `onlineEpisodicChoose_update_of_lt` shows the selector does not read reset k before length k·H;
  - `onlineInitialVectorLaw` is the product law.

  Within an episode the policy table is evaluated at the current state, which is Markov and does not
  choose the table from s₁ᵏ. Faithful to (ii).

## 6. Fail-closed check 4: axioms and tokens

- **Re-probe** (an axiom re-probe file in the reviewer's private probe folder, on my recompiled copies).
  These depend only on `[propext, Classical.choice, Quot.sound]`: the snapshot refutation (now
  `not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`),
  `eq_PAC_from_regret_conversion_corrected`, `eq_PAC_from_regret_conversion_restricted`,
  `onlineEpisode_startState_independent`, `value_le_optimal` and `sum_mul_ite_lt_le`. The `example`
  type checks against the exact Props pass.
- An all-carriers axiom probe in the same folder: the all-carriers refutation depends on the same three
  axioms, and the type checks pass.
- **Token scan** (sorry, admit, axiom, native_decide, implemented_by, extern, unsafe, opaque, debug or
  skipKernel options, csimp) over the snapshot and my probe: no hits.

## 7. Fail-closed check 5: the draft C46

The draft is accurate on these points:
- the printed claim;
- the run-identity flaw (the proof's π̂ comes from the augmented run);
- the two proof flaws: a fresh s₀ gives S+1 states and C_{S+1,A,H+1}, and a₀ must be read as A
  identical actions;
- the augmentation is unnecessary under :25–33;
- both true versions;
- the algorithm-class scope;
- the uncovered follow-up :184–198 (the `V₁⋆(s)` slip).

It does not overclaim about the proof. Required edits:
- **R1** (blocking). Cite the all-carriers refutation (all carriers, strictly positive constants) as the
  primary machine-checked evidence, and integrate it with the entries. State that the
  fixed-carrier Prop (snapshot `_printed`) has its hypothesis on the instance's carriers only,
  which is the fixed-class reading. Replace "(paper computation, not formalized)" for the C > 0 variant.
- **R2.** Replace "without known rewards a K = 1 blind guess forces C_{1,2,2} ≳ 1" (unproved) with: "The
  construction uses the known-reward convention (`onlineRL.tex:20`, `prelim.tex:682–683`) and rewards in
  [0,1]. Whether the printed constant fails with unknown rewards is not determined here."
- **R3.** Add one sentence saying the counterexample algorithm is deterministic and seedless, so the
  restricted algorithm class of the entries does not weaken the refutation.

## 8. R-items (required) and F-items (findings)

- **R1–R3**: as in §7.
- **R4.** On integration, move the probe's generic lemmas (now `rewardArgmax`/`rewardArgmin`,
  `expectation_of_subsingleton`, `trajectoryValue_withPolicy_cons`, `trajectoryValue_pointMass_nonneg`,
  `optimalValue_le_length`, `optimalValue_le_myopic_of_subsingleton`)
  into the RegretToPAC module, either renamed or replacing the Unit-only versions. Follow the Thm 7.11
  precedent for a refuted printed entry: a `_printed` Prop plus a `not_…` wrapper, with
  the all-carriers Prop as the index entry for the refutation.
- **F1.** `_printed`'s docstring correctly says "every MDP with these S states and A actions". It matches
  the fixed-class reading only.
- **F2.** Letting the algorithm see K and r is consistent with UCBVI's input (:293).
- **F3.** The `_corrected` docstring cites "proof :153–183", but its proof differs: it is direct, with no
  augmentation. The docstring says so. Fine.
- **F4.** The augmented-run reading (the paper's own object) is not formalized. This is disclosed, and
  it is optional.
- **F5.** Randomized deployed policies (:35–38) and non-finite internal randomness are not covered by
  `_corrected` or `_restricted`. This is disclosed. It does not affect the refutation.

## 9. Recommended C46 and COVERAGE text

**C46: the regret-to-PAC conversion has the wrong constant C_{S,A,H+1}.**

- **Source.** `eq:PAC-from-regret-conversion` (`-regret`, `-pac`) and `eq:uniform-policy-pihat`,
  `chapters/onlineRL.tex:115–150`, proof :153–183. Protocol `eq:generation-s1k-shk-online`, :20–41.
  Conventions `prelim.tex:682–683`.
- **Counterevidence.** Machine-checked in Lean as the all-carriers refutation (integrated, in
  positive-constant form, as `not_Eq_PAC_from_regret_conversion_printed`), with the fixed-class form
  (now `not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`).
  - Algorithm: one deterministic, seedless algorithm on every finite class. It knows H and the reward
    (:20) and plays the reward-minimizing action when H = 1 and the reward-maximizing action at every
    step when H ≥ 2.
  - Hypothesis: it holds for every MDP of every class, with α = 0 and the strictly positive constants
    C_{1,A,H} = 1/4 for H ≠ 1 and C_{S,A,H} = H + 1 otherwise. With one state myopic play is optimal;
    otherwise the regret is ≤ KH because rewards lie in [0,1].
  - Instance: S = 1, A = 2, H = 1, r = (1, 0), K = 1, δ = 1/2. Every deployed policy has gap 1, but the
    printed conclusion requires gap ≤ C_{1,2,2}/δ = 1/2 with probability ≥ 1/2.
  - More generally, with C_{1,2,H} = η for H ≥ 2 it fails for every δ ∈ (η, 1).
  - The Lean statement restricts the algorithm class to finite-seed algorithms with deterministic
    deployed policies. The counterexample is in that class, so the restriction only weakens what is
    refuted.
  - The construction uses the known-reward convention and rewards in [0,1]. The unknown-reward case is
    not determined.
- **Proof flaws.**
  - The proof applies the algorithm to an augmented MDP, so its π̂ comes from a different run than the
    statement's.
  - A fresh s₀ gives S+1 states, and hence C_{S+1,A,H+1}.
  - The "single action a₀" must be read as A identical actions to stay in the class.
- **The augmentation is unnecessary.** Under protocol (i)–(ii), s₁ᵏ is independent of π^k
  (`onlineEpisode_startState_independent`).
- **True versions.**
  - `Eq_PAC_from_regret_conversion_corrected`: constant C_{S,A,H}, hypothesis only at the instance.
  - `Eq_PAC_from_regret_conversion_restricted`: the printed constant under C_{S,A,H} ≤ C_{S,A,H+1},
    which covers the book's Õ(√(SAH³K)) use.
- **Scope.** Both cover finitely supported internal randomness and deployed policies that are
  deterministic given the seed and history. Randomized π^k (:35–38) are not covered. The follow-up at
  :184–198 is not covered. Independently critic-reviewed. Not author-approved.

**COVERAGE row.**

> regret→PAC conversion (`onlineRL.tex:115–183`): printed statement refuted (C46,
> all-carriers refutation `not_Eq_PAC_from_regret_conversion_printed`, fixed-class refutation
> `not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`).
> Corrected: `Eq_PAC_from_regret_conversion_corrected` (constant at H).
> Restricted: `Eq_PAC_from_regret_conversion_restricted` (C nondecreasing in H).
> Algorithm class: finite seed, deterministic deployed policies.
> Remaining: :184–198 follow-up; the augmented-run reading; randomized deployed policies.

## 10. Commands run (all foreground, one at a time)

```
bash scripts/lean-local.sh -o <reviewer olean folder>/{Statements,StartState,Corrected,Refutation}.olean <reviewer probe folder>/<X>.lean   # exit 0 each
bash scripts/lean-local.sh <reviewer probe folder>/<axiom re-probe>.lean        # exit 0
bash scripts/lean-local.sh -o <reviewer olean folder>/<all-carriers module>.olean <reviewer probe folder>/<all-carriers module>.lean  # 1st: one `ring` goal failed; fixed; 2nd: exit 0
bash scripts/lean-local.sh <reviewer probe folder>/<all-carriers axiom probe>.lean    # exit 0
```

Probe sha256:
```
4c28e2a1e5ed49232cd249dd134e50575b0fa2b735d0ea8391c40ef7234876e1  all-carriers module
ab29b8afdad84d70f80e4cd21b831225de0b791906605ceb28cc2f18b807a2e0  all-carriers axiom probe
8aa1df242881f34667a3a9f2996b5e96db201e7cb10f2fa7e429e12bbf63b34e  axiom re-probe
```
(The copies of Corrected and Refutation differ from the snapshot only in their import lines; Statements and
StartState are byte-identical to the snapshot.)
