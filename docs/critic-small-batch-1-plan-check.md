# CHECK: small batch 1 plan (independent plan check, critic stance)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-08): item (d), the regret-to-PAC conversion (Section 1, the (d) row of the verdict table, the (d) parts of Section 5 and answers 7–9, and the C46 numbering note), has since been built, independently critic-reviewed and integrated on 2026-11-08: issue C46 is filed in `SOURCE-ISSUES.md`, and the statement-index entries are `Eq_PAC_from_regret_conversion_corrected` and `Eq_PAC_from_regret_conversion_restricted` in `Formalization/Statements/Ch5.lean` (see `critic-regret-pac.md` and `review-regret-pac-all-carriers.md`). This check itself is not a ledger record for item (d); the ledgers are. Items (a1)–(a3), (b) and (c) were built and independently reviewed (`critic-small-batch-1.md`); they were integrated into the library on 2026-11-08 (see `critic-small-batch-1.md`). The check text below is otherwise unchanged.

Date: 2026-11-08. Checker: an independent agent. No Lean or lake was run and `Formalization/` was not edited.
The sources were read before the plan's conclusions. Not a fidelity certificate for the code that will be built.

- Plan sha256 (verified): `118920f761f9a4f81a6757366fa632c3e2cf08cdff86953cb8b329de931368e2` (507 lines).
- Source hashes: all four match the plan (prelim `2d27bb72…`, MF `7f4eb058…`, robust_RL `95ce19a9…`,
  onlineRL `393a4d26…`).
- SOURCE-ISSUES: the highest committed candidate is **C45**. The uncommitted working-tree diff (+4 lines) only adds a
  Thm 3.2 approximate-planner sentence to *Statement-index scope disclosures* (`:458ff`). It adds no new
  C-number, so **C46 is the next free number**. Re-check at integration.
- Numbering: `nowfnt.cls:1335` gives `remark` its own per-chapter counter. MF is chapter 4, so its remarks at :226, :914
  and :2088 (the one at :2093 is commented out) are Remarks 4.1, 4.2 and 4.3. `cousins.tex` is chapter 7 and inputs
  robust_RL first, so :361 is Remark 7.1. The names are right. The equation numbers 2.27/2.28 were not verified, so
  label-derived names are the safe choice.

## Verdicts

| Item | Verdict |
|---|---|
| (d) regret→PAC | **GO WITH FIXES**. Genuine source error, not a strawman. (Since built, critic-reviewed and integrated: C46; see `critic-regret-pac.md`) |
| (a3) Remark 4.3 | **GO**. `_corrected` → C34 is right. |
| (c) Remark 7.1 | **GO WITH FIXES** (minor). |
| (a1) Remark 4.1, (a2) Remark 4.2 | **GO**. |
| (b) eq 2.27/2.28 | **GO WITH FIXES**. The import edge is blocking as drafted. |
| Order / sizes | **GO** (see the last section). |

---

## 1. Regret-to-PAC (onlineRL:115–183, protocol :25–33)

> **Since built, critic-reviewed and integrated** (C46 filed; entries `Eq_PAC_from_regret_conversion_corrected` and `_restricted`; see `critic-regret-pac.md`). This section records the plan check only.

**Source re-read.** Hypothesis (:118–126): "an online RL algorithm that, *for any MDP with S states, A actions and
horizon H*, satisfies E[Regret(K)] ≤ C_{S,A,H} K^{1−α} for some α ∈ [0,1] and some quantity C_{S,A,H} that may
depend on (S,A,H)". π̂ ~ Unif(π¹,…,π^K) of "the deployed policies" (:127–130). Conclusion (:134–139): w.p. ≥ 1−δ,
V⋆₁(ρ) − V₁^{π̂}(ρ) ≤ C_{S,A,H+1} K^{−α} δ^{−1}. The proof treats the singleton case, then adds a step 0 and
applies the algorithm "to the augmented MDP without modification" (:157–161). π̂ is then a draw from the policies
deployed on the *augmented* run. The theorem's ρ is the initial distribution of the given MDP (:107–108, :25–28),
so the deployed policies in the statement are the ones from the run on the given MDP.

**Counterexample re-derived. It is legitimate.**
- Algorithm family indexed by (S,A,H). The protocol fixes H and the agent knows it. The reward is known to the agent
  (:20). Every standard algorithm (UCB-VI, MVP) uses H. The hypothesis quantifies over a single algorithm that works
  "for any MDP with S states, A actions and horizon H", and nothing forbids H-dependent behaviour.
- S = 1, A = 2. For H ≥ 2 the algorithm plays argmax_a r_h(a) at each step. With one state the transitions are
  trivial, so this myopic play is optimal and the regret is 0 surely. For H = 1 it plays argmin. For other (S,A) it
  does anything.
- The constants are arbitrary, as printed ("some quantity … that may depend on (S,A,H)"). Take α = 0, C_{1,2,1} = 1
  (the H = 1 gap is ≤ 1), C_{1,2,H} = 0 for H ≥ 2, and C_{S,A,H} = H otherwise (gap ≤ H per episode). The hypothesis
  holds for every MDP of every class.
- H = 1 instance with r(a₁) = 1 and r(a₂) = 0: every deployed policy has gap 1. The printed conclusion says
  gap ≤ C_{1,2,2}/δ = 0 with probability ≥ 1−δ > 0. Contradiction.
- **It does not rely on C = 0.** Take C_{1,2,H} = η > 0 for H ≥ 2. Then gap 1 > η/δ for any δ ∈ (η, 1), so the claim
  still fails. The construction does rely on the known-reward convention (:20) and α = 0. Without known rewards a
  K = 1 blind guess forces C_{1,2,2} ≳ 1 and the simple construction breaks. The book makes the known-reward
  convention, so this does not weaken the refutation. Say so in C46.
- The printed statement does not say which run π̂ comes from. Inside the statement, "the deployed policies" can only
  mean those of the algorithm run on the stated MDP with the stated ρ. The augmented run first appears inside the
  proof. So the augmented-run reading is an artifact of the proof, not the statement.

**Classification.** A genuine statement error in the constant's index (H+1). It is mild: the conclusion holds
whenever C is nondecreasing in H, which covers every use in the book (:184–198 with Õ(√(SAH³K))). The proof is
valid only for a different random object, the policies of the augmented run. There is a second, smaller gap in the
proof: the augmented MDP has S states only if s₀ reuses an existing state label. "Introducing … a single state s₀"
read as a fresh state gives S+1, and then C_{S+1,A,H+1}. Also, "single action a₀" must be read as A identical
actions to stay in the (S,A,H+1) class. Record both in C46.

**Faithful reading and weakest correction.** Faithful reading: π̂ is drawn from the run on the given MDP, and C is
the function in the hypothesis. Under that reading the printed statement is false. The minimal edit, C_{S,A,H+1} →
C_{S,A,H}, gives a *stronger* true statement, proved directly with no augmentation. The alternative minimal
repair keeps the printed constant and adds "C_{S,A,H} ≤ C_{S,A,H+1}". **The proposed pair is right:**
`Eq_PAC_from_regret_conversion_corrected` (constant at H) is the main entry, and `..._restricted` (monotone C,
printed constant) is a corollary. The deferred augmented-run formalization is optional. Do not call it "the
original theorem".

**Start-state independence lemma: sound under the protocol, and in the Lean model.** Protocol (i) draws s₁ᵏ i.i.d.
from ρ. Protocol (ii) chooses π^k "based on the information collected in episodes 1 through k−1". So π^k is
independent of s₁ᵏ, and E[V(s₁ᵏ) − V^{π^k}(s₁ᵏ)] = E[V(ρ) − V^{π^k}(ρ)]. No reading of (ii) lets π^k see s₁ᵏ. (If it
could, the claim would fail: a policy optimal only at the realized s₁ᵏ gives zero regret and a large ρ-gap. That is
why this lemma is essential and not a technicality.) In Lean, `onlineInitialVectorLaw` is the product of the ρ's
(SequentialEpisodeDefinitions.lean). `onlineEpisodicChoose` deploys `planner (history.take ((len/H)*H))`, and
`onlineEpisodicCurrentState` reads `initial ⟨len/H⟩` only at episode boundaries, and the stored terminal successor
is never reused (EpisodicSelectorDefinitions.lean:14–33). So the length-kH prefix depends on `initial j` only for
j < k. The planned prefix-marginal, congruence and product-split route is sound. The main risk is engineering, as
the plan says.

**Required fixes for (d).**
1. **Algorithm class disclosure.** A finite `Seed` mixing deterministic causal planners covers algorithms whose
   internal randomness is finitely supported and whose *deployed policies are deterministic Markov* given the seed
   and history. The source protocol allows stochastic π^k (a_h^k ~ π_h^k(·|s), :35–38). Kuhn purification shows that
   the *regret hypothesis* is unchanged. The *conclusion*, however, would then concern the purified deterministic
   policy, which is a different object from the randomized π^k. So the entry is also restricted in algorithm class.
   State this in the `_corrected` docstring ("deployed policies deterministic given seed and history; finitely
   supported internal randomness") and add a line under Statement-index scope disclosures. The finite seed is
   otherwise acceptable (Q8).
2. **Drop `δ < 1`.** The printed statement has no upper bound on δ, and for δ ≥ 1 the claim is trivial
   (1−δ ≤ 0 ≤ probability). Keeping `δ < 1` makes the entry conclude less than printed, without disclosure. Use
   `0 < δ` only. The `α ∈ [0,1]` premises are printed, so keep them even though they are unused.
3. The J-average form `ν.expectation (ω ↦ (1/K) Σ_k (law ω).rowMeasure.real {…})` is the joint probability of
   (seed, run, J) and is self-contained. Acceptable (Q8). Ch5.lean:33 already provides the `⊤` instance and the
   `rowMeasure.real` precedent (Ch5.lean:51). Say in the docstring that the hypothesis is assumed only at the given
   instance (H, E, ρ, K). That is weaker than the printed "for any MDP", so the entry implies the printed form,
   with the constant changed.
4. C46 text: the counterexample (with the C > 0 variant), the known-reward dependence, the run-identity issue, the
   s₀ state-count and a₀ caveats, both true versions, and the note that the augmentation is unnecessary under
   :25–33. Mark it "paper computation, not formalized" unless a Lean refutation is added. A Lean refutation is
   optional. It would need regret bounds over all classes (S = 1 myopic optimality plus trivial bounds), about 250
   lines. It is not required for this batch.
5. Coverage note: the follow-up claim at :184–198 (δ = 1/log(SAH), K = Θ̃(SAH³/ε²), and the slip "V₁⋆(s)" for
   V₁⋆(ρ)) is **not** covered by this item. List it as remaining.

---

## 2. Remark 4.3 (MF:2088–2090)

The source says the bound can be "readily translated into a bound on the expected ℓ∞ error with essentially the
same sample complexity … omit the details". It has no formula. The plan's precise reading mirrors Remarks 4.1/4.2:
δ := ε(1−γ)/2 inside Thm 4.12's budget, giving E max|Q_T − Q⋆| ≤ ε(1−δ) + δ/(1−γ) ≤ 2ε, with a fresh ∃c₁ ∃c₂.
**Faithful**: "As before" points explicitly at 4.1/4.2, and enlarging c₂ is within "essentially the same".

**`_corrected` (C34) is right, not a scope note.** Under Thm 4.12's printed premises the precise reading is false on
paper. Take S = A = 1, γ = 1/2, r = 1, Q₀ = 0, μ_min = 1, t_mix = 0, T = 1, ε = 1/2 (δ = 1/8). Then log³T = 0, so the
budget is 0 ≤ 1 and η = 0. So Q₁ = Q₀ and E err = 2 > 1 = 2ε. Add the same caveat as C34(1): read with η_t ∈ (0,1)
from :1951, the instance is ill-posed. The μ_min = 0 failure is inherited as in C34(2). Proof-plan checks: c₂ := max
c₂⁰ 1 is monotone-safe because the bracket and L² are ≥ 0 and μ_min > 0. η ≤ 1 from the budget holds, since
L ≥ log 4 > 1 because 2SAT/(ε(1−γ)) ≥ 4 for ε ≤ 1 and γ ≥ 1/2. GO. The docstring must say that the remark has no
displayed formula and that the precise form is the checker-confirmed reading. Add one sentence to C34.

---

## 3. Remark 7.1 (robust_RL:361–372)

- **Õ reading** `c_opt (1−γ)² L / N` with L = log(SAN/((1−γ)δ)): correct. It matches the commented factor at :367,
  and L dominates the other logs (N, 1/(1−γ)). Higher powers L^k (k ≥ 2) must **not** be admitted. With N at the
  threshold, the planning contribution is ≈ c_opt (1−γ)³ m ε² L^{k−1}/C₂, which is unbounded as δ → 0 (e.g. m = ε = 1,
  γ = 1/4). The remark would be false, so the plan's "no" is right.
- **∀ c_opt ∃ C₂**: correct. The reverse order is false. The scalar check holds: Ξ ≤ c_opt(1−γ)⁴mε²/C₂ ≤ c_opt/C₂, and
  Ξ/(1−γ) ≤ c_opt(1−γ)³mε²/C₂ ≤ c_opt ε/C₂, because mε ≤ √m ≤ 1 (m ≤ 1 since σ < 1 and 1−γ ≤ 3/4). The claim that the
  non-planning terms are about 0.24ε is **not verified here**. Ξ also enters `selfBoundExpr` through √(1+Ξ)
  (GapBound.lean:25), and with Ξ ≤ 1 instead of ≈ 0 that term grows by up to √2. The builder must re-derive the
  slack. Fallback if it is short: raise the base constant (10⁶ → larger), which shrinks every statistical term. Do
  not weaken the conclusion.
- **Deterministic outputs: `_restricted`, not merely a scope note.** V^{⋆,σ} is a sup over stationary randomized
  policies (Thm7_2_corrected docstring, Ch7.lean:438). The remark speaks of any planner output π̂, so excluding
  randomized π̂ narrows the hypothesis class. The precedent `Thm3_2_approxPlanner_positiveN` is likewise
  deterministic-only. Keep `Remark7_1_restricted`, pointing to the scope-disclosures section, and mention `N > 0`
  (`hN`) there too, as for Thm 7.2.
- **Uniform-over-f event**: right (Q6). It is stronger than the `pick` form, covers any data-dependent planner, and
  needs no measurability of f (the `⊤` σ-algebra). The one-sided hypothesis is equivalent to the printed ‖·‖∞ since
  V̂⋆ ≥ V̂^f. Either is fine. Prefer `|·|` to mirror the source, or say "equivalent" in the docstring.
- The residual lemma ξ ≤ YB − Z (via policyFix ≤ optFix and rowInf monotonicity) is sound in outline.

---

## 4. Remarks 4.1, 4.2, eq 2.27/2.28

**4.1/4.2.** Both are true. The drafts match `Thm4_1` (Ch4.lean:25, rate on 1 ≤ t ≤ T with log²T) and `Thm4_6`
(Ch4.lean:143, rate on k ≤ T with log³T). With δ = ε(1−γ)/2 ≤ 1/2, the scalar chain is
ε − εδ + ε/2 ≤ 2ε. Entry names `Remark4_1` and `Remark4_2` are right.
- Q1: a self-contained Prop cannot refer to another Prop's witnesses, so `∃ c₁ c₂ c₃` in Thm 4.1's order *is* the
  "same constants" reading. The docstring should say the proof reuses Thm 4.1's witnesses. Keep it (do not add a
  separate fresh-only c₃ variant).
- Q2: keep the five-part conclusion (it is the printed chain, and `Integrable` blocks the Bochner junk value).
- The η 0 detail for 4.1 (`tdIterate_bounds` needs k = 0) is correctly identified. Do not edit `tdIterate_bounds`.

**eq 2.27/2.28.** Both are true, and the labels are verified at prelim:614 and :636 (typo "perturbabtion" in the
source). `Eq_QV_pi_perturbation_r_inf` and `Eq_QV_star_perturbation_r_inf` are fine; the docstrings should quote the
exact labels.
- **Import layering, blocking as drafted.** `scripts/gates/g2_statement_imports.txt` is a frozen,
  *shrink-only* allowlist (static_gates.py:474–496). Any new `Formalization.*` import in `Statements/Ch2.lean` fails G2
  unless `--allow-grow` is used with a justification. Ch2.lean currently imports 11 `Formalization.*` modules (not all
  `*Definitions`: e.g. `BernsteinMatrixMarginals`, `RandomFamilyBorel`). `MDP/InfiniteReturn.lean` (12 theorems) and
  `MDP/ForcedActionReturn.lean` (3) are proof-bearing, so importing them also conflicts with AGENTS ("definition
  modules only"). Ch3Definitions and Ch6 are precedents, but they are already-frozen edges and not licences to grow.
  **Fix (recommended): use the Ch2 convention.** Ch2 already imports `FixedPointDefinitions`, and `Lemma2_1` states
  Q^π as `M.policyFixedPoint π` and Q⋆ as `M.optimalityFixedPoint`, with a docstring noting the separately proved
  identification with trajectory values. State eq 2.27 with `policyFixedPoint` (V^π s := (π s).expectation (Q^π s ·))
  and eq 2.28 with `⨆ π, M.policyFixedPoint π s a`, which keeps the printed max_π, or with `optimalityFixedPoint`.
  That adds no new edge. If trajectory values are insisted on, the lead must explicitly approve
  `--allow-grow` for two proof-bearing edges. Not recommended.
- The ⨆ encoding (Q4) is acceptable with the docstring note that the suprema are attained and bounded. With fixed
  points, the proof needs `policyFixedPoint ≤ optimalityFixedPoint` and attainment by a greedy policy. Find the
  existing lemmas (PolicyIteration / fixed-point modules) before writing new ones.

---

## 5. Batch order and sizes

> The (d) bullets below concern an item that has since been built, critic-reviewed and integrated (C46; see `critic-regret-pac.md`).

The order (b) → (a) → (c, stretch) for one builder, with (d) separate, is right. The sizes are plausible. Adjustments:
- Settle the (b) import decision before the builder starts. It changes the proof route from trajectory-value
  lemmas to fixed-point identification lemmas, so give (b) +30–50 lines.
- (d) can now be scheduled: this check settles Q5–Q9. C46 is a lead/ledger task, done before the entry lands.
  The 550–750 line estimate stands. Keep the 2-hour stall rule for the reset-freshness lemma, but the augmented-run
  fallback must then be labelled as a *different* reading, not the corrected entry.
- (c) carries the main numeric risk (√(1+Ξ) slack). Budget extra compiles there.

## Answers to the plan's open questions

1. Yes: the same ∃ order as Thm 4.1/4.6, and the proof reuses their witnesses. No fresh-only variant.
2. Keep all five parts.
3. Faithful. `_corrected` → C34, with the T = 1 counterexample above.
4. ⨆ is fine. Do **not** import ForcedActionReturn/InfiniteReturn into Ch2. Use policyFixedPoint/optimalityFixedPoint.
5. Yes: one L factor, ∀ c_opt ∃ C₂, no L^k. Deterministic outputs → `_restricted`.
6. Uniform-in-f.
7. (Item (d); since built, critic-reviewed and integrated: C46.) The natural reading (the original run) is the printed claim. The counterexample is valid: H-dependence and the
   known reward are allowed, and it is robust to C > 0.
8. (Item (d); since built, critic-reviewed and integrated: C46.) The finite seed is acceptable *with* the deterministic-deployed-policy disclosure. The J-average form is fine.
9. (Item (d); since built, critic-reviewed and integrated: C46.) Confirmed: π^k cannot see s₁ᵏ under :25–33, and the Lean selector enforces this.
