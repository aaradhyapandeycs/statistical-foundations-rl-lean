# Critic report: `Lemma6_11_restricted` (`lemma:useful`)

Public copy of the independent critic report; local paths removed.

- Date (UTC): Fri Nov  6 17:03:19 UTC 2026 (from `date -u` at review start)
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106` (working tree has uncommitted changes to the files under review; `LCBQUsefulSeries.lean` is untracked)
- Mode: source-only review; no Lean compiled; axiom audit not run.
- Independence: `docs/PROGRESS.md`, `docs/COVERAGE.md`, other critic reports and other private working files were not read. `docs/SOURCE-ISSUES.md` was read only after the reconstruction and comparison below were complete, and only lines 385–420.

## 1. Files read and pin check

All pinned `.tex` hashes match `source/provenance.json`. The four brief-time hashes are unchanged.

| File | SHA256 | Pin / brief | Lines inspected |
|---|---|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` | matches pin and brief | 1620–1860, 2270–2310, 4665–4830; theorem-environment scan of lines 1–2300 |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | matches pin | 45 (γ ∈ [0,1)), 120–175 |
| `source/upstream/tex/chapters/intro.tex` | `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a` | matches pin | 192 (meaning of `≲`) |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | matches pin | hashed only, not read |
| `source/upstream/tex/StatisticalRL-nowplain.tex` | `5a925ce6a5a988bdc4b8631c5b3f985195f58b9fec80cc1f3d80c6cd10aea956` | matches pin | grep `newtheorem` (lines 60, 62) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | n/a | pin entries (lines 24, 30, 37, 39–41) |
| `Formalization/Statements/Ch6.lean` | `f9fb13de3797e0d240635b31e3ee12cca72eded02874ba03729eb21922eb7d5e` | matches brief | 1–40, 180–211; `git diff HEAD` |
| `Formalization/Statements/Ch6Proofs.lean` | `d80a704b5693f0181a8b6f2df3c9bd3169eadfc87506392e51995b169b147542` | matches brief | 1–20, 90–105; `git diff HEAD` |
| `Formalization/OfflineRL/LCBQUsefulSeries.lean` (untracked) | `608077b8b523b84e62596b7e533308769cafaf0db67ab29b8e37280c9172e00d` | n/a | 1–247 (whole file) |
| `Formalization/MDP/CoreDefinitions.lean` | `68bf277b85a22ce7f2e8aee6f4ebc2bb3e06c6eb8b047519a79f0a468c1d4102` | n/a | 1–45 |
| `Formalization/MDP/DiscountedOccupancy.lean` | `029a6c51d60dfd7e637ec212394354a7471afcfd1bbf9ddf03b432b9e0bf9606` | n/a | 1–110 |
| `Formalization/MDP/DecisionStageDefinitions.lean` | `b6dbe41ebb33004ca0ff9c678e425cca6c1b59f4b3dcb5e2862463106c4b2b31` | n/a | 1–30 |
| `Formalization/MDP/FiniteOccupancy.lean` | `ad542b90fe2daeeaa93696f00fe763c7ca1e428042f769be7fd728c5657ab8d0` | n/a | 1–60 |
| `Formalization/MDP/DiscountedFiniteTrajectory.lean` | `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6` | n/a | 55–80 |
| `Formalization/MDP/Basic.lean` | `bf3db557ee22cf1894d442326794ab2bea0e8521680a996b72484b2935e7dc78` | n/a | 60–100, 125–150 |
| `Formalization/MDP/OptimalTrajectoryValue.lean` | `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7` | n/a | 1–80 |
| `Formalization.lean` | `697052168941c159e83d54a657a736da1d37e74290ab7f51ce6e04bf3b0e90a1` | n/a | grep: lines 106, 704, 705 |
| `docs/SOURCE-ISSUES.md` | `3d113729e6b40874e1692cb9f3d55f02bf701c2ae5e95431f0791c3c28014b9a` | matches brief | 385–420, read last |
| Mathlib `Analysis/Normed/Group/Constructions.lean` (pinned 32d24245) | `7943f273c08767160be6e519b44c72ff9b89e90c0f8362a61f8bce26427313ab` | n/a | 301 (Pi norm), 344 |

## 2. Source reconstruction (before reading any Lean)

**Setting (offlineRL.tex:1638–1860; prelim.tex:45, 136–175).**
- There are finitely many states and actions, with S = |𝒮| and A = |𝒜|. The discount is γ ∈ [0,1) (prelim:45).
- T is the number of LCB-Q iterations, a positive integer. δ ∈ (0,1).
- H := ⌈(4/(1−γ)) · log(SAT/δ)⌉ (`eq:defn-H-lcbq-stepsize-proof`, 1669–1672), and ι := log(SAT/δ) (1849–1851).
- The learning rate η_n = (H+1)/(H+n) and the bonus b_n are defined but are **not used by the lemma**.
- π⋆ is "at least one deterministic policy, denoted by π⋆ throughout", that is optimal (prelim:136). It is an arbitrary but fixed optimal deterministic policy.
- P_{π⋆} is the state-to-state transition matrix under π⋆. ρ ∈ Δ(𝒮) is the test distribution of Theorem 6.8. d_ρ^⋆(s) = (1−γ) Σ_t γ^t P(s_t = s | s_0 ∼ ρ, π⋆) (prelim:150, 166).
- `≲` means ≤ C₁ times the right side, for a universal constant C₁ > 0 that is independent of S, A, 1/(1−γ), H, 1/ε and 1/δ (intro:192).

**κ (2284–2289).** κ := γ(1+1/H)³, and the book says κ < 1 "follows immediately from the choice of H". This text sits inside the proof of Theorem 6.8 (`theorem:lcbq`, 1754–1776; by the shared counter it is Theorem 6.8 and `lemma:useful` is Lemma 6.11).

**Printed claim (2292–2300).** For any 0<δ<1, and with H and κ as above, every W ∈ ℝ^S with nonnegative entries satisfies

Σ_{j≥0} κ^j ρᵀ(P_{π⋆})^j W ≲ (1/(1−γ))⟨d_ρ^⋆, W⟩ + δ/(S T⁴ (1−γ)) ‖W‖_∞.

**Proof (4674–4783).**
1. Split the series at K = H. Before the split, κ^j ≤ (1+1/H)^{3K} γ^j ≤ e³ γ^j.
2. The main term is Σ γ^j ρᵀP^jW = ⟨d_ρ^⋆, W⟩/(1−γ).
3. For the tail:
   - The tail is at most κ^K/(1−κ) · ‖W‖_∞, using ρᵀP^j ∈ Δ(𝒮) and W ≥ 0.
   - γ^H ≤ exp(−H(1−γ)) ≤ δ/(ST⁴).
   - The book asserts 1−κ ≳ 1−γ ("a little algebra").

**Implicit assumptions and ambiguities found independently.**
- **A1.** The lemma is pure Markov-chain algebra. Optimality of π⋆ is never used, so the bound holds for every stationary policy. Rewards play no role.
- **A2.** κ < 1, and the uniform bound 1−κ ≳ 1−γ, do **not** follow from the choice of H alone. They need log(SAT/δ) bounded below. With S=A=T=1, δ=0.9 (ι≈0.105) and γ=0.3, H=1 and κ=2.4: the series diverges for W≡1, so the left side is +∞.
- **A3.** With S=A=T=1, δ=0.9 and γ = 1/8 − η, H=1 and κ = 1−8η < 1. The left side is 1/(8η), which tends to ∞. The right side is ≤ 2.172·C₁. So **no universal constant exists**, and the printed lemma is false when read as a standalone statement ("any 0<δ<1"; numerically, at η = 1e-6 the ratio of the left side to C₁⁻¹ times the right side is ≈ 5.8·10⁴).
- **A4.** κ < 1 holds for every γ only when ι is roughly above 3/4 (numerical sup over γ: ι=0.70 gives sup κ ≈ 1.0018; ι=0.76 gives sup κ < 1). A γ-uniform constant needs ι bounded strictly above that threshold.
- **A5.** Inside the proof of Theorem 6.8, the sample-size condition `eq:sample-size-lcbq-T-thm` with c₂ large does rescue the *conclusion*:
  - If ι < 1, then SAT ≤ 2, so T ≤ 2.
  - Using ε ≤ 1/(1−γ), S, C⋆ ≥ 1 and log(SAT/((1−γ)δ)) ≥ log(1/(1−γ)) ≥ γ, the condition gives 2 ≥ T ≥ c₂γ. Hence κ ≤ 8γ ≤ 16/c₂.
  - It does **not** imply ι ≥ 1. For example, S=A=T=1, γ=0, C⋆=1, ε=1 and δ ∈ [e^{−1/c₂}, 1) satisfy the sample-size condition (1 ≥ c₂ log(1/δ)), but ι = log(1/δ) ≤ 1/c₂ < 1.
- **A6.** The term γ^H ≤ (δ/(SAT))⁴ ≤ δ/(ST⁴) holds for every δ ∈ (0,1). Only the κ steps depend on the size of ι.

## 3. Field-by-field comparison: source vs `Lemma6_11_restricted` (Ch6.lean:197–210)

| Item | Source | Lean | Verdict | Lean location |
|---|---|---|---|---|
| Universal constant for `≲` | ∃ universal C₁ > 0 | `∃ C : ℝ, 0 < C ∧ ∀ S A M ρ δ T W, …`, with ∃ outside all model and parameter quantifiers | match | Ch6.lean:198–199 |
| Witness for C | n/a | 84 (wrapper) | n/a | Ch6Proofs.lean:102 |
| State and action spaces | finite 𝒮, 𝒜, with S, A their sizes | `Fintype S`, `Fintype A`; `DiscountedMDP` forces both nonempty | match | Ch6.lean:199; CoreDefinitions.lean:30–32 |
| γ | [0,1) | `M.discount`, with `discount_nonneg` and `discount_lt_one` | match | CoreDefinitions.lean:37–39 |
| Rewards | in [0,1] (the lemma does not use them) | in [0,1] (only enter through `optimalGreedyPolicy`) | match (see N1) | CoreDefinitions.lean:34–36 |
| δ | 0<δ<1 | `0 < δ → δ < 1` | match | Ch6.lean:201 |
| T | positive integer | `T : ℕ`, `1 ≤ T` (already implied by the ι premise, since log 0 = 0) | match | Ch6.lean:201 |
| ι = log(SAT/δ) ≥ 1 | **absent** (κ<1 asserted from H alone) | `1 ≤ Real.log (card S * card A * T / δ)` | **added premise (the restriction)** | Ch6.lean:202 |
| H | ⌈4/(1−γ) · log(SAT/δ)⌉ | `⌈4 / (1 - γ) * Real.log (…)⌉₊`; Nat.ceil of a positive real equals the integer ceiling | match | Ch6.lean:205 |
| κ | γ(1+1/H)³ | `γ * (1 + 1 / (H : ℝ)) ^ 3`; H ≥ 4 under the premises, so no division by zero | match | Ch6.lean:206 |
| W | W ∈ ℝ^S, entries ≥ 0 | `W : S → ℝ`, `∀ s, 0 ≤ W s` | match | Ch6.lean:200, 203 |
| ρ | ρ ∈ Δ(𝒮) | `FiniteDistribution S` (nonnegative, sums to 1) | match | CoreDefinitions.lean:15–18 |
| π⋆ | an arbitrary fixed optimal deterministic policy | `M.optimalGreedyPolicy` (a point mass on a `Classical.choose` maximiser of the Bellman-optimal Q fixed point) | narrower object, not narrower in substance (N1) | OptimalTrajectoryValue.lean:21–34 |
| ρᵀP_{π⋆}^j | time-j state law | `occupancyStateAt π ρ j s` = `stateAfter (replicate j (stationaryStage π)) ρ`, one step = `ρ.bind (s ↦ (π s).bind (M.transition s))` | match | DiscountedOccupancy.lean:16–32; FiniteOccupancy.lean:23–27; Basic.lean:77–86 |
| Left side | Σ_j κ^j ρᵀP^jW, in [0,∞] | `∑' j, κ^j * ∑ s, occ_j(s) * W s` (a real tsum; non-summable gives 0). Under the premises κ ≤ 1−(1−γ)/4 < 1, so it is summable and no junk value is exploited | match under the premises | Ch6.lean:207 |
| d_ρ^⋆ | (1−γ) Σ_t γ^t P(s_t=s) | `discountedStateOccupancy π ρ s = (1 - γ) * ∑' t, γ^t * occ_t(s)` (summable) | match | DiscountedOccupancy.lean:62–64, 71–79 |
| ⟨d, W⟩/(1−γ) | as printed | `(∑ s, d s * W s) / (1 - γ)` | match | Ch6.lean:208 |
| ‖W‖_∞ | sup norm | `‖W‖`, the Pi sup norm `Finset.univ.sup ‖W b‖₊` | match | Mathlib Constructions.lean:301 |
| Tail coefficient | δ/(S T⁴ (1−γ)) | `δ * ‖W‖ / (card S * T^4 * (1 - γ))` | match | Ch6.lean:209 |

**What the restriction is.** The only difference from the printed statement is the added premise `log(SAT/δ) ≥ 1`. Everything else is either the source's own object or provably equivalent (see N1).

**Is the restriction the minimum needed?**
- *Some* restriction is necessary. Without it the printed claim is false: there is no universal constant (A3), and the left side can be +∞ (A2). Lean's real-valued `tsum` would turn the +∞ cases into 0, but the A3 family is summable and still breaks every constant.
- `ι ≥ 1` is a clean sufficient condition but **not minimal**. It also excludes true instances:
  - γ = 0 with ι < 1: κ = 0, and the bound holds with C = 1.
  - In the Theorem 6.8 corner of A5, the conclusion holds.
- The exact feasible region for a fixed C has no clean closed form, so the choice is acceptable, but it should be described as sufficient, not necessary (F2).

## 4. Findings

- **F1: MAJOR. The disclosure falsely states that the added premise follows from Theorem 6.8's sample-size condition.**
  - Where it appears:
    - `docs/SOURCE-ISSUES.md:399–400`: "in the source the premise follows from the standing sample-size condition of Theorem 6.8".
    - `Ch6.lean:194–195`: "in the source it is implied by the standing sample-size condition of Theorem 6.8".
    - `LCBQUsefulSeries.lean:12–14`: "in the source it follows from the standing sample-size condition of the enclosing theorem".
  - Counterexample: S=A=T=1, γ=0, C⋆=1, ε=1 (= 1/(1−γ), allowed), and any fixed universal c₂ > 1. Then `eq:sample-size-lcbq-T-thm` reads 1 ≥ c₂ log(1/δ). This holds for every δ ∈ [e^{−1/c₂}, 1), yet ι = log(1/δ) ≤ 1/c₂ < 1.
  - What is true: for large c₂ the sample-size condition implies κ ≤ 16/c₂ in the ι<1 corner, so the lemma's *conclusion* holds there (A5). The *premise* ι ≥ 1 does not hold there.
  - Consequence: `Lemma6_11_restricted` does not cover every parameter tuple at which Theorem 6.8's proof invokes Lemma 6.11. These are tuples with SAT ≤ 2 and δ > SAT/e. A future Theorem 6.8 formalization that relies on the stated rationale would find the premise unavailable and need a separate argument for that corner.
  - Why not BLOCKING: the Lean difference itself (the added premise) is disclosed accurately.
  - Fix: replace the rationale with an accurate one. For example: "ι ≥ 1 is a sufficient condition. In Theorem 6.8 with c₂ large, ι < 1 forces SAT ≤ 2 and γ ≤ 2/c₂, a corner this entry does not cover."

- **F2: MINOR. The disclosure and the docstrings overstate the premise as necessary.**
  - Where it appears:
    - SOURCE-ISSUES:397–398: "this needs `log(SAT/δ) ≥ 1`".
    - Ch6.lean:194: "κ < 1 holds only when log(SAT/δ) ≥ 1".
    - LCBQUsefulSeries.lean:12: "gives only when".
  - Counterexample: S=A=T=1, δ=0.9 (ι≈0.105) and γ=0.1 give H=1 and κ=0.8 < 1. Uniformly in γ, κ < 1 needs only ι ≳ 3/4 (A4).
  - Fix: write "is guaranteed by the choice of H when log(SAT/δ) ≥ 1" or similar.

- **F3: MINOR. The disclosure frames the issue as only a formalization limitation, although the printed standalone lemma is false.**
  - The SOURCE-ISSUES section header says these are "not asserted errors in the manuscript". The disclosure records counterevidence only against the "κ<1 immediately" step (its κ=4 example).
  - The printed Lemma 6.11 says "Consider any 0<δ<1" with no reference to Theorem 6.8's sample-size condition. Read that way, it is false:
    - S=A=T=1, δ=0.9, γ=0.3 gives H=1, κ=2.4, and the left side is +∞ for W≡1.
    - γ = 1/8−η gives a left side of 1/(8η) against a right side ≤ 2.18·C, so no universal constant exists.
  - Under AGENTS.md ("A source error is an open obligation. Record counterevidence…"), the disclosure should either:
    - state that the standalone printed claim fails and that the book implicitly relies on the Theorem 6.8 context (correctly described, per F1), or
    - explicitly justify why it is not treated as a source error.

- **N1: NOTE. π⋆ is `M.optimalGreedyPolicy` rather than "any optimal deterministic π⋆". This is not a weakening.**
  - The conclusion depends only on (transition, γ, policy, ρ), not on the reward, and the entry quantifies over all `DiscountedMDP`.
  - So for any kernel P, any γ and any deterministic π, take the reward r(s,a) = 1{a = π(s)} ∈ [0,1].
    - Then Q⋆(s,a) = 1{a=π(s)} + γ/(1−γ), so π(s) is the unique maximiser.
    - The `Classical.choose` maximiser in `optimalGreedyAction` must therefore equal π(s).
    - So `optimalGreedyPolicy` = π, and the entry yields the bound for π.
  - Hence the entry implies the printed bound for every deterministic policy, and in particular every optimal π⋆.
  - The provider `lcbq_useful` is stated for every stationary (even randomized) policy, so the index could state `∀ π` at no cost.
  - Not disclosed; no disclosure is needed. This argument is not formalized (needs Lean-side confirmation if anyone relies on it).

- **N2: NOTE. Constant 84.** SOURCE-ISSUES says "constant 84". The index entry is existential (`∃ C > 0`, outermost) and the wrapper supplies 84. Both are faithful. The provider's arithmetic checks out by hand:
  - (1+1/H)^{3H} ≤ e³ < 21;
  - 1−κ ≥ (1−γ)/4, by expanding (1−x)(1+x/4)³ = 1 − x/4 − 9x²/16 − 11x³/64 − x⁴/64;
  - γ^H ≤ (δ/(SAT))⁴ ≤ δ/(ST⁴);
  - therefore the tail is ≤ 84 δ‖W‖/(ST⁴(1−γ)), the head is ≤ 21⟨d,W⟩/(1−γ), and 21 ≤ 84.

- **N3: NOTE. Junk values.** None are exploited:
  - the log argument is positive;
  - Nat.ceil's argument is positive;
  - every denominator is positive (H ≥ 4, γ < 1, S, T ≥ 1);
  - the `tsum` is summable under the premises.

  The statement does not record summability explicitly, but it follows mathematically from the premises.

- **N4: NOTE. Import hygiene (not specific to this lemma, partly introduced by this diff).**
  - `Ch6.lean` imports `Formalization.Probability.FiniteSampleDefinitions` twice (lines 7 and 9); the second copy was added in this diff.
  - It also imports `Formalization.MDP.DiscountedOccupancy` and `Formalization.MDP.OptimalTrajectoryValue`, which contain theorems. AGENTS.md says ChN.lean "imports definition modules only". This import pattern predates this change.

- **N5: NOTE. Citations are accurate.** `2292–2300` is exactly the lemma environment. `:4674–4785` is the proof subsection (the text ends at 4782 and the next subsection starts at 4786). `:1667–1672` is the `subequations` label through the H equation.

## 5. Provider chain

Theorem 6.11 wrapper `Lemma6_11_restricted_holds` (Ch6Proofs.lean:101–103):
- It provides `⟨84, by norm_num, fun S A _ _ M ρ δ T W hδ hδ1 hT hι hW => lcbq_useful M M.optimalGreedyPolicy ρ δ T W hδ hδ1 hT hι hW⟩`.
- This is a direct application with no restatement and no second proof.
- The provider binds `L := Real.log (…)` as a `let`. The entry inlines it, so the two match only up to ζ-reduction (needs Lean-side confirmation that it elaborates).

Provider `StatisticalRL.OfflineRL.LCBQ.lcbq_useful` (LCBQUsefulSeries.lean:51–245):
- It is general in `π : StationaryPolicy`. Its premises are exactly the entry's (`hδ, hδ1, hT, hι, hW`); there are no extra premises.
- Its conclusion has the literal constant 84 in place of C.
- Its proof follows the source: split at H, the head via `hearly` (κ^j ≤ 21γ^j for j ≤ H), and the tail via `hκH` together with 1−κ ≥ x/4. It uses `hocc` (the occupancy identity, through `Summable.tsum_finsetSum`).
- Local dependencies, all genuine definitions with no fallbacks:
  - `occupancyStateAt` / `occupancyStateLaw` / `stateAfter` / `FiniteDistribution.bind`;
  - `discountedStateOccupancy` and `discountedState_summable`;
  - `optimalGreedyPolicy` (point mass on a `Classical.choose` maximiser of `optimalityFixedPoint`);
  - `DiscountedMDP` and `FiniteDistribution` structures with real probability obligations.
- Mathlib dependencies: `Real.add_one_le_exp`, `Real.exp_one_lt_d9`, `summable_geometric_of_lt_one`, `tsum_geometric_of_lt_one`, `Summable.sum_add_tsum_nat_add`, `Summable.tsum_le_tsum`, `norm_le_pi_norm`, `Nat.le_ceil`.
- No extra assumption, no weakened conclusion, no different object (beyond N1), and no fallback definition.

## 6. Forbidden-token grep

- I computed the local import closure of `Formalization.Statements.Ch6Proofs` (87 project files). That includes `Ch6.lean` and `LCBQUsefulSeries.lean` (whose own closure is 31 files).
- In all 87 files, a whole-word grep for `sorry admit axiom opaque implemented_by unsafe native_decide ofReduceBool`, plus `@[extern`, `skipKernelTC`, `debug.` and top-level `elab`/`macro`/`syntax`, found **no hits**.
- Both statement files are imported from `Formalization.lean` (lines 704–705), and the provider at line 106.
- The axiom audit (`lake env lean Audit.lean` / `scripts/check.py`) was **not run**, as instructed. The transitive axiom closure, including Mathlib, is therefore unverified by this review.

## 7. Items needing Lean-side confirmation

1. `Ch6Proofs.lean` and `LCBQUsefulSeries.lean` compile at the pinned toolchain. This includes the `field_simp; try ring` step at LCBQUsefulSeries.lean:139–141, and the wrapper's term-mode application matching the entry's `let` telescope up to ζ.
2. `#print axioms StatisticalRL.Statements.Ch6.Lemma6_11_restricted_holds` reports ⊆ {propext, Classical.choice, Quot.sound}.
3. `‖W‖` in the entry elaborates to the Pi sup norm (Mathlib `Pi.seminormedAddCommGroup`, Constructions.lean:301).
4. If anyone relies on N1, the reward-relabelling equivalence (`optimalGreedyPolicy` realises every deterministic policy) is unformalized.

## 8. Verdict

VERDICT: PASS-WITH-FINDINGS. The Lean entry states the printed Lemma 6.11 faithfully except for the one disclosed added premise `log(SAT/δ) ≥ 1`, and the provider derives it exactly. However, the disclosure's rationale falsely claims that the premise follows from Theorem 6.8's sample-size condition (MAJOR), overstates the premise as necessary, and does not record that the standalone printed lemma is false.

## 9. Judgement of the SOURCE-ISSUES disclosure (`docs/SOURCE-ISSUES.md:394–400`)

**Incomplete and partly wrong.**

What it gets right:
- It correctly identifies *what* differs: the explicit constant 84 for `≲` and the added premise `log(SAT/δ) ≥ 1`.
- Its counterexample (S=A=T=1, δ=0.99, γ=0.5 ⇒ H=1, κ=4) is correct.
- Its silence about π⋆ = `optimalGreedyPolicy` is acceptable (N1).

What it gets wrong or leaves out:
- **(i)** The claim that "in the source the premise follows from the standing sample-size condition of Theorem 6.8" is false. The counterexample is S=A=T=1, γ=0, C⋆=1, ε=1, δ ≥ e^{−1/c₂} (F1). The restricted entry therefore does not cover all of Lemma 6.11's in-context uses.
- **(ii)** "this needs `log(SAT/δ) ≥ 1`" presents a sufficient condition as a necessary one (F2).
- **(iii)** Placing it under "not asserted errors in the manuscript" omits that the printed lemma, read as stated ("any 0<δ<1"), is false. The left side can be +∞, and no universal constant exists (F3).
