# Critic report: Lemma 2.4 (Hoeffding inequality, `lem:Hoeffding-prelim`)

Public copy of the independent critic report; local paths removed.

- UTC timestamp: 2026-11-06T16:59:25Z
- Reviewer: independent Claude critic subagent (did not build this code)
- git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`
- Branch: `batch-ch2-ch3-ch6-20261106`
- Scope: source-only review; no Lean compiled; axiom audit not run.
- Note on what was reviewed: `def Lemma2_4` (Ch2.lean) and `theorem Lemma2_4_holds` (Ch2Proofs.lean)
  are **uncommitted working-tree additions** (`git diff HEAD` shows them as `+` lines; they are not in
  HEAD 6bac672). The provider files below are unmodified relative to HEAD. This review is of the working
  tree as hashed below.

## 1. Pin check

| File | SHA256 (computed) | Pin in `source/provenance.json` | Result |
|---|---|---|---|
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | `2d27bb72…42031a5` (line 41) | MATCH |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | `78f6f8b5…11f7df3` (line 30) | MATCH |

Verdict is not provisional on pin grounds.

## 2. Files read (SHA256 and inspected ranges)

| File | SHA256 | Inspected |
|---|---|---|
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | 890–975 (lemma 939–950); grep of lines 34, 38, 55; lemma/theorem environment list for numbering |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | grep: lines 7 (`\ind`), 111 (`\cA`), 114 (`\cS`), 119 (`\cV`), 226 (`\mymid`) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | lines 30, 41 (pins) |
| `source/upstream/tex/nowfnt.cls` | `d86c0a39f74ee1a27412e6bca1b00ce72f04c7fd575d3e6cc01c1221471ffbd2` | grep: 1331–1337 (`lemma` shares the `theorem` counter, per chapter) |
| `source/upstream/tex/StatisticalRL-nowplain.tex` | `5a925ce6a5a988bdc4b8631c5b3f985195f58b9fec80cc1f3d80c6cd10aea956` | grep: `\input` order (intro, prelim, …), `\newtheorem` lines 60, 62 |
| `Formalization/Statements/Ch2.lean` | `317cfdf8c6d482b3a87cf09e528e7e2a2a77063796bb02be17445ec36d55f86d` | 1–40 (imports, header), 195–240 (Lemma2_4 at 207–228) |
| `Formalization/Statements/Ch2Proofs.lean` | `a69420317ccfaa017a8fca7aa0b4c8c5dccc95996f86326a8c355b5edcd1868a` | 1–30, 105–139 (Lemma2_4_holds at 113–118) |
| `Formalization/Probability/RandomFamilyBorel.lean` | `1bda21b0bac900dc0dec5db6cef949dfc99a745dff4cce14f2a1a0732c57d335` | 1–190 (whole file) |
| `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean` | `d5434c422e8535a134cedf7a5ff66c8ad8db0f49c77c3c018b26ec52b26f5fa6` | 1–319 (whole file) |
| `Formalization/Probability/EmpiricalHoeffdingFamily.lean` | `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d` | 1–253 (whole file) |
| `Formalization/Probability/EmpiricalHoeffding.lean` | `fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55` | 1–142 (whole file) |
| `Formalization/Probability/EmpiricalRow.lean` | `12a24b4883e75ba3f6302573f46b7d7648f90052333dc1c1d268722964c9152b` | 1–89 (whole file) |
| `Formalization/Probability/FiniteSampleDefinitions.lean` | `baa436abfb5988ab409cec759899fe944a05a7cd64bcb07fd8a8899a85f1a772` | 1–45 (whole file) |
| `Formalization/Probability/EmpiricalRowMeasurableDefinitions.lean` | `fc40126e0beac16c94075094551b34ffe2700ce31d83721f179581fb4cde4275` | 1–6 (whole file) |
| `Formalization/MDP/CoreDefinitions.lean` | `68bf277b85a22ce7f2e8aee6f4ebc2bb3e06c6eb8b047519a79f0a468c1d4102` | 1–45 (whole file) |
| `Formalization/MDP/InfiniteTrajectory.lean` | `2a3c7f5a78c69378331eb6c28d4e459da8f45df463428557cfeb229187339371` | import lines only |
| `Formalization.lean` | `697052168941c159e83d54a657a736da1d37e74290ab7f51ce6e04bf3b0e90a1` | grep: lines 436–437 import Ch2 and Ch2Proofs |
| `Audit.lean` | `29f6cd54e69586325be78af79809bda1f1d1c2b0c52f03ad3746eb6e8c3d06f3` | 1–25 (audit covers every `StatisticalRL.*` constant; allows propext, Classical.choice, Quot.sound) |
| `AGENTS.md` | `1e28b54cc339575657234bd92b3e53f82c6d347ecd3bf37f0f000a4a4af12579` | (supplied as project instructions) |

Additionally, the full local import closures of `Formalization.Probability.RandomFamilyBorel` (21 modules) and of
`Formalization.Statements.Ch2Proofs` (149 modules) were grepped for forbidden tokens (Section 7).

## 3. Source reconstruction (written before opening any Lean file)

Setting (prelim.tex 915–936, paraphrased). `P : 𝒮 × 𝒜 → Δ(𝒮)` is a transition kernel on a finite state space
`𝒮 = {1,…,S}` (line 34). For each pair `(s,a)` one has `N` samples `s^{(i)}(s,a)`, `i = 1,…,N`, drawn
**i.i.d.** from `P(·|s,a)`. The empirical row is `P̂(s'|s,a) = (1/N) Σ_{i=1}^N 1{s^{(i)}(s,a) = s'}`, and
`P̂_{s,a}`, `P_{s,a}` (line 55: `P_{s,a} := P(·|s,a) ∈ ℝ^{1×S}`) are row vectors, so `P̂_{s,a} V`,
`P_{s,a} V` are inner products with a column vector `V ∈ ℝ^S`.

Lemma (lines 939–950, label `lem:Hoeffding-prelim`, printed as Lemma 2.4: prelim is Chapter 2, and the lemma
counter is shared with theorem/corollary per `nowfnt.cls:1331–1333`; the earlier Chapter 2 lemmas are at
lines 339, 458, 544, and line 597 is commented out).

- Random objects. One fixed `(s,a)`; only that row's `N` samples matter; their count is `N` (indices `1..N`).
  A finite set `𝒱 ⊂ ℝ_+^S` of vectors. The lemma's hypothesis "if `𝒱` is independent of `P̂_{s,a}`" only makes
  sense if `𝒱` may be **random**; then `|𝒱|` is a random cardinality. A deterministic `𝒱` is the special case.
- Hypotheses.
  - Independence: the `N` samples of row `(s,a)` are mutually independent and identically distributed with law
    `P(·|s,a)`. `𝒱` (as a random element) is independent of the **empirical row `P̂_{s,a}`**, not necessarily
    of the ordered samples, and nothing is said about the other rows.
  - Boundedness: each `V ∈ 𝒱` lies in `ℝ_+^S`. `ℝ_+` is not defined anywhere in the source (grep finds only
    the three lemma uses). Either reading (nonnegative or positive) makes `V(s^{(i)}) ∈ [0, ‖V‖_∞]`, which is
    the closed range Hoeffding needs with range length `‖V‖_∞`. Without the sign condition the printed constant
    would be wrong (the range could be `2‖V‖_∞`).
  - Measurability: unstated (implicit).
  - `0 < δ < 1` (open interval, explicit).
  - Implicit: `N ≥ 1` (division by `N`, and the definition of `P̂`); `S ≥ 1` (`Δ(𝒮)` nonempty); `𝒱` may be
    empty (then the claim is vacuous, and `log(0)` is never evaluated).
- Conclusion. With probability **strictly greater than** `1 − δ`, the event
  "`|(P̂_{s,a} − P_{s,a})V| ≤ sqrt(‖V‖_∞² · log(2|𝒱|/δ) / (2N))` for all `V ∈ 𝒱` simultaneously" holds.
  The inner inequality is non-strict (`≤`). The constants are: a factor 2 inside the log (two-sided tail) times
  `|𝒱|` (union-bound multiplicity), `2N` in the denominator, `‖V‖_∞²` in the numerator, and the natural log.
- Truth of the printed form (my reconstruction). Write `X_i = V(s^{(i)}) ∈ [0, ‖V‖_∞]`. Hoeffding gives
  `P(|X̄ − PV| ≥ t) ≤ 2 exp(−2Nt²/‖V‖_∞²)`; with `t` equal to the printed radius this is `δ/|𝒱|`, and the union
  bound gives failure `≤ δ`. The **strict** "greater than" also holds. Hoeffding's lemma is strict for
  `λ ≠ 0` when the range is positive, or one can use the finite sample space to get a positive gap. A vector with
  `‖V‖_∞ = 0` contributes an empty failure event. So the total failure is `< δ`. For random `𝒱` independent of
  `P̂_{s,a}`, condition on `𝒱` and integrate a function that is strictly below `δ`, which gives a strict
  inequality. So the printed statement is correct as written (under the implicit `N ≥ 1`).
- Source defects noticed. Cosmetic only: the display at line 945 opens with `\big(` and closes with a plain `)`,
  which is a mismatched delimiter size and has no mathematical effect. `ℝ_+` is undefined. Measurability of
  `𝒱` is not stated. None of these is a mathematical error.

## 4. Lean statement (Ch2.lean:207–228) versus the source, field by field

Mathlib semantics I rely on (**assumed from Mathlib knowledge, needs Lean-side confirmation**):
- `‖V‖` for `V : State → ℝ` is the Pi sup norm `sup_s |V s|`. The provider uses `norm_le_pi_norm`
  (EmpiricalHoeffding.lean:122), which is consistent with this.
- `μ.real A = (μ A).toReal`.
- `IndepFun f g μ` is independence of `comap f mβ` and `comap g mγ` under `μ`.
- `MeasurableSpace.map f m` is the pushforward σ-algebra `{A | MeasurableSet (f⁻¹' A)}`, and `⨅` of
  σ-algebras is their intersection.
- `letI` in term mode inlines the instance.
- `binop%` elaboration casts `N` and `card` to `ℝ`. Even if the products were computed in `ℕ` first, the value
  would be the same, because no `ℕ` division occurs: both divisions have a real operand (`δ`, or a real
  numerator).

| Field | Source (prelim.tex 939–950) | Lean (Ch2.lean) | Status |
|---|---|---|---|
| Docstring citation | `lem:Hoeffding-prelim`, lines 939–950, Lemma 2.4 | `lem:Hoeffding-prelim`, `chapters/prelim.tex:939–950`, "Lemma 2.4" (208) | match |
| State space | finite `𝒮 = {1..S}` | `State : Type u`, `[Fintype State]` (214). Nonempty because `d : FiniteDistribution State` has `Σ prob = 1` (CoreDefinitions.lean:15–18) | match |
| Row `P_{s,a}` | the `(s,a)` row of a kernel `P` | arbitrary `d : FiniteDistribution State` (215): real probability vector, `prob ≥ 0`, `Σ = 1`. Every row is such a `d`, and every `d` is a row of some kernel | match (equivalent generalization) |
| Samples | `s^{(i)}(s,a)`, `i = 1..N`, i.i.d. `~ P(·|s,a)` | `draw : Ω → Fin N → State`, `Measurable draw`, `μ.map draw = d.sampleMeasure N` (218), where `sampleMeasure = Measure.pi (fun _ ↦ d.toPMF.toMeasure)` (FiniteSampleDefinitions.lean:25–30). A joint law equal to the product law is exactly "i.i.d. with marginal `d`" | match (count `N`, 0-based `Fin N`) |
| Other rows `(s',a') ≠ (s,a)` | present in the source's generative model, irrelevant to this lemma | not modelled; `Ω` is arbitrary, so other randomness is allowed | match (more general, harmless) |
| `N` range | `N ≥ 1` implicit | `(N : ℕ) (hN : 0 < N)` (216) | match (implicit premise made explicit) |
| Empirical row | `(1/N) Σ_i 1{s^{(i)} = s'}` | `empiricalRow N hN ω`, `prob s = (N:ℝ)⁻¹ * Σ_i (if ω i = s then 1 else 0)` (FiniteSampleDefinitions.lean:33–35) | match |
| `P̂_{s,a}V`, `P_{s,a}V` | inner products | `expectation q V = Σ_x q.prob x * V x` (CoreDefinitions.lean:24–25) | match |
| `𝒱` | finite set of vectors in `ℝ_+^S`, possibly random | `family : Ω → Finset (State → ℝ)` (219): a random finite set; `card` is per `ω` | match (random reading; the deterministic case is a constant `family`) |
| Sign condition | `V ∈ ℝ_+^S` | `∀ ω V, V ∈ family ω → ∀ s, 0 ≤ V s` (225): sure, nonnegative | match (covers either reading of `ℝ_+`) |
| Measurability of `𝒱` | implicit | `Measurable family` w.r.t. `finiteFamilyBorel` (220–221) | implicit premise made explicit; see F2 |
| Independence | "`𝒱` independent of `P̂_{s,a}`" | `IndepFun family (ω ↦ empiricalRow N hN (draw ω)) μ`, with the family σ-algebra `finiteFamilyBorel` and the row σ-algebra `rowVectorSpace = comap prob (Borel on ℝ^State)` (222–224). Independence is from the empirical row only, not from the ordered sample | match (the natural σ-algebras; see F2) |
| `δ` | `0 < δ < 1` | `0 < δ → δ < 1` (216) | match |
| Probability measure | `P` on the sample space | `μ : Measure Ω`, `[IsProbabilityMeasure μ]` (215), `μ.real` | match |
| Direction of the probability bound | "greater than `1−δ`" (strict) | `1 - δ < μ.real {…}` (226) | match (strict) |
| Quantifier inside the event | for all `V ∈ 𝒱` simultaneously | `∀ V ∈ family ω` (226) | match |
| Inner inequality | `≤` | `≤` (227) | match |
| Left side | `|(P̂_{s,a} − P_{s,a})V|` | `|(empiricalRow …).expectation V - d.expectation V|` (227) | match |
| Radius | `sqrt(‖V‖_∞² log(2|𝒱|/δ)/(2N))` | `Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family ω).card / δ) / (2 * N))` (228), parsed as `sqrt((‖V‖² · log((2·card)/δ)) / (2N))` | match (constants 2, 2, square, natural log, union multiplicity `card`) |
| Junk values | none | `card = 0` only when `family ω = ∅`, where `∀ V ∈ ∅` is vacuous, so `Real.log 0 = 0` is never used meaningfully. If `card ≥ 1` then `2·card/δ > 2`, so the log is positive. The `sqrt` argument is `≥ 0`, and `2N > 0` | no junk-value exposure |
| Event measurability | implicit | not asserted in the Prop. The provider proves the event measurable (EmpiricalHoeffdingRandomFamily.lean:176–182), so `μ.real` is the genuine probability, not an outer-measure artifact | match; see F4 |
| Hidden premises | none | `Measurable draw`, `Measurable family` (standard implicit regularity). Nothing else | none found |
| Self-containedness | n/a | The Prop is fully spelled out and does not refer to any theorem's type. It uses only definitions: `FiniteDistribution`, `expectation`, `sampleMeasure`, `empiricalRow`, `finiteFamilyBorel`, `rowVectorSpace` | match |

Instance check: the deterministic printed case (fixed `𝒱`) is an instance of the Prop with `family := fun _ ↦ 𝒱`.
A constant map is measurable and is independent of every random variable under a probability measure. The
random-`𝒱` case with `𝒱` Borel-measurable (for example `{V_1(ω),…,V_k(ω)}` with Borel random vectors) is also an
instance; see F2. So the Prop states the printed result, with no weakening.

## 5. Findings

- **F1 — MINOR (process / AGENTS.md convention, not source fidelity).** AGENTS.md requires
  "`Formalization/Statements/ChN.lean` imports definition modules only and contains no proofs." `Lemma2_4`
  depends on `finiteFamilyBorel`, which is defined in `Formalization/Probability/RandomFamilyBorel.lean` (a
  proof-bearing module; it also contains the provider theorem `randomBorelFamily_empiricalRow_success_gt`
  itself, line 162). It also depends on `rowVectorSpace`, defined in
  `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean:258` (proof-bearing). Ch2.lean therefore
  imports proof modules (Ch2.lean:4–5), and through them `EmpiricalHoeffdingFamily`, `EmpiricalHoeffding` and
  `EmpiricalRow`. This deviation predates this change: HEAD's Ch2.lean already imported both modules for
  `Lemma2_11`. The working-tree change also adds `import Formalization.Probability.BernsteinMatrixMarginals`
  (Ch2.lean:6, used by Lemma2_5 and outside this review's scope). There is no fidelity consequence: the
  `Lemma2_4` Prop uses only definitions and does not cite a theorem type. The fix would be to move
  `finiteFamilyBorel` (with `FamilyEnumeration` and `enumerationFamily`) and `rowVectorSpace` into
  `*Definitions` modules.
- **F2 — NOTE (implicit regularity made explicit; σ-algebra choice).** The source states neither the
  measurability of `𝒱` nor the σ-algebra in which "independent" is meant. The Lean statement fixes the family
  σ-algebra as `finiteFamilyBorel = ⨅ n, map (enumerationFamily n) (Borel on injective n-tuples)`
  (RandomFamilyBorel.lean:83–84). This is the quotient-Borel structure: nontrivial (not `⊥`, since "nonempty"
  is a measurable proper event) and not `⊤` (`{{x} | x ∈ B}` with `B` non-Borel is not measurable). By my own
  (unformalized) argument it coincides with the Hausdorff-metric/Effros Borel structure on finite subsets of
  `ℝ^S`: on each cardinality stratum, sorting is a Borel section of the enumeration map. So it is the standard
  structure, and natural random families are measurable in it. The independence hypothesis is therefore the
  natural reading. The provider chain needs only the much coarser `familyTestSpace` (generated by the
  nonnegativity event and the per-row failure events; EmpiricalHoeffdingRandomFamily.lean:189–193), so the
  Prop's hypothesis is not artificially restrictive. A user whose random set is independent only with respect
  to a σ-algebra strictly coarser than `finiteFamilyBorel` would need to use the library theorem
  `randomFiniteFamily_empiricalRow_success_gt` directly. This is a NOTE, not a discrepancy.
- **F3 — NOTE (implicit premise `N ≥ 1`).** The source never states `N ≥ 1` but divides by `N`. The Lean
  `hN : 0 < N` is required, and making it explicit does not weaken the result.
- **F4 — NOTE (event measurability).** The Prop applies `μ.real` to the success set without asserting
  measurability. I checked that the provider establishes measurability of the failure preimage, and hence of its
  complement, the success set (`hmeas`, EmpiricalHoeffdingRandomFamily.lean:176). The bound is therefore a
  genuine probability bound, not a bound on an outer measure of a possibly non-measurable set.
- **F5 — NOTE (source typography).** prelim.tex:945 has a mismatched delimiter (`\big(` … `)`), and `ℝ_+` is
  undefined in the source. The Lean statement uses `0 ≤ V s`, which covers both readings of `ℝ_+`. No
  mathematical defect.
- **F6 — NOTE (strict probability bound is genuinely proved).** The printed "greater than `1−δ`" is the stronger
  strict form. The provider proves it strictly, not just `≥`: `familyViolation_lt` uses the positive gap
  available on the finite sample space plus strict monotonicity of `exp`
  (EmpiricalHoeffdingFamily.lean:137–206). `empiricalRow_family_success_gt` uses a strict finite sum (210–241).
  For random families, `lintegral_strict_mono` handles the mixing (EmpiricalHoeffdingRandomFamily.lean:130). The
  empty family is handled separately (62–64). No weakening from `<` to `≤`.

No BLOCKING or MAJOR findings.

## 6. Provider chain (wrapper to Mathlib)

`Lemma2_4_holds` (Ch2Proofs.lean:113–118) introduces the binders in the Prop's order, installs
`MeasurableSpace State := ⊤`, and applies `d.randomBorelFamily_empiricalRow_success_gt` with
`Filter.Eventually.of_forall hV`, which strengthens the sure nonnegativity into the provider's a.e. hypothesis.
The provider's conclusion is token-for-token the Prop's conclusion. The wrapper neither restates nor re-proves
the result.

1. `randomBorelFamily_empiricalRow_success_gt` (RandomFamilyBorel.lean:162–188). Its hypotheses are exactly the
   Prop's, except that nonnegativity is `∀ᵐ` (weaker), and its conclusion is identical. Proof: it coarsens the
   family σ-algebra `finiteFamilyBorel` to `familyTestSpace` via `familyTestSpace_le_finiteFamilyBorel`
   (146–158, which uses the Borel measurability of the nonnegativity and failure tests on enumeration spaces,
   102–143). It transports `Measurable` with `.mono` and `IndepFun` with `.comp`.
2. `randomFiniteFamily_empiricalRow_success_gt_vectorSigma` (EmpiricalHoeffdingRandomFamily.lean:289–315). It
   upgrades row independence from `rowVectorSpace` to `⊤` using finite range plus measurable singletons
   (`indepFun_finiteRange_to_discrete`, 235–254, and `rowVectorSpace_singletons`, 262–284).
3. `randomFiniteFamily_empiricalRow_success_gt` (211–230) instantiates
4. `randomFamily_empiricalRow_success_gt` (137–185) with `code := id`. It rewrites the joint law as a product
   law via Mathlib's `indepFun_iff_map_prod_eq_prod_map_map`, then bounds the failure set by
5. `product_supportedFamilyBad_lt` (97–132), a section-wise bound using `Measure.prod_apply` and
   `lintegral_strict_mono`. The sections are bounded by
6. `empiricalRowLaw_familyBad_lt` (42–64), which handles the empty family separately and reduces to
7. `empiricalRow_family_success_gt` (EmpiricalHoeffdingFamily.lean:210–241), a strict union bound over a
   deterministic family, using
8. `familyViolation_lt` (137–206), a strict per-vector bound `< δ/k` built on
9. `empiricalRow_hoeffding_norm` / `empiricalRow_hoeffding` (EmpiricalHoeffding.lean:84–122). These give
   Hoeffding with interval `[0, ‖V‖]` and the bound `2 exp(−2Nε²/B²)`, obtained from Mathlib's
   `hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma), `HasSubgaussianMGF.sum_of_iIndepFun` and
   `HasSubgaussianMGF.measure_ge_le`. The independence of the coordinates comes from Mathlib's `iIndepFun_pi`
   (EmpiricalRow.lean:51–53), and the coordinate mean from `measurePreserving_eval` / `PMF.integral_eq_sum`
   (EmpiricalRow.lean:37–76).
10. Supporting definitions: `familyRadius = ‖V‖ * sqrt(log(2k/δ)/(2N))`, proved equal to the source form by
    `familyRadius_eq_source` (EmpiricalHoeffdingFamily.lean:22–32). There are also `empiricalRow_norm_zero_deviation`
    (EmpiricalHoeffding.lean:125–130) and `empiricalRow_expectation` (EmpiricalRow.lean:56–62).

No fallback definitions, extra assumptions, or weakened conclusions were found anywhere in the chain. Every
`MeasurableSpace State` local instance in the chain is `⊤`: FiniteSampleDefinitions:21,
EmpiricalRowMeasurableDefinitions:5, EmpiricalHoeffding:13, EmpiricalHoeffdingFamily:19,
EmpiricalHoeffdingRandomFamily:13, RandomFamilyBorel:20. They agree with the Prop's `letI … := ⊤`. The local
`MeasurableSpace (FiniteDistribution State) := ⊤` in EmpiricalHoeffdingRandomFamily.lean:14 is file-local and
does not leak into the Prop, which fixes `rowVectorSpace` explicitly.

## 7. Forbidden-token grep

Pattern (word-bounded): `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide`, plus `@[extern` and
`ofReduceBool`. Results:
- Local import closure of `Formalization.Probability.RandomFamilyBorel` (21 modules), plus
  `Formalization/Statements/Ch2.lean` and `Formalization/Statements/Ch2Proofs.lean`: **0 hits**.
- Full local import closure of `Formalization.Statements.Ch2Proofs` (149 modules): **0 hits**.
- `Audit.lean` was not run. It would check every `StatisticalRL.*` constant (which includes
  `StatisticalRL.Statements.Lemma2_4_holds`) against {propext, Classical.choice, Quot.sound}, and
  `Formalization.lean:436–437` imports both statement files. **Axiom closure is unverified by this review.**

## 8. Items needing Lean-side confirmation

1. That the uncommitted `Lemma2_4` (Ch2.lean) and `Lemma2_4_holds` (Ch2Proofs.lean) elaborate and compile at
   the pinned Lean/Mathlib (no compiler was run).
2. The elaborated type of `Lemma2_4`, in particular that `(2 * N)` and `2 * (family ω).card / δ` elaborate with
   real casts (value-equal either way), and that `‖V‖` resolves to the Pi sup norm.
3. That the `MeasurableSpace (Fin N → State)` in `μ.map draw = d.sampleMeasure N` unifies as `MeasurableSpace.pi`
   over `⊤` on both sides, and that `finiteFamilyBorel` / `rowVectorSpace` resolve to the `StatisticalRL.FiniteDistribution` definitions read here.
4. `#print axioms StatisticalRL.Statements.Lemma2_4_holds` (or `lake env lean Audit.lean`) returns only
   `propext`, `Classical.choice`, `Quot.sound`.
5. The Mathlib semantics listed at the top of Section 4.

## 9. Verdict

VERDICT: PASS-WITH-FINDINGS. The indexed `Lemma2_4` Prop states the printed Lemma 2.4 exactly. This covers
constants, strictness, `δ` range, the random family independent of `P̂_{s,a}` only, the nonnegativity
condition, and the empty-family edge case, adding only standard implicit regularity (`N > 0` and
measurability). The wrapper derives it directly from a sorry-free provider chain. The only non-NOTE finding (F1)
is a pre-existing statement-file import-convention deviation with no fidelity impact.

## 10. Disclosure check (performed only after Sections 3–9 were written)

`docs/SOURCE-ISSUES.md` (SHA256 `3d113729e6b40874e1692cb9f3d55f02bf701c2ae5e95431f0791c3c28014b9a`, 773 lines) was searched for `Hoeffding`, `prelim.tex`,
`Lemma 2.4`, `Lemma2_4`, `939`, `945`, `ℝ_+`, `finiteFamilyBorel`, `rowVectorSpace`, `import`, `definition modules`,
and the section headings were read, including the "Statement-index scope disclosures" block at lines 389–466.

- F1 (statement-file imports proof modules): **not disclosed**. It is a process-convention item, not a source
  issue, so `SOURCE-ISSUES.md` is not the natural home; it belongs in the lead's integration notes.
- F2–F6 (NOTEs): **not disclosed**, and no disclosure is required. Each is either an implicit source premise made
  explicit in a way that still implies the printed statement (which AGENTS.md says is not a discrepancy) or a
  cosmetic source typo.
- No `_corrected` or `_restricted` variant exists or is needed for Lemma 2.4.
