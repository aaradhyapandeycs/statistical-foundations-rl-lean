# Critic report: Lemma 2.12 (`lem:KL-tensorize`)

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-06T17:10:23Z (session start 2026-11-06T17:05:29Z)
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106` (working tree has uncommitted changes; reviewed files are uncommitted/untracked as listed below)
- Mode: source-only review; no Lean compiled; axiom audit not run. No lake/lean/LSP process was started.
- Independence: `docs/PROGRESS.md`, `docs/COVERAGE.md`, other critic reports and other private working files were not read. `docs/SOURCE-ISSUES.md` was read only after the sections up to "Items needing Lean-side confirmation" were written.

## 1. Files read (SHA-256) and ranges inspected

Project files (paths relative to the project root):

| File | SHA-256 | Pin / brief | Ranges inspected |
|---|---|---|---|
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | matches pin and brief | 1081–1103 (comment env, via grep), 1120–1145, 1205–1215, 1270–1345, 595–600, 1352–1370 (comment env, via grep); greps for KL / lemma environments over whole file |
| `source/upstream/tex/chapters/intro.tex` | `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a` | matches pin | 215–250 (printed KL definition) |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | matches pin | grep only (lines 61–64, `\KL` macros) |
| `source/upstream/tex/StatisticalRL-nowplain.tex` | `5a925ce6a5a988bdc4b8631c5b3f985195f58b9fec80cc1f3d80c6cd10aea956` | matches pin | grep `newtheorem` only (lines 60, 62) |
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` | matches pin | 2786–2793 (downstream use) |
| `source/upstream/tex/chapters/generative_model_model_based.tex` | `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d` | matches pin | 1993–1999 (downstream use) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | — | grep for pin keys |
| `Formalization/Statements/Ch2.lean` | `317cfdf8c6d482b3a87cf09e528e7e2a2a77063796bb02be17445ec36d55f86d` | matches brief | 1–40, 260–290, docstring/def grep, `git diff` |
| `Formalization/Statements/Ch2Proofs.lean` | `a69420317ccfaa017a8fca7aa0b4c8c5dccc95996f86326a8c355b5edcd1868a` | matches brief | 1–30, 125–139, `git diff` |
| `Formalization/PrelimKL/KLArbitraryFinitePi.lean` | `e2c843fcb07110fbad3308389feefeeed6df35e2363edddfee6f94ff2dd0a1fa` | untracked | full (44 lines) |
| `Formalization/PrelimKL/KLFinitePi.lean` | `e4f054b1b40a339f8852341d5e174e22f5f8caf5b544ee2c880873bda73bcc0e` | untracked | full (45 lines) |
| `Formalization/PrelimKL/KLMeasurableEquiv.lean` | `05f1fb71471b01a7cef1fbb369c8eb3a93e761e9470be4662cb32003733646a1` | untracked | full (80 lines) |
| `Formalization/PrelimKL/KLBinaryProductAllValues.lean` | `81da8bcb078313e733e304c5da62ecaeff3203d5f3188322dbbc63f9d10fa18d` | untracked | full (128 lines) |
| `Formalization/PrelimKL/KLBinaryProductFinite.lean` | `48fd0e7b19bb63a116c2ae4109f39858d63ab96a955a99ce0850143128b09378` | untracked | full (111 lines) |
| `Formalization/PrelimKL/KLBinaryProductLLRAdd.lean` | `ca25461bc67abb2fd884ee7cb81503b9e7dba1489255d20293cbb21015d17176` | untracked | full (69 lines) |
| `Formalization/PrelimKL/KLBinaryProductRNDerivative.lean` | `0e4ec7053061ff965649e41966218c0e39c00e4f7568a1561193c707c4aa0a03` | untracked | full (55 lines) |
| `Formalization.lean` | `697052168941c159e83d54a657a736da1d37e74290ab7f51ce6e04bf3b0e90a1` | — | grep + `git diff` (imports at 107–113, 436–437) |
| `Audit.lean` | `29f6cd54e69586325be78af79809bda1f1d1c2b0c52f03ad3746eb6e8c3d06f3` | — | 1–24 |
| `lakefile.toml` | `81c4d520fd54386390da16caec86bbc61220188e04ac0c996e880458a5d728ed` | — | full (no `leanOptions`) |
| `lean-toolchain` | `194fcae7a59d3268baa175bd3e352dafab6954fe08a5b7caec13bedf36f80315` | — | `leanprover/lean4:v4.27.0-rc1` |

All seven `PrelimKL` hashes are recorded above; the brief did not give reference hashes for them. The two statement files and `prelim.tex` match the brief exactly; nothing changed since brief time.

Mathlib (read-only, `the pinned Mathlib dependency checkout (read-only)`, `git rev-parse HEAD` = `32d24245c7a12ded17325299fd41d412022cd3fe`, clean working tree, matching the `lakefile.toml` pin):

| File | SHA-256 | Ranges |
|---|---|---|
| `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` | `6ae68f0c2ecafbe5f7932b3d8f863539d4d9f6018c1905ed0e5664986ef6c23d` | 1–110, 150–172 |
| `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean` | `12bfcbd9923aa4276a18c1e72f82c8c48326ee608fdc0c67d2f76de834a0f38b` | 37–39, 87 |
| `Mathlib/MeasureTheory/Constructions/Pi.lean` | `13d39aa0f7e4ba15a9d83dfab8f072888b976a1e55fa9a7a0a0acefce04b5981` | 67–71 (variables), 280–300, 336–340, 690–735, 793–797 |
| `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` | `a6b36f4bbf936b667df61c4eb3732db5162c197ab3cff55ca23c46a1afd597cc` | 487–498 |
| `Mathlib/MeasureTheory/Measure/WithDensity.lean` | `11c5c298bacef476fc14c026aa95c6a1a1c8b781ab9200e0af0115ad017feb8e` | 683–690 (grep) |
| `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` | `6269b4727c63b43b24397ae8e8ea9d59ca3d4395002caece1f531cd30b146fc8` | 565–569 |
| `Mathlib/MeasureTheory/Integral/Prod.lean` | `2f35cd4b89bc6be0acd9cdd688989112ce0a4e0939c3f574e620658a8d6b1825` | 295–299, 331–336 (grep) |
| `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean` | `187924bc1b41d30b1406aaca16563582ea6f815719e7f2048c276d3295cba567` | 421, 433 (grep) |

## 2. Source reconstruction (written before reading any Lean)

**The lemma** (`prelim.tex:1313–1319`, label `lem:KL-tensorize`). For two product distributions P = P_1 ⊗ ⋯ ⊗ P_n and Q = Q_1 ⊗ ⋯ ⊗ Q_n, the lemma states the identity KL(P‖Q) = Σ_{i=1}^n KL(P_i‖Q_i). No proof is printed. The lead-in at 1311 calls this the "tensorization (i.e., additivity) property" for independent data and cites Tsybakov §2.4.

**Numbering check.** Counting the uncommented `lemma` environments in `prelim.tex` gives 339, 458, 544, 939, 956, 985, 1001, 1038, 1056, 1140, 1209, 1313, 1335. The lemma at 1092 sits inside `\begin{comment}` 1081–1103, and the ones at 597 and 1022 are commented out with `%`. So `lem:KL-tensorize` is printed as **Lemma 2.12**. This agrees with the existing index, which has 2.11 = reverse Fano at 1209 and 2.13 = KL-quadratic at 1335.

**KL definition.** The printed definition is `intro.tex:229–232` (`eq:defn-KL`): "When P is absolutely continuous w.r.t. Q", KL(P‖Q) := ∫ log(dP/dQ) dP, for probability measures on a common measurable space (`intro.tex:218`). A second copy at `prelim.tex:1132–1138` is commented out, so it is not printed text. The book prints no convention for the case where absolute continuity fails. The value ∞ for P not ≪ Q is the standard convention, but the book does not state it. When P ≪ Q are probability measures and f = dP/dQ, the negative part of log f is P-integrable: ∫(log f)^- dP = ∫_{f<1} f·(−log f) dQ ≤ 1/e. So the printed integral is always well defined in [0, ∞] (Gibbs gives ≥ 0), and it equals +∞ exactly when the positive part diverges.

**What "product distributions" means.** The book uses a finite number n of factors (n ≥ 1 implicitly; n = 0 is the trivial case where both sides are 0). P_i and Q_i are probability measures on a common measurable space X_i. The X_i may differ across i, and nothing requires them to be finite or discrete: the use at `offlineRL.tex:2786–2793` applies the lemma to i.i.d. samples from a general behaviour law, and `generative_model_model_based.tex:1993–1999` applies it to samples with coordinate-dependent laws. P and Q are the product measures on X_1 × ⋯ × X_n with the product σ-algebra.

**Implicit assumptions and ambiguities.**
1. The identity lives in [0, ∞]. Either side may be +∞.
2. When some P_i is not ≪ Q_i, the printed definition does not define KL(P_i‖Q_i). In that case P is not ≪ Q either, since marginals of an a.c. pair are a.c. So under the literal printed definitions, both sides make sense exactly when every P_i ≪ Q_i, which for probability measures is equivalent to P ≪ Q. Under the standard ∞ convention, both sides are ∞ in the non-a.c. case. The lemma does not say which reading it intends, but any faithful formalization must agree with the printed identity on the a.c. domain, including the +∞ values.
3. The factors are probability measures, not general finite measures. This matters: with the normalized-mass KL used by Mathlib, additivity fails for unnormalized measures.

## 3. Lean statement: field-by-field comparison

The Lean entry is `Formalization/Statements/Ch2.lean:277–288`. Its body is:

```lean
def Lemma2_12 : Prop :=
  ∀ (ι : Type u) [Fintype ι] (α : ι → Type v)
    [∀ i, MeasurableSpace (α i)]
    (P Q : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)],
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
      ∑ i, InformationTheory.klDiv (P i) (Q i)
```

Mathlib semantics relied on (checked in the pinned Mathlib sources): `klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ llr μ ν ∂μ + ν.real univ − μ.real univ) else ∞` (`KullbackLeibler/Basic.lean:56–60`), and `llr μ ν x = log (μ.rnDeriv ν x).toReal` (`LogLikelihoodRatio.lean:37`). For probability measures the correction term ν.real univ − μ.real univ is 0.

| Field | Source | Lean (file:line) | Verdict |
|---|---|---|---|
| Number / index of factors | i = 1..n, finite (n ≥ 1 implicit) | `ι : Type u` with `[Fintype ι]` (Ch2.lean:283) | **stronger** (generalization). The source is the instance ι = `Fin n` at u = 0. Empty ι is allowed: both sides are 0, which is true. |
| Factor spaces | measurable space X_i, may depend on i, arbitrary | `α : ι → Type v`, `[∀ i, MeasurableSpace (α i)]` (283–284) | match. Arbitrary measurable spaces, no standard-Borel, countably generated, or discreteness assumption. |
| Product space | X_1 × ⋯ × X_n with the product σ-algebra | `∀ i, α i` with `MeasurableSpace.pi` (implicit in `Measure.pi`) | match up to the canonical measurable equivalence (NOTE-1). For finite ι, `MeasurableSpace.pi` is the product σ-algebra. |
| Product measure | P_1 ⊗ ⋯ ⊗ P_n | `Measure.pi P` (287). For σ-finite factors it is characterized by `pi_pi` on boxes, `Pi.lean:290–294`. | match |
| Measure class | "distributions", i.e. probability measures | `IsProbabilityMeasure (P i)` and `IsProbabilityMeasure (Q i)` for every i (286) | match. No extra finiteness/σ-finiteness premise; it follows from the probability assumption. |
| P_i and Q_i on the same space | yes | both `Measure (α i)` (285) | match |
| Divergence | KL of `eq:defn-KL`: ∫ log(dP/dQ) dP when P ≪ Q | `InformationTheory.klDiv` (Mathlib, not shadowed; grep found no local `klDiv`, `Measure`, or `InformationTheory` namespace or definition under `Formalization/`) | match on the a.c. domain. If P ≪ Q and llr is integrable, `klDiv = ofReal(∫ llr dP)`, which equals the source integral (the integral is ≥ 0, so `ofReal` loses nothing). If P ≪ Q and llr is not integrable, `klDiv = ∞` and the source integral is +∞ (its negative part is integrable). Junk values of `llr` where rnDeriv ∈ {0, ∞} lie on a P-null set when P ≪ Q. **Extension**: Mathlib sets `klDiv = ∞` when absolute continuity fails, a case the printed definition leaves undefined. |
| Codomain | [0, ∞] | `ℝ≥0∞` on both sides, finite sum in `ℝ≥0∞` (287–288) | match. No `toReal` and no real-valued junk. |
| Non-a.c. coordinate | undefined in the printed text; ∞ under the standard convention | RHS = ∞ (`ENNReal` sum with an ∞ summand). LHS = ∞ because the product is not a.c. (proved in the chain via marginals). | the Prop is **true and consistent with the convention**. It asserts nothing false or vacuous about the source. |
| Hidden premises | — | none: no a.c., integrability, finiteness-of-KL, `DecidableEq`, or countability premise | match |
| Missing source premises | — | none | match |
| Universes | none in the source | `Lemma2_12.{u, v}` is universe-polymorphic; the wrapper proves it at arbitrary `u, v` (Ch2Proofs.lean:135) | no restriction |
| Docstring label and range | `lem:KL-tensorize`, `prelim.tex:1313–1319` (exactly the `lemma` environment) | Ch2.lean:277 | match; the printed number 2.12 is verified above |
| Docstring claim "both sides are ∞ exactly when some coordinate divergence is" | — | Ch2.lean:279 | correct: a finite `ℝ≥0∞` sum is ∞ iff some summand is ∞, and LHS = RHS |
| Docstring claim "The source's general KL definition is the standard extended-valued one" | the printed definition is conditional on P ≪ Q, and no ∞ convention is printed | Ch2.lean:280–281 | **inaccurate attribution** (MINOR-1) |

**Overall statement verdict.** The Prop implies the printed identity at every instance where the printed identity is meaningful (ι = `Fin n`, all P_i ≪ Q_i), including the +∞ cases. Outside that domain it asserts ∞ = ∞, which is the standard convention and is true. It does not assume more or conclude less than the source, and it concerns the same objects.

## 4. Wrapper and provider chain

The wrapper is `Ch2Proofs.lean:135–137`, `theorem Lemma2_12_holds : Lemma2_12.{u, v}`. It runs `intro ι hι α hα P Q hP hQ`, which matches the 8 binders in order, then `exact StatisticalRL.PrelimKL.klDiv_pi_eq_sum α P Q`. The provider's signature is `{ι : Type*} [Fintype ι] (α : ι → Type u) [∀ i, MeasurableSpace (α i)] (P Q) [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]`, and its conclusion is literally the body of `Lemma2_12` (`KLArbitraryFinitePi.lean:13–19`). This is an exact application: no restatement, no reproof, no extra hypothesis, no weakening. `u, v` are not declared with `universe` in `Ch2Proofs.lean`, so they are auto-bound. `lakefile.toml` sets no `leanOptions`, so the default `autoImplicit`/`relaxedAutoImplicit` applies. The committed `Lemma2_11_holds : Lemma2_11.{u}` (HEAD, `Ch2Proofs.lean:62`) uses the same pattern.

Provider chain (all in namespace `StatisticalRL.PrelimKL`, so the `Audit.lean` prefix scan over `StatisticalRL` covers them):

1. `klDiv_pi_eq_sum` (`KLArbitraryFinitePi.lean:13–42`). It reindexes ι to `Fin (card ι)` via `Fintype.equivFin` and `MeasurableEquiv.piCongrLeft`, with measure preservation from Mathlib `measurePreserving_piCongrLeft`. That lemma uses `{ι ι' : Type*}` in independent universes (`Pi.lean:67`), so reindexing from `Type u` to `Type 0` is fine. It then applies (2) and (3) and finishes with `Equiv.sum_comp`.
2. `klDiv_measurePreserving_measurableEquiv` (`KLMeasurableEquiv.lean:13–78`). KL of probability measures is invariant under a measurable equivalence preserving both measures. The proof transfers a.c. via `map`, transfers rnDeriv via `MeasurableEmbedding.rnDeriv_map`, transfers llr integrability via `integrable_comp_emb`, and in the finite case compares integrals via `toReal_klDiv_of_measure_eq` and `integral_comp'`. The ∞ case is handled by `klDiv_ne_top_iff`. The argument is mathematically sound.
3. `klDiv_pi_fin` (`KLFinitePi.lean:11–43`) proceeds by induction on n. The case n = 0 uses `pi_of_empty` (Dirac at the same default point), then `klDiv_self` and an empty sum. The succ case uses `piFinSuccAbove α 0` and `measurePreserving_piFinSuccAbove` (single universe `α : Fin (n+1) → Type u`, which holds here), then (2), (4), `Fin.sum_univ_succ` and the induction hypothesis.
4. `binary_product_klDiv_add` (`KLBinaryProductAllValues.lean:103–126`) is the extended-valued binary identity. It splits into three cases:
   - KL(P₁‖Q₁) = ∞: the product KL is ∞ by `binary_product_finite_klDiv_left`. That lemma gets marginal a.c. via `map fst`, rewrites the product llr to llr₁ + llr₂ a.e. by (5), takes a P₂-a.e. integrable section `prod_left_ae`, picks one point, and subtracts a constant.
   - KL(P₂‖Q₂) = ∞: symmetric, via `binary_product_finite_klDiv_right`.
   - Both finite: the product KL is finite by `binary_product_finite_klDiv_of_finite`, and the `toReal` identity comes from (6).
5. `llr_prod_eq_add_ae` (`KLBinaryProductLLRAdd.lean:12–67`). Under P₁ ≪ Q₁ and P₂ ≪ Q₂, the product llr equals llr₁(z.1) + llr₂(z.2) P₁⊗P₂-a.e. The proof uses (7), positivity and finiteness of the coordinate rnDerivs a.e. (`rnDeriv_pos`, `rnDeriv_lt_top`, pushed through the marginals), then `Real.log_mul`.
6. `binary_product_toReal_klDiv_of_finite` (`KLBinaryProductFinite.lean:15–109`). It repeats the llr additivity argument inline, uses product integrability `comp_fst.add comp_snd`, applies `integral_add`, and maps the integrals to the marginals.
7. `rnDeriv_prod_eq_mul_ae` (`KLBinaryProductRNDerivative.lean:16–53`). It writes μ = ν.withDensity(dμ/dν) for μ ≪ ν, applies Mathlib `prod_withDensity` (`WithDensity.lean:690`), and concludes uniqueness via `Measure.eq_rnDeriv₀` (`Lebesgue.lean:565`, needs `SigmaFinite` of the product, which is available).

The chain bottoms out in Mathlib only: `klDiv`, `llr`, `rnDeriv`, `Measure.pi`, `Measure.prod`, `withDensity`, `MeasurableEquiv`. It uses no local definitions, no fallback definitions, and no additional hypotheses. I checked by reading that every Mathlib name used exists at the pinned revision: `prod_withDensity`, `eq_rnDeriv₀`, `measurePreserving_piCongrLeft`, `measurePreserving_piFinSuccAbove`, `pi_of_empty`, `stronglyMeasurable_llr`, `Integrable.comp_fst`/`comp_snd`, `Integrable.prod_left_ae`/`prod_right_ae`, `MeasurableEmbedding.rnDeriv_map`, `klDiv_ne_top_iff`, `toReal_klDiv_of_measure_eq`. I did not compile, so I did not confirm that every tactic step elaborates.

## 5. Forbidden-token grep

The grep covered two scopes:
- the 7 `PrelimKL` files, `Ch2.lean` and `Ch2Proofs.lean`;
- the full transitive `Formalization.*` import closure of `Formalization/Statements/Ch2Proofs.lean`: 149 modules, computed by a script that follows `import Formalization.*` lines. The closure of `KLArbitraryFinitePi` alone is the 7 `PrelimKL` modules plus Mathlib.

Tokens searched: `grep -nwE "sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|ofReduceBool"` and `grep -n "@\[extern"`.

**Result: no matches in either scope.** The axiom audit (`lake env lean Audit.lean` / `#print axioms`) was **not run**, per the brief, so transitive kernel-axiom closure is unverified. `Audit.lean` scans every constant with prefix `StatisticalRL`, which includes `StatisticalRL.Statements.Lemma2_12_holds` and all `StatisticalRL.PrelimKL.*`. Both statement files are imported from `Formalization.lean` (lines 436–437), and all 7 `PrelimKL` modules are imported at lines 107–113.

## 6. Findings

No BLOCKING or MAJOR findings.

- **MINOR-1: docstring misattributes the ∞ convention to the source** (`Ch2.lean:280–281`). The docstring says "The source's general KL definition is the standard extended-valued one, modelled by Mathlib's `klDiv`." The printed definition (`intro.tex:229–232`, `eq:defn-KL`) is stated only "When P is absolutely continuous w.r.t. Q", and the book prints no ∞ convention. The commented copy at `prelim.tex:1132–1138` has the same condition and is not printed text. The docstring also does not cite `eq:defn-KL`.
  - Concrete failure: a reader checking the entry against the book, as the index is meant to allow, will not find an extended-valued definition. They may conclude either that the book asserts the identity for non-a.c. pairs, which it does not, or that the entry rests on an unprinted definition without saying so.
  - Effect on the Prop: none. It is true and implies the printed identity on its domain.
  - Suggested wording: "The printed KL (`eq:defn-KL`, `chapters/intro.tex:229–232`) is defined only for P ≪ Q. Mathlib's `klDiv` agrees with it there, including the value ∞ when the integral diverges, and is ∞ otherwise. In that extension case both sides are ∞."
- **MINOR-2: stale draft and status headers in library modules slated for the public repo.**
  - `KLBinaryProductRNDerivative.lean:5–6`: "Private source proof draft … No compiler was run for this file in the current task."
  - `KLBinaryProductFinite.lean:6–7`: "Private proof draft for the finite-KL binary-product branch of preliminary.tex, … Not compiled in this task." This also names a nonexistent source file: the file is `chapters/prelim.tex`, not `preliminary.tex`.
  - Both modules are imported by `Formalization.lean`. Once the build passes, these headers will state a false status. They also conflict with AGENTS.md's public-release requirement of "no transient probes". This is not a source-fidelity defect.
- **NOTE-1: representation choice.** P_1 ⊗ ⋯ ⊗ P_n is modelled as `Measure.pi` on the dependent function type over an arbitrary `Fintype ι`, not as an iterated binary product on X_1 × ⋯ × X_n indexed by `Fin n`. This generalizes the source (the source is ι = `Fin n`, u = 0) and is equivalent up to a measure-preserving measurable equivalence. The library proves exactly this invariance for KL in `KLMeasurableEquiv.lean`. It also covers n = 0. Acceptable; it could be mentioned in the docstring.
- **NOTE-2: duplicated proof.** The a.e. llr additivity argument (positivity/finiteness boilerplate plus `Real.log_mul`) appears twice: `KLBinaryProductLLRAdd.lean:20–67` and `KLBinaryProductFinite.lean:25–80`. `binary_product_toReal_klDiv_of_finite` could call `llr_prod_eq_add_ae`. This is a maintainability issue only.
- **NOTE-3: auto-bound universes in the wrapper.** `Lemma2_12_holds : Lemma2_12.{u, v}` relies on auto-bound universe names (no `universe u v` in `Ch2Proofs.lean`; default `autoImplicit` because `lakefile.toml` sets no options). This matches the committed `Lemma2_11_holds` pattern. It is harmless if it compiles, but it becomes fragile if the project ever sets `autoImplicit = false`.
- **NOTE-4 (out of scope for Lemma 2.12; recorded for the lead): `Ch2.lean` imports proof modules.** It imports modules that contain theorem/lemma declarations: `Formalization.Probability.RandomFamilyBorel` (9), `Formalization.Probability.EmpiricalHoeffdingRandomFamily` (11), and `Formalization.Probability.BernsteinMatrixMarginals` (6, added in the current uncommitted diff). This conflicts with AGENTS.md "`ChN.lean` imports definition modules only". Lemma 2.12 itself needs only the Mathlib imports `Mathlib.InformationTheory.KullbackLeibler.Basic` and `Mathlib.MeasureTheory.Constructions.Pi`, which are already present, so this entry is unaffected.

## 7. Items needing Lean-side confirmation

1. The whole `PrelimKL` chain compiles at the pinned toolchain and Mathlib. Two files say in their own headers that they were not compiled. Spots I could not confirm by reading:
   - the definitional unfolding `α (Fin.succAbove 0 j)` ≡ `α j.succ` in the `let e` type ascription and in `hP`/`hQ` (`KLFinitePi.lean:22–29`);
   - the `simp` closing the n = 0 case (`KLFinitePi.lean:19–20`);
   - the `simpa … using Equiv.sum_comp` step (`KLArbitraryFinitePi.lean:40–42`).
2. `#print axioms StatisticalRL.Statements.Lemma2_12_holds` is ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, and `lake env lean Audit.lean` passes.
3. The elaborated type of `Lemma2_12_holds` is `Lemma2_12.{u, v}` with `u, v` as genuine universe parameters, not specialized, and the auto-bound universes elaborate (NOTE-3).
4. `InformationTheory.klDiv`, `Measure.pi` and `IsProbabilityMeasure` in `Ch2.lean` resolve to the Mathlib constants. Grep found no local shadowing, but resolution should be confirmed by `#check @StatisticalRL.Statements.Lemma2_12` / `#print`.

## 8. Verdict

VERDICT: PASS-WITH-FINDINGS — `Lemma2_12` is a faithful, slightly more general statement of the printed tensorization identity in `ℝ≥0∞` with no hidden premises, and the wrapper applies an exactly matching provider whose chain reaches only Mathlib definitions. The findings are a docstring misattribution of the ∞ convention (MINOR-1) and stale "draft / not compiled" headers (MINOR-2), and compilation plus the axiom audit remain unverified by this source-only review.

## 9. Disclosure in `docs/SOURCE-ISSUES.md`

(Filled in after the sections above were written.)

`docs/SOURCE-ISSUES.md` (sha256 `3d113729e6b40874e1692cb9f3d55f02bf701c2ae5e95431f0791c3c28014b9a`, 773 lines) has no entry for Lemma 2.12, `lem:KL-tensorize`, KL tensorization, or the `PrelimKL` files. I searched for `2.12`, `2_12`, `tensoriz`, `KL-tensorize`, `klDiv`, `extended-valued`, `absolutely continuous`, `PrelimKL`, `draft`, `not compiled` and `preliminary.tex`, and read the section headings. The only hit, "draft" at line 169, is in Candidate C5 (Lemma 4.3) and unrelated. Candidate C21 (lines 757–773) concerns a different lemma.

- MINOR-1 (docstring misattributes the ∞ convention): **not disclosed.** Under AGENTS.md this does not require a `SOURCE-ISSUES.md` entry, because the Prop implies the printed result. The fix belongs in the `Ch2.lean:277–281` docstring.
- MINOR-2 (stale "Private … draft / not compiled" headers, wrong file name `preliminary.tex`): **not disclosed.** This is release hygiene, not a source issue, and should be fixed in the two module headers before publication.
- NOTE-1 to NOTE-4: **not disclosed.** None is a source-fidelity discrepancy that requires a `SOURCE-ISSUES.md` entry.

The absence of a `_corrected` or `_restricted` variant for Lemma 2.12 is consistent with my finding that the export implies the printed statement.
