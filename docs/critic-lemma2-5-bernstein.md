# Critic report: Lemma 2.5 (Bernstein inequality), `lem:Bernstein-prelim`

Public copy of the independent critic report; local paths removed.

- Date (UTC, from `date -u`): Fri Nov  6 17:03:19 UTC 2026
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`
- Branch: `batch-ch2-ch3-ch6-20261106` (working tree has uncommitted changes to `Ch2.lean` and `Ch2Proofs.lean`; this review covers the working-tree contents hashed below)
- Mode: source-only review. No Lean compiled, no `lake`, no `scripts/check.py`. The axiom audit was not run.

## 1. Inputs and pin check

Every `.tex` file read was compared with `source/provenance.json` (`source_files`). All match.

| File | SHA256 | Pin | Lines inspected |
|---|---|---|---|
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | n/a | whole |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` | MATCH | 30–40, 380–460, 895–990; theorem-environment grep |
| `source/upstream/tex/chapters/commands.tex` | `78f6f8b5f086797d195dc72df6426df96faf632b3687723cfbe405fe411f7df3` | MATCH | grep: 7 (`\ind`), 111 (`\cA`), 114 (`\cS`), 226 (`\mymid`), 266 (`\Var`) |
| `source/upstream/tex/chapters/intro.tex` | `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a` | MATCH | 183–215 (notation: entrywise `|a|`, `sqrt a`, `a ≤ b`) |
| `source/upstream/tex/StatisticalRL-nowplain.tex` | `5a925ce6a5a988bdc4b8631c5b3f985195f58b9fec80cc1f3d80c6cd10aea956` | MATCH | 185–210, `\input` grep (chapter order) |
| `source/upstream/tex/nowfnt.cls` | `d86c0a39f74ee1a27412e6bca1b00ce72f04c7fd575d3e6cc01c1221471ffbd2` | MATCH | 1331–1337 (lemma shares theorem counter, per chapter) |
| `Formalization/Statements/Ch2.lean` | `317cfdf8c6d482b3a87cf09e528e7e2a2a77063796bb02be17445ec36d55f86d` | same as brief | 1–60, 180–290 |
| `Formalization/Statements/Ch2Proofs.lean` | `a69420317ccfaa017a8fca7aa0b4c8c5dccc95996f86326a8c355b5edcd1868a` | same as brief | 1–30, 95–139 |
| `Formalization/MDP/CoreDefinitions.lean` | `68bf277b85a22ce7f2e8aee6f4ebc2bb3e06c6eb8b047519a79f0a468c1d4102` | n/a | 1–45 |
| `Formalization/Probability/VarianceDefinitions.lean` | `850d2fb7b62601ec5b4ba05d0f1f56d974102eac1106e33be1d7acacf9d1c6c0` | n/a | whole |
| `Formalization/Probability/FiniteSampleDefinitions.lean` | `baa436abfb5988ab409cec759899fe944a05a7cd64bcb07fd8a8899a85f1a772` | n/a | whole |
| `Formalization/Probability/RandomFamilyBorel.lean` | `1bda21b0bac900dc0dec5db6cef949dfc99a745dff4cce14f2a1a0732c57d335` | n/a | 1–140 |
| `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean` | `d5434c422e8535a134cedf7a5ff66c8ad8db0f49c77c3c018b26ec52b26f5fa6` | n/a | 1–60, 225–300 |
| `Formalization/Probability/BernsteinMatrixMarginals.lean` | `70cefdb4775c8dc406b61e22fa41f0a80e3689d13e98e2a272a19380e500f321` | n/a | whole (161 lines) |
| `Formalization/Probability/BernsteinFamily.lean` | `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe` | n/a | whole (335 lines) |
| `Formalization/Probability/SharpEmpiricalBernstein.lean` | `f47b57d451b8ee49c8b702a834ee99747ec5cca36288bf9344dd08c11a596e67` | n/a | whole (299 lines) |
| `Formalization/Probability/EmpiricalBernstein.lean` | `ceee7deadcbf30aad24c3c2b4f6e38a53eb5055f792a849ab95368ce95023cdf` | n/a | 17–165, 227–230 |
| `Formalization/Probability/EmpiricalRow.lean` | `12a24b4883e75ba3f6302573f46b7d7648f90052333dc1c1d268722964c9152b` | n/a | 1–30, 65–73 |
| `Formalization/Probability/EmpiricalRowMeasurableDefinitions.lean` | `fc40126e0beac16c94075094551b34ffe2700ce31d83721f179581fb4cde4275` | n/a | whole |
| `Formalization/Probability/Variance.lean` | `e9133f551400e38be5010bf6d3ca31416ae535a00ba71b3f17f24f875d52125f` | n/a | 27–43 |
| `Formalization/Statements/Ch3Definitions.lean` | `8494b89e4a2c90c0ee41fd6fcc84796cfdb588b88320b352656e5dba5147b68c` | n/a | namespace grep only (name-clash check) |
| `Formalization.lean` | `697052168941c159e83d54a657a736da1d37e74290ab7f51ce6e04bf3b0e90a1` | n/a | grep: 436–437 import Ch2, Ch2Proofs |
| `Audit.lean` | `29f6cd54e69586325be78af79809bda1f1d1c2b0c52f03ad3746eb6e8c3d06f3` | n/a | whole (22 lines) |
| `AGENTS.md` | `1e28b54cc339575657234bd92b3e53f82c6d347ecd3bf37f0f000a4a4af12579` | n/a | provided as session context |
| Mathlib `Analysis/Normed/Group/Constructions.lean` (rev `32d24245c7a1`, read-only) | `7943f273c08767160be6e519b44c72ff9b89e90c0f8362a61f8bce26427313ab` | n/a | grep: 301 (Pi norm is `Finset.univ.sup ‖f b‖₊`), 344 |
| Mathlib `Probability/Independence/Basic.lean` (rev `32d24245c7a1`) | `0be38d08759189fdae35f959940495346535fac9ed136081788bdd758b2aa5c9` | n/a | grep: 144 (`def IndepFun`) |

The three hashes given in the brief (prelim.tex, Ch2.lean, Ch2Proofs.lean) are unchanged. commands.tex matches its pin.

## 2. Source reconstruction (written before opening any Lean file)

**Numbering.** In `nowfnt.cls` (lines 1331–1332), `lemma` shares the `theorem` counter and is numbered within chapters. `prelim.tex` is the second `\chapter` (intro is first). Non-commented lemmas in prelim.tex before line 956 are at lines 339, 458, 544 and 939, with no theorem environments. So `lem:Bernstein-prelim` (956) is **Lemma 2.5**, and Hoeffding (939) is Lemma 2.4.

**Ambient setting (prelim.tex:916–934, 30–36, 428–437).**
- State space 𝒮 = {1,…,S} is finite (line 34) and action space 𝒜 = {1,…,A}. The kernel is P: 𝒮×𝒜 → Δ(𝒮).
- For each pair (s,a), there are N independent samples s^{(i)}(s,a) ~ P(·|s,a), i = 1..N, i.i.d. (lines 916–921). The text does not say whether samples for different (s,a) are independent of each other.
- The empirical row is P̂(s'|s,a) = (1/N) Σ_i 1{s^{(i)}(s,a) = s'} (line 926). P̂ ∈ ℝ^{SA×S} stacks these rows (929–934). N ≥ 1 is implicit because the formula divides by N.
- Var_{P_{s,a}}(V) = Σ_{s'} P(s'|s,a) V_{s'}² − (Σ_{s'} P(s'|s,a) V_{s'})². This is the **population** variance under the true row (eq:defn-Var-Psa-V, 428–437). Var_P(V) ∈ ℝ^{SA} stacks these values.
- Notation (intro.tex:197–200): |·| and √· act entrywise on vectors, and vector ≤ means entrywise ≤. ‖V‖_∞ is the max-abs entry.

**Hypotheses of Lemma 2.5 (956–960, 969).**
- Fix a pair (s,a) and a finite set 𝒱 ⊂ ℝ_+^S of entrywise-nonnegative vectors. 𝒱 may be random, since the lemma only asks for independence. |𝒱| is its cardinality.
- 0 < δ < 1.
- Display 1: 𝒱 is independent of P̂_{s,a} (that row only). This is independence from the empirical row, not from the raw samples, although the two coincide in strength for this event.
- Display 2: 𝒱 is statistically independent of P̂ (the whole matrix).

**Conclusion of display 1 (eq:Bernstein-Psa-prelim, 962).** With probability **strictly greater** than 1−δ, the following holds simultaneously for all V ∈ 𝒱:
|(P̂_{s,a} − P_{s,a})V| ≤ √(2 log(4|𝒱|/δ)/N) · √Var_{P_{s,a}}(V) + 2‖V‖_∞ log(4|𝒱|/δ)/(3N).
This is a scalar, non-strict inequality. The constants are 2, 4, 2/3. The log argument is 4|𝒱|/δ, and the union-bound multiplicity is |𝒱|.

**Conclusion of display 2 (eq:Bernstein-P-whole-prelim, 972).** With probability strictly greater than 1−δ, the following entrywise inequality holds in ℝ^{SA}:
|(P̂ − P)V| ≤ √(2 log(4SA|𝒱|/δ)/N) · √Var_P(V) + (2‖V‖_∞ log(4SA|𝒱|/δ)/(3N)) 1_{SA}.
It holds for every (s,a) row, and (implicitly) simultaneously for all V ∈ 𝒱. The union-bound multiplicity is SA·|𝒱|.

**Mathematical check.** For V ≥ 0, the variable X = V_{s'} with s' ~ P_{s,a} satisfies |X − EX| ≤ ‖V‖_∞. The two-sided Bernstein tail is 2exp(−Nt²/(2(σ² + ‖V‖_∞ t/3))). Take t = √(2σ²L/N) + 2‖V‖_∞L/(3N); then the exponent is at most −L, because N t² ≥ Nx² + Ny(x+y) for x, y ≥ 0. With L = log(4|𝒱|/δ), each V fails with probability ≤ δ/(2|𝒱|), so the union fails with probability ≤ δ/2 < δ. The strict "greater than 1−δ" is therefore genuine, and the factor 4 (instead of the minimal 2) is slack. Display 2 follows in the same way with SA·|𝒱| events. A random 𝒱 is handled by conditioning on 𝒱, which uses independence from P̂_{s,a} (respectively from P̂). The printed lemma is **true** as stated.

**Ambiguities and possible errors in the printed statement.**
- (A1) Display 2 does not restate "simultaneously for all V ∈ 𝒱". The 4SA|𝒱| factor implies the simultaneous reading, which is also the strongest natural one.
- (A2) The source does not say whether samples for different (s,a) are independent. The union bound does not need this.
- (A3) The source does not say whether |𝒱| may be random. Conditioning handles it.
- (A4) N ≥ 1 and S, A ≥ 1 are implicit.
- (A5) The nonnegativity 𝒱 ⊂ ℝ_+^S matters for the constant 2/3. With signed entries, the one-sided range bound can reach 2‖V‖_∞.
- (Aside, not Lemma 2.5) The Lemma 2.4 display (945–946) has no `\label{eq:Hoeffding-Psa-prelim}`, but line 952 cites `\eqref{eq:Hoeffding-Psa-prelim}`. This is a dangling reference in the source.

## 3. Lean statement: `Formalization/Statements/Ch2.lean:230–275`

**Docstring (231–237).** It cites "Lemma 2.5 (Bernstein inequality), `lem:Bernstein-prelim`, `chapters/prelim.tex:956–978`, both displays". The label is correct, the number 2.5 is correct, and 956–978 is exactly the `\begin{lemma}`…`\end{lemma}` span. It refers to "the setting of Lemma 2.4" for the sampling model, but it does not cite the setting lines 916–934 or the variance definition 428–437 (see F6).

**σ-algebra on `State`.** The Prop has no `MeasurableSpace State` binder. Instead it contains `letI : MeasurableSpace State := ⊤` inside its body, at line 242 (display 1) and line 259 (display 2). The Prop therefore **fixes** the discrete σ-algebra on `State` and does not quantify over σ-algebras. This matches `sampleMeasure`, which is defined with a file-local `MeasurableSpace State := ⊤` (FiniteSampleDefinitions.lean:21, 29–30). For a finite carrier, ⊤ is the only sensible choice: it equals the Borel σ-algebra of the discrete topology.

**Definitions behind the statement (all followed to source).**
- `FiniteDistribution` (CoreDefinitions.lean:15–18): a real probability vector. `expectation d f = Σ_x d.prob x * f x` (24–25), which is P_{s,a}V.
- `variance d f = E_d[f²] − (E_d f)²` (VarianceDefinitions.lean:14–15). This is exactly eq:defn-Var-Psa-V, the population variance. `variance_nonneg` is proved (Variance.lean:40–42), so `Real.sqrt` never sees a negative argument.
- `sampleMeasure d N = Measure.pi (fun _ ↦ d.toPMF.toMeasure)` under ⊤ (FiniteSampleDefinitions.lean:25–30): the genuine i.i.d. product law. `toPMF` uses `ENNReal.ofReal (d.prob x)` with no renormalisation.
- `empiricalRow N hN ω` has `prob s = N⁻¹ Σ_i [ω i = s]` (33–35), which is exactly line 926. Decidable equality is the internal `Classical.decEq`, and there is no parameter to mis-instantiate.
- `‖V‖` for `V : State → ℝ` is Mathlib's Pi sup norm `Finset.univ.sup ‖V s‖₊` (Mathlib Constructions.lean:301), i.e. max_s |V s| = ‖V‖_∞. Ch2.lean has no local norm override (`open scoped Matrix` adds none), and the provider proof uses `norm_le_pi_norm`, which is consistent with this.
- `finiteFamilyBorel` (RandomFamilyBorel.lean:83–84) is `⨅ n, map (enumerationFamily n)` of the Borel structure on injective n-tuples. A set of finsets is measurable iff its preimage under every injective enumeration is Borel (96–99). For a singleton family {V(ω)} built from a Borel random vector, σ(family) = σ(V). This is the canonical quotient-Borel structure on finite subsets of ℝ^S.
- `rowVectorSpace = comap prob (Borel on State → ℝ)` (EmpiricalHoeffdingRandomFamily.lean:258–259). Singletons are measurable (262–284). Because the empirical row has finite range, independence with respect to `rowVectorSpace` is equivalent to independence with respect to ⊤ (`indepFun_finiteRange_to_discrete`, 235–254). So the hypothesis is exactly "𝒱 independent of P̂_{s,a}".
- `marginalMatrixVectorSpace` (BernsteinMatrixMarginals.lean:45–47) is `letI rowVectorSpace; inferInstance`, i.e. `MeasurableSpace.pi` with `rowVectorSpace` on every row. The local `letI` should take priority over the file-level `local instance … := ⊤` (line 12). The proof of `marginalMatrixVectorSpace_eval` (50–54, `exact measurable_pi_apply i` against codomain `rowVectorSpace`) would only typecheck if that is the case (needs Lean-side confirmation).

### 3a. Display 1 field-by-field (Ch2.lean:239–254)

| Field | Source (prelim.tex) | Lean | Verdict |
|---|---|---|---|
| Row | P_{s,a}, fixed (s,a) (958) | `d : FiniteDistribution State` (240) | match |
| State space | finite 𝒮 (34) | `State : Type u` `[Fintype State]` (239); a `FiniteDistribution` forces nonemptiness | match |
| Probability space | implicit | arbitrary `Ω`, `μ`, `[IsProbabilityMeasure μ]` (239–240) | match |
| N | N ≥ 1 implicit (920, 926) | `N : ℕ`, `hN : 0 < N` (241) | match |
| δ | 0 < δ < 1 (958) | `0 < δ → δ < 1` (241) | match |
| Samples | N i.i.d. draws from P_{s,a} (919–920) | `Measurable draw`, `μ.map draw = d.sampleMeasure N` (243) | match (exact i.i.d. joint law) |
| P̂_{s,a} | eq. at 926 | `empiricalRow N hN (draw ω)` (249, 252) | match |
| 𝒱 | finite set, possibly random (958) | `family : Ω → Finset (State → ℝ)`; cardinality may be random and the set may be empty (244) | match / slightly more general (random card) |
| 𝒱 ⊂ ℝ_+^S | 958 | `∀ ω V, V ∈ family ω → ∀ s, 0 ≤ V s` (250) | match |
| Measurability of 𝒱 | not in source (informal) | `Measurable family` w.r.t. `finiteFamilyBorel` (245–246) | regularity premise, canonical (NOTE F4) |
| Independence | 𝒱 ⫫ P̂_{s,a} (959) | `IndepFun family (empiricalRow ∘ draw)` with `finiteFamilyBorel` × `rowVectorSpace` (247–249) | match |
| Probability | "greater than 1−δ", strict (959) | `1 - δ < μ.real {…}` (251) | match; the event is proved measurable in the provider chain, so `μ.real` is not an outer-measure artefact |
| Quantifier | simultaneously ∀ V ∈ 𝒱 (966) | `∀ V ∈ family ω` inside the event (251) | match |
| LHS | \|(P̂_{s,a} − P_{s,a})V\| (962) | `\|(empiricalRow …).expectation V - d.expectation V\|` (252) | match |
| Relation | ≤ (962) | `≤` (252) | match |
| Variance term | √(2 log(4\|𝒱\|/δ)/N) · √Var_{P_{s,a}}(V) | `Real.sqrt (2 * Real.log (4 * (family ω).card / δ) / N) * Real.sqrt (d.variance V)` (253) | match (population variance under the true row) |
| Range term | 2‖V‖_∞ log(4\|𝒱\|/δ)/(3N) | `2 * ‖V‖ * Real.log (4 * (family ω).card / δ) / (3 * N)` (254) | match (`‖·‖` = sup norm) |
| Junk values | n/a | N > 0 so no division by zero; card = 0 makes the event vacuous; card ≥ 1 gives log argument > 4; variance ≥ 0 | none |

### 3b. Display 2 field-by-field (Ch2.lean:255–275)

| Field | Source | Lean | Verdict |
|---|---|---|---|
| Spaces | finite 𝒮, 𝒜 | `State Action : Type u`, `[Fintype _]`, **`[Nonempty State] [Nonempty Action]`** (255–256) | extra premises that exclude only trivial cases (NOTE F2). `Action` shares universe `u` with `State` (NOTE F3) |
| Kernel P | P ∈ ℝ^{SA×S} | `d : State × Action → FiniteDistribution State` (257) | match |
| N, δ | as above | `hN : 0 < N`, `0 < δ`, `δ < 1` (257–258) | match |
| Sampling | for each (s,a), N i.i.d. draws from P(·\|s,a); cross-row independence unspecified (916–921) | `draw : Ω → State × Action → Fin N → State`, `Measurable draw`, `∀ i, μ.map (fun ω ↦ draw ω i) = (d i).sampleMeasure N` (260–261) | weaker hypothesis, so a stronger theorem: arbitrary cross-row dependence is allowed (disclosed in the docstring) |
| P̂ | rows as above (929–934) | `fun i ↦ empiricalRow N hN (draw ω i)` (268, 271) | match |
| 𝒱 nonneg, finite, random | 958 | same as display 1 (262, 269) | match |
| Independence | 𝒱 ⫫ P̂ (whole matrix) (969) | `IndepFun family (fun ω ↦ fun i ↦ empiricalRow …)` with `marginalMatrixVectorSpace` = product of `rowVectorSpace` (265–268) | match (independence from the whole matrix, product σ-algebra) |
| Probability | strict > 1−δ (969) | `1 - δ < μ.real {…}` (270) | match |
| Quantifiers | entrywise over all (s,a); simultaneously over 𝒱 (implicit, A1) | `∀ i : State × Action, ∀ V ∈ family ω` (270) | match (strongest natural reading) |
| LHS / relation | \|(P̂ − P)V\| ≤ entrywise | `\|… - (d i).expectation V\| ≤` (271) | match |
| Log argument | 4SA\|𝒱\|/δ | `4 * Fintype.card State * Fintype.card Action * (family ω).card / δ` (272, 274) | match (ℕ leaves cast to ℝ; the value does not depend on cast placement) |
| Variance term | √(2 log(·)/N) √Var_P(V) entrywise | `Real.sqrt (2 * Real.log (…) / N) * Real.sqrt ((d i).variance V)` (272–273) | match |
| Range term | (2‖V‖_∞ log(·)/(3N)) 1_{SA} | `2 * ‖V‖ * Real.log (…) / (3 * N)` (274–275) | match |

**Satisfiability (non-vacuity).** The hypotheses of both displays can be satisfied, so the Prop has real content.
- Display 1: take Ω = Fin N → State, μ = `d.sampleMeasure N`, `draw = id`, and a constant family {V} with V ≥ 0. A constant family is independent of everything.
- Display 2: take Ω = State×Action → Fin N → State, μ = `Measure.pi (fun i ↦ (d i).sampleMeasure N)`, and `draw = id`. The coordinate marginals are correct.

## 4. Wrapper and providers

**Wrapper `Lemma2_5_holds` (Ch2Proofs.lean:120–131).**
- Display 1: `intro State _ Ω _ μ _ d N hN δ hδ hδ1; letI : MeasurableSpace State := ⊤; intro …; exact d.randomBorelFamily_bernstein_source … (Filter.Eventually.of_forall hV)`.
- Display 2: `intro State Action _ _ _ _ Ω _ μ _ d N hN δ hδ hδ1; letI … ⊤; intro …; exact randomBorelFamily_matrixBernstein_of_rowMarginals … (Filter.Eventually.of_forall hV)`.
- The wrapper's `letI ⊤` only re-creates the same instance that the Prop body already fixes with its internal `letI` (§3). It does **not** specialise a universally quantified statement: the Prop has no σ-algebra binder for `State`, and Lean would reject a mismatch.
- The only adaptation is pointwise nonnegativity becoming `∀ᵐ`, which goes from stronger to weaker as it should.
- The wrapper applies the library theorem and does not restate or re-prove it, which conforms to AGENTS.md.
- `theorem Lemma2_5_holds : Lemma2_5` has no explicit universe annotation, unlike `Lemma2_12_holds : Lemma2_12.{u, v}`. Lean should generalise the leftover universe metavariables into parameters, so this proves `Lemma2_5` at all universes (needs Lean-side confirmation; NOTE F8).

**Provider 1: `randomBorelFamily_bernstein_source` (BernsteinFamily.lean:315–333).**
- Its signature is identical to display 1, except that nonnegativity is `∀ᵐ` (weaker hypothesis).
- Proof: `bernsteinRadius_eq_source` rewrites √(2L·Var/N) into √(2L/N)·√Var using `variance_nonneg` (20–29). It then applies `randomBorelFamily_bernstein_success_gt` (280–312), which works as follows:
  - It upgrades independence to the discrete σ-algebra on the finite-range row (`indepFun_finiteRange_to_discrete` with `rowVectorSpace_singletons`).
  - It applies `randomFamily_bernstein_success_gt` (189–237). That theorem uses `indepFun_iff_map_prod_eq_prod_map_map` to turn the joint law of (family, row) into a product, then integrates the per-family bound (`product_supportedBernsteinBad_lt`, 149–184, via `Measure.prod_apply` and `lintegral_strict_mono`).
  - The per-family bound is `empiricalRow_bernsteinFamily_success_gt` (59–92): a union bound with failure ≤ δ/(2k) per vector (`bernsteinViolation_le`, 36–56), so the total is ≤ δ/2 < δ. The empty family is handled separately.
- The per-vector bound `empiricalRow_source_threshold_strict` (SharpEmpiricalBernstein.lean:247–297) is built as follows:
  - Taylor majorant e^z ≤ 1 + z + z²/(2(1−|z|/3)) for |z| < 3 (12–48, via the exp series in Mathlib).
  - The resulting MGF bound for the centered row variable, with B = ‖V‖ and V ∈ [0, B] (58–102).
  - Chernoff on the i.i.d. product: `empiricalRow_chernoff_mgf`, EmpiricalBernstein.lean:136–156, built on Mathlib `measure_ge_le_exp_mul_mgf` and `iIndepFun.mgf_sum`.
  - Optimisation at u = ε/(σ² + Bε/3) (125–154).
  - Reflection for the lower tail (157–181), then the two-sided bound and the threshold t = x + y with N t² ≥ 2L(σ² + Bt/3) (213–243). Zero-variance and B = 0 cases go through Chebyshev (206–210, 264–297).
- This is my reconstruction of the source argument, with the same constants and no extra assumption. The conclusion is not weakened, and there is no fallback definition. The empirical row, variance and sampling law are the objects defined in §3.

**Provider 2: `randomBorelFamily_matrixBernstein_of_rowMarginals` (BernsteinMatrixMarginals.lean:82–159).**
- Its signature is identical to display 2 (`MarginalRowIndex` is an `abbrev` for `State × Action`, and `marginalEmpiricalMatrix` unfolds to the row map), except that nonnegativity is `∀ᵐ`.
- Proof:
  - Set η = δ/(SA), using `[Nonempty State] [Nonempty Action]` to get SA ≥ 1.
  - Derive per-row independence from whole-matrix independence by composing with the measurable evaluation (113–120). Each row has the correct i.i.d. law (`hrowlaw`).
  - Apply the display-1 core with η, so each row fails with probability < η (123–133).
  - Take a union over the SA rows to get < δ (134–143).
  - Use `hlog`: 4k/η = 4·S·A·k/δ (144–148).
  - The failure event is measurable via `marginalBernsteinBad_measurable` (58–79).
- Exact derivation, with no extra assumption beyond the Nonempty instances, which the Prop also carries.

**Forbidden-token grep.**
- I computed the local import closure of `Formalization.Statements.Ch2Proofs` by recursively parsing `import Formalization.*` lines: 149 modules. The closure of `Ch2.lean` together with `BernsteinMatrixMarginals` alone is 32 modules.
- The pattern `\bsorry\b|\badmit\b|^\s*axiom\b|\baxiom\s|\bopaque\b|implemented_by|\bunsafe\b|native_decide|@\[extern|ofReduceBool` matched nothing in any of the 149 files.
- A case-insensitive sweep (also covering `debug.skipKernelTC` and `set_option … kernel`) found only prose hits: "admits" (GenerativeLowerBoundFiniteKLDataProcessing.lean:9, SharpEmpiricalBernstein.lean:11) and "externally"/"external" (FreedmanNaturalHistory.lean:4, 61).
- The axiom audit (`lake env lean Audit.lean`) was **not run**. `Audit.lean` collects transitive axioms of every `StatisticalRL.*` constant against {propext, Classical.choice, Quot.sound}, and `Formalization.lean:436–437` imports both Ch2 statement files, so `Lemma2_5_holds` would be covered.

## 5. Findings

No BLOCKING or MAJOR findings. The Lean Prop states the printed Lemma 2.5, both displays, with identical constants, strictness, log arguments, variance object (population variance under the true row), norm (sup norm), δ range, N range, nonnegativity, and independence hypothesis. Where it differs from the source it only removes a hypothesis: it allows arbitrary cross-row dependence and random cardinality.

- **F1 — MINOR (project policy, not source fidelity): the statement file imports proof modules.**
  - AGENTS.md says `Formalization/Statements/ChN.lean` "imports definition modules only and contains no proofs".
  - This working-tree change adds `import Formalization.Probability.BernsteinMatrixMarginals` (Ch2.lean:6). That module contains the display-2 provider theorem itself, and through `BernsteinFamily` and `SharpEmpiricalBernstein` it pulls in the entire display-1 proof chain.
  - Ch2.lean already imported the proof modules `RandomFamilyBorel` and `EmpiricalHoeffdingRandomFamily` at HEAD (used by Lemma2_4 and Lemma2_6).
  - Consequence: the statement index is no longer independent of the proof modules it is meant to be checked against. A definition in those modules could be changed in a way that silently changes the meaning of the Prop.
  - Fix: move `finiteFamilyBorel`, `rowVectorSpace` and `marginalMatrixVectorSpace` (plus the `FamilyEnumeration` / `enumerationFamily` definitions they need) into `*Definitions` modules, or inline `marginalMatrixVectorSpace` as `letI := rowVectorSpace; MeasurableSpace.pi`.
- **F2 — NOTE: hidden premises `[Nonempty State] [Nonempty Action]` in display 2 (Ch2.lean:255–256).**
  - These premises are not in the source and are not mentioned in the docstring.
  - The excluded cases are trivially true. If either type is empty, `State × Action` is empty, so `∀ i` is vacuous, and the event is `univ` with `μ.real univ = 1 > 1−δ`.
  - The premises come from the provider's section variables. They do not weaken the result in any meaningful way, and the source takes S, A ≥ 1 for granted. A docstring mention would be enough.
- **F3 — NOTE: universe coupling in display 2.**
  - Display 2 has `Action : Type u`, the same universe as `State`, while the provider allows independent universes.
  - This has no effect on source fidelity, since the source has no universes, but the index entry is slightly less general than the export.
- **F4 — NOTE: formal regularity premises.**
  - `Measurable family` (w.r.t. `finiteFamilyBorel`) and `IndepFun` w.r.t. `finiteFamilyBorel` × `rowVectorSpace` (or its product) are formalisation choices that are absent from the informal source.
  - I checked that these structures are canonical:
    - quotient-Borel structure on finite subsets;
    - σ(singleton family) = σ(vector);
    - families built from finitely many Borel random vectors are measurable (partition by equality pattern);
    - for the finite-range row, independence w.r.t. `rowVectorSpace` is equivalent to discrete independence.
  - So the independence premise is neither stronger nor weaker than the source's "independent of P̂_{s,a}".
- **F5 — NOTE: generalisations (stronger than the source; disclosed).** Display 2 allows arbitrary dependence across rows, and both displays allow a random |𝒱|. These are weaker hypotheses than the source's, and the docstring discloses the cross-row one.
- **F6 — NOTE: citation incompleteness.**
  - The docstring cites only 956–978 and refers to "the setting of Lemma 2.4". The sampling model and P̂ (prelim.tex:916–934) and Var_{P_{s,a}} (428–437) are not cited.
  - The Lemma2_4 docstring cites only 939–950, not 916–934, whereas the Lemma2_6 docstring does cite 916–927.
  - AGENTS.md only requires the label and range, which are present.
- **F7 — NOTE (source).**
  - Display 2 omits "simultaneously for all V ∈ 𝒱" (A1). The Lean statement takes the simultaneous reading, which is the strongest one and is consistent with the 4SA|𝒱| factor. I did not find a source error in Lemma 2.5: the printed lemma is true, with a factor-2 slack inside the log.
  - Aside on Lemma 2.4: its display has no `\label`, but line 952 cites `eq:Hoeffding-Psa-prelim`. This is a dangling cross-reference in the source.
- **F8 — NOTE: `Lemma2_5_holds` has no explicit universe annotation (Ch2Proofs.lean:120).** It relies on Lean generalising universe metavariables in the header. This should be fine, but it needs Lean-side confirmation that the declaration's type is `Lemma2_5.{u_1,u_2}` with both levels free.

## 6. Items needing Lean-side confirmation

1. `Ch2.lean` and `Ch2Proofs.lean` compile at the pinned toolchain, and `Lemma2_5_holds : Lemma2_5` type-checks (not compiled here).
2. `lake env lean Audit.lean` passes, so that the transitive axioms of `StatisticalRL.Statements.Lemma2_5_holds` are within {propext, Classical.choice, Quot.sound} (not run).
3. `marginalMatrixVectorSpace` elaborates to `MeasurableSpace.pi` with `rowVectorSpace` coordinates. The `letI` local instance should take priority over the file-level `local instance bernsteinMatrixRowMeasurable := ⊤`, and the proof of `marginalMatrixVectorSpace_eval` would fail otherwise.
4. `‖V‖` in Ch2.lean elaborates to Mathlib's Pi sup norm (no other `Norm (State → ℝ)` instance in scope).
5. `Lemma2_5_holds` is universe-polymorphic (F8).
6. Whether `marginalMatrixVectorSpace` carries `[Nonempty …]` instance arguments, which would explain why they appear in the Prop (F2).

VERDICT: PASS-WITH-FINDINGS — both displays of the Lean `Lemma2_5` state the printed Lemma 2.5 exactly. The constants, strictness, population variance, sup norm, log arguments and independence hypothesis all match, and the only differences are harmless or generalising: trivially satisfied Nonempty premises and allowed cross-row dependence. The remaining issues are a project-policy MINOR (the statement file imports proof modules) and NOTEs.

## 7. Agreement with the Lemma 2.4 report and disclosure check (read only after Sections 1–6 were written)

Files read for this section:
- the private original of `docs/critic-lemma2-4-hoeffding.md` (SHA256 of the original `e687856696c8f510ed1519c1cec72bde8c07b472e76d4800ed7f4f5753170553`, 266 lines)
- `docs/SOURCE-ISSUES.md` (SHA256 `3d113729e6b40874e1692cb9f3d55f02bf701c2ae5e95431f0791c3c28014b9a`, 773 lines; grep for `prelim`, `Bernstein`, `Lemma 2.5`, `Lemma2_`, `956`, `972`, `Nonempty`, `import`, `universe`, `cross-row`; section headings; the "Statement-index scope disclosures" block at 389–466)

**Agreement on the shared random-family setting.** I agree with the Lemma 2.4 report on every shared point:
- The `⊤` σ-algebra on `State` is fixed inside the Prop, and every provider-file local instance is `⊤`.
- `sampleMeasure` is the genuine i.i.d. product law.
- `empiricalRow` matches prelim.tex:926.
- `finiteFamilyBorel` is the canonical quotient-Borel structure on finite subsets: it agrees with the Effros/Hausdorff structure via a sorting section, and natural random families are measurable in it.
- `rowVectorSpace` independence is equivalent to discrete independence for the finite-range row.
- The event is proved measurable, so `μ.real` is a genuine probability.
- The strict "> 1−δ" is genuinely proved.
- The statement file importing proof modules is a MINOR AGENTS.md process deviation.

**Disagreements and additions.**
- (a) The Lemma 2.4 report (its F1) says HEAD's `Ch2.lean` already imported `RandomFamilyBorel` / `EmpiricalHoeffdingRandomFamily` "for `Lemma2_11`". At HEAD, the entry that uses `finiteFamilyBorel` / `rowVectorSpace` is `Lemma2_6` (`git show HEAD:Formalization/Statements/Ch2.lean`, lines 185–196). `Lemma2_11` uses only `PrelimFano` definitions and `klDiv`. This is a factual slip in that report and does not change its conclusion.
- (b) The Lemma 2.4 report observes that the Hoeffding provider only needs the coarser `familyTestSpace`. The Bernstein providers export no such coarser route: `randomBorelFamily_bernstein_success_gt` works directly with `finiteFamilyBorel`, via `code := id` and the enumeration-measurability lemmas. For Lemma 2.5, therefore, the independence premise w.r.t. `finiteFamilyBorel` is the weakest premise the library offers. I still judge it canonical (F4), so this is a NOTE only.
- (c) The Lemma 2.4 report did not mention that the Lemma 2.4 display has no `\label{eq:Hoeffding-Psa-prelim}`, although prelim.tex:952 cites it. I flag this as a source aside under F7. It is cosmetic and does not affect Lemma 2.5.

**Disclosure status in `docs/SOURCE-ISSUES.md`.** The file has no Chapter 2 entries at all.
- F1 (statement file imports proof modules, newly including the Lemma 2.5 provider module `BernsteinMatrixMarginals`): **not disclosed**. It is a process item rather than a source issue, so it belongs in the lead's integration notes or `docs/PROGRESS.md`, not `SOURCE-ISSUES.md`.
- F2 (`[Nonempty State] [Nonempty Action]`), F3 (universe coupling), F4 (regularity σ-algebras), F5 (generalisations), F6 (citation scope), F8 (wrapper universes): **not disclosed, and no disclosure is required**. In each case the Lean entry implies the printed result, so under AGENTS.md this is not a source-fidelity discrepancy. A short docstring mention of F2 would still help readers.
- F7 (display 2 lacks "simultaneously for all V"; the Lemma 2.4 label is missing): **not disclosed**. These are source presentation issues, not mathematical errors. An optional cosmetic entry is possible, but nothing is required.
- No `_corrected` or `_restricted` variant exists or is needed for Lemma 2.5.
