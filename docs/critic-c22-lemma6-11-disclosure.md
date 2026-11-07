# Critic report: C22 and the Lemma 6.11 disclosure texts

Public copy of the independent critic report; local paths removed.

- Date (UTC): Fri Nov  6 19:38:04 UTC 2026 (from `date -u` at review start)
- Reviewer: independent Claude critic subagent (did not write the reviewed text)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106`. The reviewed texts are uncommitted working-tree changes; `LCBQUsefulSeries.lean` and `LowerBoundFamilyKL.lean` are untracked.
- Mode: source-only; no Lean run. No lake, `scripts/check.py`, `lean-local.sh` or LSP was used. The only computation was plain `python3 -I` on two scratch scripts outside the project.
- Independence: I formed and wrote down the judgement below (sections 2–4) from the pinned source, the reviewed texts and the Lean statement. Only after that did I read `docs/critic-lemma6-11-restricted.md`, which section 6 compares against.

## 1. Files read (SHA-256)

Both pinned `.tex` hashes match `source/provenance.json`: line 39 (`chapters/offlineRL.tex`) and line 41 (`chapters/prelim.tex`).

| File | SHA-256 | Lines used |
|---|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches pin) | 1650–1800, 2200–2420, 2436–2519, 2825–2871, 4668–4790, 5680–5790; theorem-environment scan up to 2300 |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` (matches pin) | 45 (γ ∈ [0,1)), 1333–1348 (Lemma 2.13) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` | pin lines 39, 41 |
| `docs/SOURCE-ISSUES.md` | `3fdb5ecaab677a10c43832605b0fe05494c874f5df505371ac53edfda591cfbf` | 385–420, 700–735, 740–797; `git diff` |
| `Formalization/Statements/Ch6.lean` | `1e57492d2ee36eea13a16a2c011f584c919af91e8a5552957f45816fbf7ae925` | 150–212 |
| `Formalization/Statements/Ch6Proofs.lean` | `d80a704b5693f0181a8b6f2df3c9bd3169eadfc87506392e51995b169b147542` | 101–103 |
| `Formalization/OfflineRL/LCBQUsefulSeries.lean` | `02a9397ce753f6d725d86ee083513243de0b79e615941c07d1f589c85c75678e` | 1–70; grep for `84` |
| `Formalization/OfflineRL/LowerBoundFamilyKL.lean` | `c80fff1463b59bbba74aa28f706a0cf68a0e6f9e02a130c4478a77a7c1dc6b15` | 1–25 |
| `Formalization/MDP/DiscountedOccupancy.lean` | `029a6c51d60dfd7e637ec212394354a7471afcfd1bbf9ddf03b432b9e0bf9606` | 1–80 (`occupancyStateAt`, normalised `discountedStateOccupancy`) |
| `docs/COVERAGE.md` | `246734222543f81d85c6faf816f110b617b3878b20c84d3898d6c09b7f6783a6` | rows 92–93; `git diff` |
| `docs/PROGRESS.md` | `b5376c213708151a86146ca6b9fd5476fff202e1a85cbbf5b190e42d17dbe2a4` | 1–30 |
| `docs/named-result-status.json` | `6a96b832e40d131820d70176fdb1c9f44341c1ba5e9fb6e419604ad3854dadc6` | key counts only |
| `AGENTS.md` | `1e28b54cc339575657234bd92b3e53f82c6d347ecd3bf37f0f000a4a4af12579` | whole file (given in context) |
| private original of `docs/critic-lemma6-11-restricted.md` | `aec72c77e70ff3175e1041d591f5e958743ec25d4e07b3dbc0c1edd98e395496` | whole file, read last |
| scratch `c22_checks.py` (outside the project) | `9ee6177144809b61d31b7ae765b765b73c9d4035b063114de8fdf6bf73554684` | n/a |
| scratch `c21_check.py` (outside the project) | `59b77ef54d9e5261cb4f0feae3a1a337ee0484fc29d3660492a6d9906609d86c` | n/a |

The full scratch path is (local scratch path omitted).

## 2. Source facts, reconstructed independently

- **Lemma 6.11** (`lemma:useful`) is the environment at `offlineRL.tex:2292–2300`, an exact locator. It says "Consider any 0<δ<1", fixes H and κ, and claims, for every W ≥ 0:

  Σ_j κ^j ρᵀ P_{π⋆}^j W ≲ ⟨d_ρ^⋆, W⟩/(1−γ) + δ‖W‖_∞/(S T⁴ (1−γ)).

  It does not mention Theorem 6.8's sample-size condition. The numbering 6.11 is consistent with the shared theorem/lemma counter: the environments at 456, 872, 899, 1079, 1104, 1147, 1529, 1754, 1866, 1907 and 2292 are 6.1–6.11.
- **H** is defined at 1669–1672, with `\begin{equation}` at 1669, the label at 1671, and the enclosing `subequations` opening at 1666–1667:

  H = ⌈4/(1−γ) · log(SAT/δ)⌉.
- **κ** is defined at 2284–2289 as γ(1+1/H)³ < 1, and line 2289 says the inequality "follows immediately from the choice of H".
- **d_ρ^⋆** is normalised. The proof at 4707–4712 writes d_ρ^⋆ = (1−γ) Σ_j γ^j ρᵀ P_{π⋆}^j. So ⟨d_ρ^⋆, 1⟩ = 1.
- **The Lean `discountedStateOccupancy`** is also normalised: `(1 - γ) * ∑' t, γ^t * occ_t(s)` (DiscountedOccupancy.lean:62–64).
- **Theorem 6.8** (1754–1772) has these hypotheses:
  - 0<δ<1;
  - ε ∈ (0, 1/(1−γ)];
  - C⋆ ≥ 1;
  - γ ∈ [0,1), from prelim.tex:45, with no further restriction in the theorem;
  - T ≥ c₂ S C⋆ log(SAT/((1−γ)δ)) / ((1−γ)⁵ ε²) (line 1767), for "some large enough universal constant c₂".
- **The proof of Lemma 6.11** (4674–4782) uses three facts:
  - (1+1/H)^{3H} ≤ e³;
  - γ^H ≤ exp(−H(1−γ)) ≤ δ/(ST⁴);
  - "1−κ ≳ 1−γ".

  Only the κ facts depend on the size of log(SAT/δ).

## 3. Numeric and analytic checks

All outputs below come from `python3 -I c22_checks.py` and `python3 -I c21_check.py`.

**Check 1: the C22 counterexample.** Inputs: S=A=T=1, δ=0.9, γ=0.3.
- 4 log(1/δ)/(1−γ) = 0.60206, so H = 1 and κ = 2.4.
- For W ≡ 1, the left side Σ 2.4^j diverges.
- The right side is (1 + δ/(ST⁴))/(1−γ) = 2.7143, times C.
- **Confirmed.**

**Check 2: the γ = 1/8 − η family.** Inputs: S=A=T=1, δ=0.9.
- H = 1 on the whole family, because 4 log(1/0.9)/(7/8) = 0.4816 < 1.
- κ = 1 − 8η exactly. Sample values of η: 0.1, 0.05, 0.01, 1e−3, 1e−4, 1e−6, 1e−9.
- The left side is 1/(1−κ) = 1/(8η): 1.25, 2.5, 12.5, 125, 1250, 1.25e5, 1.25e8.
- The right side divided by C is 1.9/(7/8+η). It increases to its supremum 1.9/(7/8) = **2.1714** as η → 0.
- "Below about 2.2·C" is correct. It relies on the normalised d, which the source uses, and on δ = 0.9.
  - For general δ<1 the bound would be 2/(7/8) = 2.286. H = 1 near γ = 1/8 needs δ ≥ e^{−7/32} = 0.8035.
  - C22 does say "with the same S, A, T, δ", so the figure 2.2 is right as written.
- The range of η is implicitly 0 < η < 1/8.
- **Confirmed.**

**Check 3: the sample-size example.** Inputs: S=A=T=1, γ=0, C⋆=ε=1.
- The tuple is inside Theorem 6.8's hypotheses: γ=0 ∈ [0,1), ε = 1 = 1/(1−γ), and C⋆ = 1.
- The condition reads 1 ≥ c₂ log(1/δ), i.e. δ ≥ e^{−1/c₂}:

  | c₂ | condition holds for δ ≥ | log(SAT/δ) at the midpoint δ |
  |---|---|---|
  | 1 | 0.3679 | 0.380 |
  | 10 | 0.9048 | 0.0488 |
  | 100 | 0.99005 | 0.00499 |
  | 1e4 | 0.99990 | 5e−5 |

  In every case log(SAT/δ) < 1.
- **Confirmed.** Note that κ = 0 at γ = 0, so this tuple is not a point where the lemma fails (see F6).

**Check 4: the premise log(SAT/δ) ≥ 1 is sufficient, with the constant 84.**
- Analytic argument. Put x = 1−γ.
  - H ≥ 4/x gives κ ≤ (1−x)(1+x/4)³ =: f(x).
  - f′(x) = (1+x/4)²(−1/4 − x) < 0 and f(0) = 1, so κ < 1.
  - g(x) = 1 − f(x) − x/4 has g(0) = 0 and g′ ≥ 0, so 1−κ ≥ (1−γ)/4.
  - γ^H ≤ e^{−4L} = (δ/SAT)⁴ ≤ δ/(ST⁴).
  - Hence the left side is at most 21·A₁ + 4·21·A₂ ≤ 84(A₁+A₂), where A₁ and A₂ are the two right-side terms. For reference, e³ = 20.09 and 4e³ = 80.34.
- Numeric grid: SAT ∈ {1,2,3,5,10,100}, δ ∈ [1e−6, 1−1e−6] with L ≥ 1, and γ ∈ [0, 1−1e−8].
  - 0 violations of κ<1, of 1−κ ≥ (1−γ)/4, and of γ^H ≤ δ/SAT.
  - The minimum of (1−κ)/(1−γ) is 0.2518.
- **Confirmed.**

**Check 5: the equivalence and the uncovered region.**
- log(SAT/δ) ≥ 1 ⇔ SAT/δ ≥ e ⇔ δ ≤ SAT/e, since δ > 0. **Confirmed.**
- The premise fails iff δ > SAT/e. Because δ < 1, this forces SAT < e, so SAT ∈ {1,2}.
  - SAT/e is 0.368 for SAT = 1, 0.736 for SAT = 2, and ≥ 1.10 for SAT ≥ 3.
- So "SAT ≤ 2 and δ > SAT/e" is exactly the uncovered region. The "SAT ≤ 2" part is implied by δ > SAT/e and is redundant but harmless. **Confirmed.**

**Check 6: the sharp threshold for κ < 1, which the texts do not need.**
- Analytically, f_L(x) = (1−x)(1+x/(4L))³ has f′_L(0) = 3/(4L) − 1.
  - So κ < 1 for every γ iff L ≥ 3/4.
  - For L < 3/4, κ > 1 when γ is close to 1, even with the ceiling.
- Numeric evidence:

  | SAT | δ | L | max κ found | at γ | H |
  |---|---|---|---|---|---|
  | 1 | 0.5 | 0.693 | 1.00181 | 0.95 | 56 |
  | 1 | 0.48 | 0.734 | 1.00014 | 0.99 | — |
  | 2 | 0.95 | 0.744 | 1.0000168 | 0.995 | — |

  For L ≥ 0.755 no κ > 1 was found.
- So for SAT = 1 the left side is already +∞ for some γ whenever δ > e^{−3/4} ≈ 0.472. For SAT = 2 this needs δ > 2e^{−3/4} ≈ 0.945, and for SAT ≥ 3 it never happens.
- For any L₀ > 3/4, the premise L ≥ L₀ gives 1−κ ≥ (1−γ)(1 − 3/(4L₀)), hence the lemma with a constant that depends on L₀. This confirms "sufficient, not necessary".

**Check 7: the corner inside Theorem 6.8 (SAT ≤ 2, δ > SAT/e) is resolved on paper.**
- Bound γ. In the corner, T ≤ SAT ≤ 2.
  - ε ≤ 1/(1−γ) gives (1−γ)⁵ε² ≤ (1−γ)³ ≤ 1.
  - Also S, C⋆ ≥ 1, and log(SAT/((1−γ)δ)) > log(1/(1−γ)) ≥ γ.
  - So Theorem 6.8's condition gives T > c₂γ, hence γ < 2/c₂.
  - Numerically, the largest feasible γ is 0.0899 for c₂ = 16, 0.0519 for c₂ = 32 and 0.0187 for c₂ = 100.
- Bound κ. κ ≤ 8γ < 16/c₂, so κ < 1/2 once c₂ ≥ 32.
- Bound the left side by the right side:
  - The left side is at most ρᵀW + κ/(1−κ)·‖W‖ ≤ ρᵀW + ‖W‖.
  - ρᵀW ≤ ⟨d,W⟩/(1−γ), because d ≥ (1−γ)ρ entrywise and W ≥ 0.
  - δ/(ST⁴(1−γ)) ≥ δ/(ST⁴) > A/(eT³) ≥ 1/(8e) = 0.0460.
  - Hence the left side is at most 8e·(right side), and 8e ≈ 21.75 < 84.
- **Conclusion.** Under Theorem 6.8's hypotheses with c₂ ≥ 32:
  - κ < 1 holds everywhere;
  - Lemma 6.11's conclusion holds everywhere, with the same constant 84.

  The printed error is confined to two things:
  - the standalone lemma's hypothesis list;
  - the justification "immediately from the choice of H".

  This argument is not formalized.

**Check 8: C21 numbers.**
- At u = 0.99, v = 0.5: KL = 0.63715 and (u−v)²/(u(1−v)) = 0.48505. **Confirmed.**
- The two Lemma 2.13 bounds, (u−v)²/(v(1−v)) and (u−v)²/(u(1−u)), are each ≥ (u−v)²/(u(1−v)) when u > v. **Confirmed** algebraically.
- Then I swept a grid over the a=0 case of the proof's actual region:
  - 2/3 ≤ γ < 1;
  - t = 224(1−γ)ε/γ ∈ (0, 1/2];
  - α = 1 − 1/(C(S−1)) ∈ (1/2, 1);
  - u = αp + 1−α and v = αq + 1−α.

  The maximum of KL/[(u−v)²/(u(1−v))] was 0.9097, so the cited inequality appears to hold on that region. This is a grid, not a proof.

## 4. Findings

**F1 — MAJOR. C22 leaves "open" a corner that Theorem 6.8's own hypotheses close, and it does not say that Theorem 6.8 is unaffected.**
- Where:
  - SOURCE-ISSUES C22, paragraph 2: "The lemma's conclusion may still hold in that corner inside Theorem 6.8, but that needs its own argument".
  - SOURCE-ISSUES C22, the proposed correction: "check that Theorem 6.8 either assumes it or treats δ > SAT/e separately".
  - SOURCE-ISSUES C22: "**Open:** Theorem 6.8's uses … with SAT ≤ 2 and δ > SAT/e".
  - Echoed in COVERAGE row 92, `Ch6.lean:194–196` and `LCBQUsefulSeries.lean:14–16`.
- Every sentence is literally true. In formal terms the corner is not covered by `Lemma6_11_restricted`.
- But the entry stops where a three-line argument (Check 7) settles the question:
  - with c₂ ≥ 32, the sample-size condition forces γ < 2/c₂ in the corner;
  - so κ < 1/2, and the lemma's conclusion holds with constant 8e < 84;
  - and κ < 1 holds on the whole of Theorem 6.8's hypothesis set.
- As written, a reader of C22, the COVERAGE row or PROGRESS may infer a possible gap in Theorem 6.8's proof. That is the main impact question a source-issue entry should answer.
- The project's own precedent, C19, states explicitly that the parent regime implies the needed condition and that the observation "is not a counterexample to the parent theorem".
- Correction. Add to C22:

  > Inside Theorem 6.8 this corner is harmless: with c₂ ≥ 32, the sample-size condition (using ε ≤ 1/(1−γ), S, C⋆ ≥ 1 and log(SAT/((1−γ)δ)) ≥ γ) gives γ < T/c₂ ≤ 2/c₂, so κ ≤ 8γ < 1/2. Moreover δ/(ST⁴) > 1/(8e), so the lemma's conclusion holds there with constant 8e < 84. This is not a counterexample to Theorem 6.8. The source error is confined to the standalone lemma's hypotheses and to the claim that κ < 1 follows from the choice of H alone.

  Reword "**Open:**" to make clear what remains open: the formal coverage of that corner, which is not formalized. The paper argument is not open.
- Why not BLOCKING: the texts hedge ("may still hold") rather than assert a gap.

**F2 — MINOR. C22's title understates and mislocates the failure region.**
- The title is "weighted propagation lemma fails for delta close to 1".
- Failure needs log(SAT/δ) small, which requires SAT ≤ 2. For SAT ≥ 3 the lemma holds for every δ ∈ (0,1).
- For SAT = 1, the left side is +∞ for some γ already at δ > e^{−3/4} ≈ 0.47 (Check 6), which is not "close to 1".
- Correction: retitle, for example "weighted propagation lemma fails when log(SAT/δ) is small (SAT ≤ 2)" or "…lacks a lower bound on log(SAT/δ)".

**F3 — MINOR. The scope-disclosure item asserts a manuscript error under a heading that says no errors are asserted.**
- The section header (SOURCE-ISSUES:391–392) says "These are limitations of the currently proved formalizations, not asserted errors in the manuscript."
- The Lemma 6.11 item (394–398) states "The printed lemma itself is false without some such premise".
- Correction: either amend the header ("…; where a limitation responds to a candidate source issue, the item links to it"), or reword the item to "The restriction responds to candidate source issue [C22](#C22) (the standalone printed lemma fails without such a premise)".

**F4 — NOTE. "Constant 84" is attributed to the statement rather than to the proof.**
- C22 says "The formal statement `Lemma6_11_restricted` proves the lemma with this premise and constant 84". The scope item says "made explicit (constant 84)".
- The indexed `Prop` is `∃ C : ℝ, 0 < C ∧ …` (Ch6.lean:199). The constant 84 is the witness in `Ch6Proofs.lean:102` and the literal constant in the library export `lcbq_useful` (LCBQUsefulSeries.lean:63).
- This is faithful, but imprecise. Suggest: "`Lemma6_11_restricted` (an existential universal constant) is proved with witness 84 from `lcbq_useful`".

**F5 — NOTE. The Ch6.lean docstring (193) ties falsity to κ ≥ 1 only.**
- It says "The source's assertion κ < 1 can fail, and then the printed lemma is false".
- Check 2 shows the printed lemma also fails with κ < 1, because no universal constant exists. Also, κ < 1 does hold under Theorem 6.8 with c₂ ≥ 32.
- Suggest: "κ < 1 does not follow from the choice of H alone; without a lower bound on log(SAT/δ) the standalone printed lemma is false (κ can exceed 1, and even for κ < 1 no universal constant works; candidate C22)."

**F6 — NOTE. The reasoning and the example in C22's sample-size paragraph.**
- "only bounds T from below, so it does not imply …" is a weak inference: a lower bound on T could, in principle, force SAT ≥ 3. The example is what carries the claim. Suggest: "does not imply log(SAT/δ) ≥ 1: for …".
- The example (γ = 0) is admissible (Check 3), but there κ = 0 and the lemma holds trivially. The example shows only that the *premise* is not implied. Pair it with the F1 sentence.

**F7 — NOTE. Locators and precision.**
- `eq:defn-kappa-proof-lcbq` has no line range in C22; it is 2284–2289.
- The H range "1667–1672" starts at the `subequations` label; the H equation itself is 1669–1672. This is acceptable.
- The η range (0 < η < 1/8) is implicit.
- "Below about 2.2·C" holds for δ = 0.9 (supremum 2.171·C).
- `2292–2300`, line 1767 and the Ch6 proof range `:4674–4785` are correct (the text ends at 4782 and blank lines follow to 4785).

**F8 — NOTE. The threshold could be sharpened (optional).**
- "Sufficient, not necessary" (LCBQUsefulSeries.lean:13; SOURCE-ISSUES scope item) is accurate.
- The γ-uniform threshold for κ < 1 is log(SAT/δ) ≥ 3/4. Any premise log(SAT/δ) ≥ L₀ > 3/4 gives the lemma, with constant 21/(1 − 3/(4L₀)) (Check 6). For L₀ = 1 this is 84.
- The texts need not adopt this.

**F9 — NOTE. Cosmetic.**
- `LCBQUsefulSeries.lean:16` is an overlong line that joins two sentences ("…not covered here. The argument follows the source: …"). Rewrap.

**C21 / Lemma 6.15 locator.**
- `offlineRL.tex:2835–2865` is exactly the lemma environment: `\begin{lemma}` at 2835, `\end{lemma}` at 2865. The proof subsection starts at 5680, and `eq:KL-single-action-bound-infinite-proof` is at 5740.
- The locator is consistent in SOURCE-ISSUES:759, Ch6.lean:167, LowerBoundFamilyKL.lean:9 and COVERAGE row 93.
- The replacement sentence reads: "Whether the cited inequality holds on the proof's actual parameter region is not established here; the formal proof does not use it."
  - It is accurate as a non-claim. The formal route via Lemma 2.13 clause 1 is as described.
  - Optional addition: a numeric grid suggests the inequality does hold on the proof's a=0 region (max ratio 0.91, Check 8), unproved.
- C21's other numbers and claims check out (Check 8).
- **NOTE:** C21 has no explicit `<a id="C21"></a>` anchor, unlike C19, C20 and C22. PROGRESS links it by heading slug, which resolves, but the style is inconsistent.

**Consistency of texts with the Lean statement.**
- The `Lemma6_11_restricted` body (Ch6.lean:198–210) matches every description:
  - ∃ C > 0;
  - all finite S, A and every `DiscountedMDP`;
  - 0<δ<1, T ≥ 1, the premise `1 ≤ log(card S·card A·T/δ)`, and W ≥ 0;
  - H = ⌈4/(1−γ)·L⌉₊ and κ = γ(1+1/H)³;
  - the actual time-j state laws and normalised discounted occupancy of `optimalGreedyPolicy`;
  - the Pi sup norm.
- The texts are mutually consistent on the premise, the "sufficient for κ<1" framing, the claim that the printed lemma is false without such a premise, the claim that the premise is not implied by Theorem 6.8, and the uncovered region. The one exception is the C22 title (F2).
- No reviewed sentence overclaims what is proved.

**Classification of C22 as a candidate source error.**
- This is justified.
  - The printed standalone lemma ("any 0<δ<1", no T condition) is false: Checks 1–2 give a left side of +∞, and no universal constant exists.
  - The inline claim at 2289 that κ < 1 follows immediately from H is false in general.
- Its impact on Theorem 6.8 is nil for c₂ ≥ 32 (F1). Like C19, it should say so.

## 5. Verdict

VERDICT: ACCURATE-WITH-FINDINGS — every mathematical claim in C22 and the rewritten disclosures checks out (counterexample, η-family with bound ≈2.171·C, sample-size example, equivalence, exact uncovered region, C21 locator), but C22 leaves open a Theorem 6.8 corner that the theorem's own sample-size condition closes for c₂ ≥ 32 (MAJOR omission), and the title and the section-header framing need minor fixes.

## 6. Comparison with the earlier critic report (`docs/critic-lemma6-11-restricted.md`, read after sections 2–5 were written)

**Points of agreement.** The earlier report's A2, A3 and A5 match my Checks 1, 2, 3 and 7 in substance:
- the S=A=T=1, δ=0.9, γ=0.3 counterexample;
- the 1/8−η family with right side ≤ 2.172·C;
- the γ=0 sample-size example;
- in the corner, 2 ≥ T ≥ c₂γ, so κ ≤ 16/c₂.

Its A4 (the threshold near 3/4) matches my Check 6.

**Its findings are addressed in the rewrite:**
- F1 (the false claim that the premise follows from Theorem 6.8): fixed. All texts now say the premise is not implied, and the counterexample is in C22.
- F2 (the premise presented as necessary): fixed. The texts now say "sufficient", and LCBQUsefulSeries adds "not necessary".
- F3 (no source error recorded): addressed by the new C22 and by "printed lemma itself is false". This introduces the header inconsistency in my F3.

**Remaining difference.**
- The earlier report noted (A5) that the sample-size condition "does rescue the conclusion", but bounded only κ (≤ 16/c₂). Its suggested fix wording ("a corner this entry does not cover") was adopted verbatim in spirit.
- The rewrite did not carry over the "rescues the conclusion" point and instead says "may still hold … needs its own argument" / "Open".
- My Check 7 completes A5 with an explicit constant (8e < 84, c₂ ≥ 32). This is the basis of my F1, which the earlier report did not raise because the C22 text did not yet exist.

**New relative to the earlier report:** F2 (the title), F3 (the header inconsistency) and the C21 locator check. The earlier report's N2 already judged the constant-84 attribution faithful; my F4 only refines the wording.
