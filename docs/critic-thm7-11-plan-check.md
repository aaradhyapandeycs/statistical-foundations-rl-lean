# CHECK: Theorem 7.11 plan (`thm:Berry-Esseen-linear`)

Public copy of the independent critic report; local paths removed.

**Scope.** This is an independent plan check against the source only.
- No Lean or lake command was run, and nothing under `Formalization/` or `.lake` was touched.
- No paper was fetched, including wu2024statistical.
- I read AGENTS.md, SOURCE-ISSUES C43, `inference.tex:40–210` and `prelim.tex:405–421`, and wrote down my own reading
  (§1) before reading the plan's conclusions. I then read the plan in full and the Theorem 7.7 plan check (docs/critic-thm7-7-plan-check.md, for format).
- Every number in plan §2.2–2.5 was recomputed exactly. The script is
  a reviewer scratch script `z.py` (`python3 -I`, `fractions` plus a grid check of the Lyapunov step).
- Mathlib and project names were checked by grep against the local read-only Mathlib checkout and
  `Formalization/`.

**Files written.** This file, and the scratch script `z.py` (in a reviewer scratch folder, not published).

## 0. Pins

| File | SHA-256 |
| --- | --- |
| the builder's private plan (as reviewed) | `27706788f4cb1daa82b46d7d479fc097836bb83fcf9c95f4c9b3423d47b6dcbb` (verified) |

The source hashes are as quoted in plan §0. I did not re-hash them; the text I read matches the quoted line ranges.

## 1. My reading of the printed statement (written before reading the plan)

- **Sampling (:52–66).** The tuples are i.i.d.: s ∼ μ, a ∼ π(·|s), r = r(s,a) (deterministic), s′ ∼ P(·|s,a), and λ₀ = min μ > 0.
- **Update (:72).** Asynchronous. Only coordinate s_t changes. The average is V̄_T = (1/T)Σ_{t=1}^T V_t. V₀ is unspecified.
- **Mean operator.** E[e_s(r + γV(s′) − V(s))] = diag(μ)(r_π + γP_πV − V). Hence A = diag(μ)(I − γP_π) is the right
  drift matrix, with the right sign. Λ⋆ = A⁻¹ΓA⁻ᵀ is the standard Polyak–Ruppert sandwich, so the transpose convention
  is right.
- **Γ (:111–117).** The per-sample noise is ξ = e_s(V^π(s) − r(s,a) − γV^π(s′)). Its covariance is diagonal, with entries
  μ(s)E_{a,s′}[(V^π(s) − r(s,a) − γV^π(s′))²].
  - The printed formula uses an undefined `r(s)` and averages over s′ ∼ P_π(·|s) only.
  - With r(s) = r_π(s), the only notation defined in prelim (:414–419), the bracket is γ(P_πV^π(s) − V^π(s′)), so
    Γ_printed,ss = μ(s)γ²Var_{P_π(·|s)}V^π.
  - This omits the action-reward variance and the reward/next-value covariance.
  - I agree with C43 and plan §1.2.4: under the printed sampling, rewards depend on (s,a), so the theorem quantifies
    over such MDPs.
- **`≲` and C̃.** `≲` means a universal constant. C̃ is "problem-related, independent of T" and polynomial.
- **Convex distance.** The sup is over all convex sets of ℝ^S.
- **Γ ≻ 0.** ‖Γ⁻¹‖ and κ(Γ) need it; otherwise the RHS is +∞ and the statement is vacuous.

My reading agrees with plan §1.1–1.2. Specific verdicts follow in §2.

## 2. Statement reading (priority 1)

### 2.1 Quantifier order and C̃: FAITHFUL, and the weakening goes the right way

- **c first, C̃ per instance (incl. V₀) before ∀T.** This is the standard reading of "≲ … + C̃T^{−1/2}, C̃ independent of T".
- **Dropping "polynomial in salient parameters".** This only removes a constraint on the witness C̃:
  printed ⇒ weakened, so ¬weakened ⇒ ¬printed. **Confirmed.**
  - The same holds for the added hypothesis `∀ s, 0 < Γ_printed,ss`. It is a definedness condition, and the RHS is +∞
    without it.
  - It also holds for letting C̃ depend on V₀.
- **§1.3 equivalence (C̃ absorbs everything up to some T₀).** Correct as sketched. The constant changes from c to 2c,
  and d_cvx ≤ 1.
- **Robustness of R1 to the `≲` reading.** R1 works even if c may depend on the instance, because for a fixed instance
  the RHS → 0 as T → ∞. The plan's Props do not record this: both Props put c first. See required fix F3, which closes off any
  "the constant may depend on the problem" objection at essentially no cost.

### 2.2 Sampling, r(s), Γ_printed, Gaussian: FAITHFUL

- **Sampling.** The i.i.d. product weight ∏ μ(s)π(a|s)P(s′|s,a) is exact.
- **r(s) = r_π(s).** This is the only prelim-consistent reading. The alternative readings (π deterministic, or a
  state-only reward) are special cases, as the plan says. The reading is not a strawman: the printed setting
  explicitly has r_t = r(s_t,a_t) (:62).
- **`gaussCov A Γ` as the law of A⁻¹(√Γ ⊙ Z).** Its covariance is A⁻¹ diag(√Γ) I diag(√Γ) A⁻ᵀ = A⁻¹ΓA⁻ᵀ, using that Γ is
  diagonal. **Correct.** Sign and transpose conventions do not matter for a centred Gaussian, beyond the sandwich being
  A⁻¹·A⁻ᵀ, which it is.
- **`tdA`.** The draft `μ(s)(δ_{ss′} − γP_π(s,s′))` is diag(μ)(I − γP_π) row-wise. **Correct.**
- **Junk trap (not in the plan).** `Measure.map f ν` is the **zero measure** when f is not AEMeasurable. R1 only needs
  Q({0}) = 0, so R1 would also "succeed" against a junk zero measure. M1 must therefore export
  `IsProbabilityMeasure (gaussCov A Γ)`; see F2. It is listed in §4 M1 among the "basic lemmas", but not among the
  §8 targets.

### 2.3 Convex sets and measurability: FAITHFUL, but make the refuted Prop weaker

- The Prop quantifies over **all** convex C and uses `.real` (outer measure) on non-measurable ones.
- For a *refutation*, quantifying over more sets makes the refuted Prop **stronger**, so ¬Prop is **weaker**.
- R1 and R2 only use closed sets ({0} and a closed slab). So the refuted Prop should restrict to
  `Convex ℝ C → IsClosed C` (or `MeasurableSet C`). Then the refutation holds for every reasonable set class and
  needs no argument about outer measures. See F4.
- For the positive (corrected or restricted) entries, the plan's §6.6 treatment is fine.

### 2.4 Step size: one precision gap

- The step at iteration t ≥ 1 must use η_t = η₀t^{−2/3}.
- §4 M1 says "step t+1 using `ω ⟨t, _⟩`" but does not say which step size is used.
- In Lean, `(0:ℝ) ^ (-(2/3):ℝ) = 0`. If the builder writes `stepSize η₀ t` at the recursion index t, then the first update
  has η = 0 and every later step size is shifted by one. That would be a silent off-by-one.
- See F1.

### 2.5 V₀ readings

- (∀) ⇒ (0) ⇒ (∃) is correct.
- R1 needs (∀). R2 covers every fixed V₀, including 0 and V^π, so it refutes (∃). **Confirmed** (§3.3).

## 3. Refutations re-derived (priority 2)

### 3.1 Instance Z: all numbers CONFIRMED exactly

Instance Z: S = A = 2, γ = ½, μ and π uniform, s′ = a deterministically, and r = (½, ¾; 0, ¼).

- **V^π = (1, ½).** Directly: r_π = (5/8, 1/8), P_π has uniform rows, and V = r_π + ¼(V₁ + V₂) gives (1, ½).
- **The TD error is 0 for all four (s,a).** For example, V(1) − r(1,2) − ½V(2) = 1 − ¾ − ¼ = 0. So **ξ ≡ 0 on the whole support**, and Γ_true = 0.
- **Γ_printed = diag(1/128, 1/128).** The bracket is ±1/8 for both s, so the entry is ½·(1/64).
- **A and A⁻¹.** A = [[3/8, −1/8], [−1/8, 3/8]], with det A = 1/8 and A⁻¹ = [[3,1],[1,3]].
- **Λ_printed.** Λ_printed = (1/128)[[10,6],[6,10]] = [[5/64, 3/64], [3/64, 5/64]], which is nondegenerate.
- **The printed coefficient.** λ₀ = ½, Tr Γ·‖Γ⁻¹‖ = 2, κ = 1 and S = 2, so K = 4√η₀ + 4√2/η₀. This is finite for every
  η₀ ∈ (0, ¼).
- **Iterates.** With V₀ = V^π, every positive-weight sample satisfies r + γV^π(s′) = V^π(s), so the update fixes V^π.
  Hence √TΔ̄_T = 0 surely, P({0}) = 1, and Q({0}) = 0:
  - the preimage under the injective linear map is {0} = Set.pi univ {0};
  - `Measure.pi_pi` gives a product of `gaussianReal 0 1 {0} = 0`, by `noAtoms_gaussianReal`.
- **Gap and RHS.** The gap is 1 at every T. The RHS is cK·T^{−1/3} + C̃T^{−1/2} → 0, with every quantity finite.
  **R1 is a valid refutation.**
- **Instance Zδ.** V = (101/100, 51/100). The TD errors are ±1/200, so Γ_true = diag(1/80000, 1/80000). Γ_printed is still
  1/128, because V₁ − V₂ = ½ is unchanged. **Confirmed.**

**Legitimacy of the degenerate instance.** All printed hypotheses hold: μ > 0, η₀ ∈ (0, ¼), rewards in [0,1], γ < 1,
and even the added Γ_printed ≻ 0. The theorem as printed is about these Γ objects, and the instance satisfies them. It is
not a strawman.

### 3.2 R2 Lyapunov step: CONFIRMED (and slack)

For Φ = Σ_s Δ(s)²:
- By convexity, ((1−η)x + η(γy))² ≤ (1−η)x² + ηγ²y² for 0 ≤ η ≤ 1.
- In instance Z, s′ = a is uniform and independent of s.
- Hence E[Φ_t | past] ≤ Φ(1 − η/2 + ηγ²/2) = (1 − 3η/8)Φ.

The exact one-step map is computed in the script: E Φ_t ≤ Φ(1 − η/2 + η²/8), so the worst ratio (EΦ/Φ − 1)/η is
−15/32 ≤ −3/8 on η ∈ (0, ¼].

### 3.3 R2 averaging: CONFIRMED, √TΔ̄_T → 0 in L¹ at rate T^{−1/2}

- Σ_{i≤t} i^{−2/3} ≥ ∫₁^{t+1} x^{−2/3} dx = 3((t+1)^{1/3} − 1).
- Hence E‖Δ_t‖ ≤ √Φ₀ exp(−(9η₀/16)((t+1)^{1/3} − 1)).
- This decay is stretched-exponential, so Σ_t E‖Δ_t‖ ≤ √Φ₀K₁(η₀) < ∞. The bound e^{−x} ≤ 720/x⁶ makes it explicit.
- Therefore E‖√TΔ̄_T‖ = T^{−1/2}E‖Σ_t Δ_t‖ ≤ √Φ₀K₁/√T → 0. The averaged error really is O(T^{−1}), not O(T^{−1/2}):
  the errors are summable because there is no additive noise.
- For Φ₀ = 0 the bound is 0. So R2 covers V₀ = V^π too, and every fixed V₀.

### 3.4 R2 Gaussian slab: CONSTANT WRONG (harmless, but fix it)

- L = A⁻¹diag(√Γ) has L₁₁ = 3/√128 ≈ 0.26517.
- Route (b) gives a Gaussian slab mass ≤ 2ε/(L₁₁√(2π)) ≈ **3.009ε**, not "< 2.4ε".
- Route (a), with exact variance 5/64, gives ≤ 2.855ε. The plan's 2.4 matches neither route.
- Corrected value at ε = 1/10 and E‖X_T‖ ≤ 1/100: d ≥ 1 − 0.1 − 0.301 = **0.599**, not 0.66.
- Any positive constant suffices. Suggest ε = 1/20 with E‖X_T‖ ≤ 1/1000, giving d ≥ 1 − 0.02 − 0.151 > 0.82, or simply
  `d ≥ 1/2`. See F5.

### 3.5 R3: CONFIRMED numerically

- u = Aᵀe₁ projects the printed Gaussian to N(0, Γ_printed,11) = N(0, 1/128).
- At a = 0.014, the bound 1 − (1/80000)/a² − 2a/√(2π/128) = 0.8098.
- The claim limsup E(uᵀX_T)² ≤ Γ_true,11 is the M3 PR-decomposition statement (leading term −T^{−1/2}Σξ_t). It is
  plausible, but it is M3 work, not checked here.

### 3.6 Which refutations are deliverables

- **M1: R1**, `not_thm7_11_printed`. It is cheap and exact at every T.
- **M2: R2**, `not_thm7_11_printed_someInit`. It subsumes R1 via `thm7_11_printed_imp_someInit`.
- **R3 stays optional (M3).** It is the only witness that patching Γ ≻ 0 without replacing Γ fails, which is useful
  evidence for C43's "replace Γ". It is not needed to refute the printed theorem.
- The exact refutation Props should be §5.1, amended by F3 and F4.

## 4. Corrected statement and open risk §6.4 (priority 3)

### 4.1 Γ_true and Γ_true ≻ 0

- **Formula.** `trueGamma` is exactly Cov ξ: diagonal, μ(s)E_{a,s′}[(V^π(s) − r(s,a) − γV^π(s′))²]. **Correct.**
- **Γ_true ≻ 0.** The plan calls this "needed" or "necessary". In the source's own terms it is a **definedness**
  condition: ‖Γ⁻¹‖ = ∞ when Γ is singular, so the printed RHS is +∞ and the singular case is vacuous.
  - Stating it as a hypothesis is therefore not a substantive weakening.
  - The C43 append should say "definedness (‖Γ⁻¹‖ = ∞ otherwise), required in Lean because of the junk value 0", rather
    than present it as a mathematical necessity. See O1.
  - The plan's observation is correct: with Lean's x/0 = 0 the junk RHS → 0, and in instance Z with V₀ ≠ V^π the law is
    not δ₀.

### 4.2 Is the corrected theorem plausibly true with the printed coefficient form?

**The §6.4 worry about Zδ with δ → 0 is resolved negatively by homogeneity.** In Zδ, every TD error is linear in δ
(ξ = δ·ξ̂), and Δ_t = (I − η_tA_t)Δ_{t−1} − η_tξ_t is linear in (Δ₀, ξ).
- From V₀ = V^π, the law of √TΔ̄_T/δ is independent of δ, and Λ_true ∝ δ².
- d_cvx is invariant under invertible linear maps, and K(Γ) is scale-invariant in Γ. So d_cvx(T) and K are both
  **independent of δ**, and no ‖V^π‖/√min Γ factor can arise.
- More generally, V^π enters the error dynamics only through ξ.
- After the V₀-transient, which decays like exp(−cη₀T^{1/3}) and goes into C̃, the stationary Δ_t is of size
  √η_t·(noise scale). The multiplicative term (A_t − A)Δ_{t−1} therefore scales with √Γ, and whitening cancels the scale.
- Higher-moment or kurtosis quantities, such as E‖Γ^{−1/2}ξ‖³, arise only in terms of order T^{−1/2} or faster, which
  §1.3 lets C̃ absorb.

**Remaining genuine risks for "universal c × K"** (these are proof-technique risks, not counterexamples):
- **(a) Coefficient bookkeeping.** Plan §4 M3(e) claims its L² estimate "matches the printed √(Sκ)/((1−γ)λ₀η₀) after
  whitening". As written, it does not:
  - the bound `S·Σc_k²·Tr Γ/((1−γ)λ₀)²`, whitened by ‖Γ⁻¹‖, gives √(S·TrΓ‖Γ⁻¹‖) ≥ S, which can be √S·√(Sκ);
  - the ∞-norm contraction converted to 2-norm (‖G‖₂ ≤ √S‖G‖_∞) also loses √S;
  - the √(Sκ) form does arise naturally: for the whitened term M = Γ^{−1/2}AB, E‖Mξ‖² = ‖MΓ^{1/2}‖_F² ≤ S·κ·‖AB‖₂².
    But this works only if the propagators B are controlled in 2-norm without a √S loss. That is not automatic: tabular
    TD contracts in ∞-norm, and I − ηA is not a 2-norm contraction for general μ.
- **(b) Convex anti-concentration.** The Gaussian surface area of convex sets can be of order S^{1/4} (Nazarov), while the
  first printed term has slack (TrΓ‖Γ⁻¹‖ ≥ S) but the second term does not obviously have any.
- **(c) Rate.** An L²-only remainder loses rate (T^{−2/9}). Moment or tail routes give log T. Getting T^{−1/3} with no log
  needs a leave-one-out (Shao–Zhang/Chen–Shao) argument.

**Assessment.**
- I found no counterexample to the corrected form, and the homogeneity argument removes the one specific threat
  raised in §6.4. I rate `Thm7_11_corrected` as plausibly true.
- But a proof matching the printed coefficient exactly (universal c, no log, √(Sκ) rather than S√κ) is unestablished.
- **Recommendation.** Keep `Thm7_11_corrected` (§5.2) as the **target** name, but commission only `_restricted` entries
  until M6 actually delivers the printed coefficient. Any variant with an extra √S, an S^{1/4}, or a log T must be
  `_restricted`, with the exact coefficient stated.

### 4.3 The restricted drafts: honest and non-vacuous

- **`_restricted_smooth`.** This is a genuinely different metric (C³ test functions with global L₁, L₃ bounds). It is
  non-vacuous: f = sin(⟨u,·⟩) satisfies the hypotheses. The docstring must say it does **not** imply any convex-set
  claim; it does.
  - Two notes: the ∫ against `gaussCov` needs an integrability lemma (Lipschitz f), or the junk value 0 makes the
    statement about a different quantity; and `tdRemainderConst` must be fixed and displayed before the entry is
    added. The `∃ K` fallback is honest only if the docstring says "K problem-dependent".
- **`_restricted_halfspace`.** C̃ is uniform over (u, b) and the rate T^{−2/9} is explicit, so this is a real CLT-type
  statement for projections. u = 0 gives a gap of 0. It is honest and non-vacuous.
- Both depend on M3's correctness, and both are fine as `_restricted` entries pointing to C43.

## 5. Inventory spot-check (priority 4)

| Claim | Result |
| --- | --- |
| `gaussianReal` (Real.lean:200), `noAtoms_gaussianReal` (:213, needs v ≠ 0) | **present** |
| `class IsGaussian` (Basic.lean:45), `isGaussian_map` (:128, CLM), `IsGaussian.charFun_eq` (:186), `isGaussian_iff_charFun_eq` (:193) | **present** |
| "the product instance (:241)" | **present but binary `μ.prod ν`**, not `Measure.pi`. There is no `IsGaussian (Measure.pi …)` instance (grep). M2 needs an induction over `Fin n` or a charFun argument. |
| `Measure.ext_of_charFun` (CharacteristicFunction.lean:237), `charFun_pi` (:293) | **present**. `charFun_pi` is stated on `PiLp 2 E`, so M2 must work on `EuclideanSpace`/`WithLp`, as the plan anticipates. |
| `Measure.pi_pi` (Constructions/Pi.lean:291) | **present** |
| gaussianPDF ≤ 1/√(2π v) | **absent** (no `gaussianPDFReal_le…` lemma). The R2 slab bound must prove it (easy from `exp ≤ 1`). |
| no CLT, Lindeberg, Berry–Esseen or Esseen | **confirmed absent** (case-insensitive grep over all of Mathlib: no hits) |
| no `stdGaussian`/`multivariateGaussian` | **confirmed absent** |
| Project: `TemporalDifference.policyReward` (TDIterateBounds.lean:11), `valueFixedPoint` (+`_spec`), `policyTransition` (= (π s).bind (M.transition s)) | **present**. Another `policyReward` exists in `StatisticalRL.ModelBasedPolicyEvaluation` (Generative/PolicyEvaluationInverse.lean:18). The brief should name the namespace. |
| Point-mass and uniform helpers for instance Z | `MDP/PointMassDefinitions.lean` (`pointMass`) and `OfflineRL/VILCBDatasetDefinitions.lean` (`uniformRow`) exist. Point the builder at them. |

## 6. M1 brief (priority 5)

- **Scope.** The scope (three files, R1 only, R2 and charFun out) is correct.
- **Props.** They are self-contained: every binder is explicit, the hypotheses μ > 0, 0 < η₀ < ¼ and Γ_printed ≻ 0
  are written out, and the RHS is a closed formula once `printedRate` is a displayed def.
- **Binders.** `[DecidableEq State]` is needed for `Function.update` and for `Matrix.inv`. The binders in `Type`
  (rather than `Type u`) are fine for a refutation, since the witness lives in `Type`.
- **Gaps.** The brief has the gaps F1–F4 below.

## 7. Verdicts

- **M1: GO WITH FIXES** (F1–F4. F5 is M2-scoped and may be done now in the plan text).
- **Overall staging: GO.**
  - M1 → M2 (refutations, with no CLT) → M3 (L² theory, R3, covariance limit) → M4/M5 restricted entries is sound,
    and each stage has standalone library value.
  - M6 must stay labelled research-scale. COVERAGE must keep 7.11 as "printed refuted; corrected open" until M6, and
    must not count any `_restricted` as the corrected theorem.

## 8. Required fixes

- **F1. Step-size index.** Specify that the recursion step producing V_{t+1} uses `stepSize η₀ (t+1)` and sample
  `ω ⟨t, _⟩`, and add the docstring line "η_t = η₀t^{−2/3} for t ≥ 1".
  - Justification: Lean's `0 ^ (−2/3) = 0` would make an off-by-one silent (§2.4).
- **F2. Non-junk Gaussian.** Add these to the §8 M1 targets:
  - `measurable`/`continuous` for the map `z ↦ A⁻¹ *ᵥ (√Γ ⊙ z)`;
  - `IsProbabilityMeasure (gaussCov A Γ)`;
  - and require `gaussCov_singleton_zero` to go through `Measure.map_apply` with that measurability.
  - Justification: `Measure.map` of a non-AEMeasurable map is 0, and R1 would also "refute" against that junk measure
    (§2.2). Also add `lawProb_univ = 1`, already listed in §4, to the §8 target list.
- **F3. Instance-level core lemma, robust to the `≲` reading.** Export
  `zeroNoise_violates : ∀ c Ct : ℝ, ∃ T : ℕ, 1 ≤ T ∧ |lawProb Z … V^π T {0} − (gaussCov …).real {0}| > c * K * T^(−1/3) + Ct * T^(−1/2)`.
  - Then derive `¬Thm7_11_printed` from it, and also `¬Thm7_11_printed_instWise`, in which `∃ c, ∃ Ct` come
    **after** the instance binders.
  - Justification: this shows the refutation does not depend on c being universal, at essentially zero cost (§2.1).
- **F4. Restrict the refuted Props' set class to closed convex sets** (add `IsClosed C →`, or `MeasurableSet C →`).
  - Justification: this weakens the refuted Prop, so the refutation becomes stronger and free of any outer-measure
    question. The docstring records that the printed class is all convex sets, and that refuting the closed subclass
    refutes it (§2.3).
- **F5. Correct the R2 slab constant.** Route (b) gives 2ε/(L₁₁√(2π)) ≈ 3.01ε, and the bound at ε = 1/10, E‖X‖ ≤ 1/100 is
  0.599, not 0.66. Choose ε = 1/20 with E‖X‖ ≤ 1/1000 (giving > 0.82), or target `d ≥ 1/2` (§3.4).
- **F6. Correct plan §4 M3(e)'s "matches √(Sκ)" claim.** As derived, it gives √(S·TrΓ‖Γ⁻¹‖), which can be √S·√(Sκ), plus
  a possible further √S from the ∞→2 norm conversion. Record this as a §6.4 coefficient risk, not as a match (§4.2(a)).

## 9. Optional suggestions

- **O1.** Phrase Γ_true ≻ 0 in C43 and in the docstrings as definedness of ‖Γ⁻¹‖ and κ (with the Lean junk-value reason),
  not as a mathematical necessity (§4.1).
- **O2.** Add the homogeneity argument of §4.2 to plan §6.4 as the answer to the Zδ worry. It also suggests an M3 sanity
  lemma: with V₀ = V^π, the law of scaledError is linear in a common scaling of the rewards' TD errors.
- **O3.** Name the namespace `StatisticalRL.TemporalDifference.policyReward` in the brief, and point to `pointMass` and
  `uniformRow` for instance Z.
- **O4.** In M2, plan for the missing `IsGaussian (Measure.pi …)` instance and the missing Gaussian pdf sup bound
  (§5).
- **O5.** R2 in fact gives liminf d_cvx = 1, using shrinking slabs. A cleaner statement is `∀ ε > 0, eventually d ≥ 1 − ε`,
  but any positive constant suffices for the refutation.

SHA-256 of this file: reported by the caller-facing hand-off message (computed after writing).
