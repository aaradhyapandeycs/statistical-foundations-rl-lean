# Critic report: corrected Theorem 7.11, milestone M5 (D′ B1–B5, F1–F3)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Critic: independent (not the builder). Date: 2026-11-09.
Brief: the private corrected-theorem plan §3 M5, as amended by `critic-thm7-11-corrected-plan-check.md` §3 and §7 (F1–F3).

## Verdict: ACCEPT

There are no required fixes. The optional items F1–F4 and the integration step I1 are listed below.

## Files reviewed (sha256 at review time)

| File | Lines | sha256 |
| --- | --- | --- |
| `Formalization/Analysis/MatrixContractionSup.lean` | 169 | `9a366d29fe8cee48817f45ce5398163c3fcea0f6cb82c92397ab7d6de0774633` |
| `Formalization/TDInference/Linearised.lean` | 197 | `8e2b48684d7a38089a1653cbd82d7d7b7aaa0dc1a8996bdeb16baea0bbc6aec4` |
| `Formalization/TDInference/Kernel.lean` | 611 | `2c54f3a87ff08b1a64a2bd1c7e5269eb3d331e861ef5b33df1a3aa5b70d4bb6e` |
| `Formalization/TDInference/LinearisationRemainder.lean` | 350 | `9541f157ba051df1fabbd23417f2f1060fd65b76242fa696a6c1bee90fef0ddb` |
| `Formalization/TDInference/LinearisedCovariance.lean` | 239 | `ba89ae8e7df3db84b18790d3915a58ad1206b09c0e6879906a4c15bd1f0248ed` |

`git status` shows no existing `Formalization/Ch7Rest`, `Analysis` or `Probability` file modified. The five files are new and untracked, and none of their 88 declaration names collides with an existing declaration in `Formalization/`.

## Compile and axiom evidence (my own run)

I did not rebuild the builder's oleans. Instead:
- I concatenated the five files, in dependency order with their inter-imports removed, into one scratch file, `reviewer-probes/CriticM5All.lean`. Its external imports are `TDInferencePolyakRuppert711`, `TDInferencePRRemainder711`, `TDInferenceZeroNoise711` and the Mathlib imports.
- I appended `#print axioms` for **every** theorem in the five files (71), the builder's probe (instances Z and G), and three critic sanity checks of the indexing.
- Command: `bash scripts/lean-local.sh reviewer-probes/CriticM5All.lean`. One Lean process; nothing else was running. Exit 0, 38.5 s wall time, no errors.
- All 71 theorems depend on exactly `[propext, Classical.choice, Quot.sound]`, as parsed from `reviewer-probes/critic.out`.
- `grep` finds no `sorry`, `admit` or `axiom` in the five files.

The sanity checks compile:
- `linIter … ω 1 = −(stepSize η₀ 1 • noiseVec (ω 0))`: the first tuple uses η₁ = η₀.
- `linWeight 1 0 = stepSize η₀ 1 • 1`.
- `linWeight T T = 0`: no spurious weights.

## 1. The definitions are the real objects

**Recursion.** I re-derived it from `tdStep` and `tdNoise` (ξ = V^π(s) − r − γV^π(s′)):

  V′(s) = V(s) − η[(V−V^π)(s) − γ(V−V^π)(s′) + ξ],

so Δ_{t+1} = Δ_t − η′_t(A_{ω t}Δ_t + ξ_t e_s) = (I − η′_tA)Δ_t − η′_tξ_t − η′_tζ_t. That is `tdError_succ`. It is proved from `tdIter`, not assumed.

**Indexing.**
- `linStep t` uses `stepSize η₀ (t+1)` with tuple `ω t`, exactly as `tdIter` does.
- `linIter` is defined by the genuine linearised recursion, with Δ^lin_0 = 0 and frozen for t ≥ T.
- `linPart = T^{-1/2} Σ_{t<T} linIter (t+1)` mirrors `scaledError_eq`.
- No definitional shortcut is involved: `linPart_eq_sum` (the independent-sum form) is *derived* through the variation-of-constants lemma `sum_linRec_eq`.

**Weights.** `linWeight T k = η′_k Σ_{t∈[k,T)} G_{k+1,t+1}`, with `matProd` latest-factor-first. I checked this against the backward recursion S_k = I + S_{k+1}B_{k+1}.
- `linWeight_last`: `linWeight T (T−1) = stepSize η₀ T • 1`. This is the paper's β_{T,T} = −η_T I.
- The sign convention β = −linWeight is harmless. Every use is quadratic (`linCov`) or goes through absolute values and norms. The decomposition B3 carries the sign explicitly, as `−Σ_k W_kζ_k`, and `linSummand` has the minus.

**Covariance.** `linCov` is defined as T⁻¹Σ_k W_k diag(Γ_true) W_kᵀ. F3 (`sum_pathWeight_linPart_mul_linPart`) proves that it is **exactly** E[linPart(s)·linPart(s′)] under `pathWeight`, for every T and η₀ with no hypotheses. The proof goes through:
- the generic independent-sum covariance `sum_pathWeight_mul_sum_mul_sum`, proved by `Fin.snoc` induction;
- the existing noise-covariance identity `sum_tupleProb_mul_noiseVec_mul`.

So `linCov` is the true covariance of the linear part, and Γ is the C43 `trueGamma`. `sum_pathWeight_linPart` (mean 0) is also proved.

**Decomposition B3.** `scaledError_sub_linPart_eq` is pathwise, for T ≥ 1 and every V₀. The transient (Σ_t G_{0,t+1})Δ_0 is deterministic.

## 2. Constants: T-free and k-free; the hypotheses are exact

All definitions are T-free and k-free:
- `tdBurnIn = ⌈(2/(μmin(1−γ)η₀))³⌉ + 1`;
- `linWeightConst = η₀t₁ + 3η₀/(a·η_{t₁+1})`, with a = μmin(1−γ);
- `linRemainderConst = K_β(D/η₀ + 2D + 2√(3Cη₀))`, where D = `tdPathBound` (depends on V₀) and C = `tdMomentConst` (depends on V₀, μmin, η₀);
- `linCovConst = ‖Γ_true‖_∞(K_β + 1/a)(3K_β² + 1/a²)/η₀`.

The dependence on the instance, η₀ and V₀ is acceptable per the plan.

**Hypotheses** of both main exports: `0 < η₀`, `η₀ ≤ 1`, `0 < μmin`, `∀ s, μmin ≤ μ.prob s`, `1 ≤ T`, with V₀ universally quantified.
- There is no Γ ≻ 0, no stationarity hypothesis, and no hidden μ assumption beyond the full-support lower bound.
- The printed range η₀ < 1/4 is inside η₀ ≤ 1.
- F3 and B3 need no hypotheses beyond T ≥ 1 (for B3).

## 3. Re-derivation of the inductions and orders

**B1** (`norm_linStep_mulVec_le`). Row s of (I − ηA)v is (1 − ημ_s)v_s + ημ_sγ·E_{P_π(s,·)}v. Both coefficients are ≥ 0 when η ≤ 1, so

  |·| ≤ (1 − ημ_s(1−γ))‖v‖ ≤ (1 − aη)‖v‖.

This uses no stationarity. The bound is for the *deterministic* mean A only (see the notes for M8).

**`mul_contrSum_le_of_ge`.** Write σ_k = 1 + (1 − ae_{k+1})σ_{k+1}, x = e_k and y = e_{k+1}, and assume yσ_{k+1} ≤ 3/a.
- The slow-variation condition x − y ≤ (a/2)xy, together with y ≤ x, gives x(1 − ay) ≤ y(1 − ay/2).
- The same condition with ax ≤ 1 gives x ≤ 3y/2.
- Hence xσ_k ≤ x + (1 − ay/2)(3/a) = 3/a + x − 3y/2 ≤ 3/a. ✓
- Before the burn-in, σ_k ≤ (t₁ − k) + σ_{t₁}, so e_kσ_k ≤ Et₁ + 3E/(ae_{t₁}). ✓
- The slow condition holds for k ≥ t₁ through `stepSize_sub_succ_le` (needs u_{k+2} ≥ 2/(aη₀); `tdBurnIn` ensures this). ✓

**`contrDrift_le`.** τ_k = (e_k − e_{k+1})σ_k + (1 − ae_{k+1})τ_{k+1}: split e_k − e_{t+1} and peel off p_{k+1,t+1} = (1 − ae_{k+1})p_{k+2,t+1}. ✓
- The hypothesis (e_k − e_{k+1})(k+2) ≤ e_k is equivalent to u_{k+1} ≤ u_{k+2}, since (k+1)e_k = η₀u_{k+1}. Equivalently, 1 − (1−r)^{2/3} ≤ r. ✓
- It gives (e_k − e_{k+1})σ_k ≤ K/(k+2), and the induction closes because K/(k+3) ≤ K/(k+2). ✓

**F2** (`tdA_mul_sum_linKernel`). A·Σ_{t∈[k,T)}η′_{t+1}G_{k+1,t+1} = I − G_{k+1,T+1}. I checked this by induction on T:
- G_{k+1,T+2} = (I − η′_{T+1}A)G_{k+1,T+1};
- everything commutes as polynomials in A, and the proof only uses A·(…) on the left;
- so A·η′_{T+1}G_{k+1,T+1} = G_{k+1,T+1} − G_{k+1,T+2}. ✓

This gives `linWeight − A⁻¹ = Σ_t(η′_k − η′_{t+1})G − A⁻¹G_{k+1,T+1}`, with A invertible by `tdA_isUnit` under full support.

**B4 order.** By martingale orthogonality (existing `sum_pathWeight_mul_sq_sum_eq`), E(Σ_k W_kζ_k)(s)² = Σ_k E[(W_kζ_k)(s)²].
- |W_k(s,u)| ≤ K_β (row bound from the operator norm), and E_x(Σ_u w_uζ_x(u))² ≤ K_β²E(2Δ(s_x)² + 2Δ(s′_x)²) by variance ≤ second moment.
- The k = 0 term is ≤ 4K_β²D², and the terms k ≥ 1 are ≤ 4K_β²Cη_k (M3's `tdSecondMoment_le`, non-stationary).
- Σ_{k<T} η_k ≤ 3η₀T^{1/3}.
- So ‖E_T(s)‖_{L²} ≤ T^{-1/2}[K_βD/η₀ + 2K_β(D + √(3Cη₀)T^{1/6})] ≤ K_E·T^{-1/3}. ✓

**B5 order.**
- Each term satisfies |(W_kΓW_kᵀ − A⁻¹ΓA⁻ᵀ)(s,s′)| ≤ ‖Γ‖(K_β + 1/a)·e_k, where e_k = τ_k + p_{k+1,T+1}/a is the row-sum bound of W_k − A⁻¹. The generic split lemma is correct; I checked that its cross terms cancel because diag Γ is symmetric.
- Σ_kτ_k ≤ Σ_k K_β²/((k+2)e_k) ≤ (K_β²u_T/η₀)Σ_k u_{k+1}^{-2} ≤ 3K_β²u_T²/η₀.
- Σ_kp_{k+1,T+1}/a ≤ 1/(a²e_{T−1}) = u_T²/(a²η₀), by telescoping.
- Dividing by T gives u_T²/T = T^{-1/3}. ✓

**Numerics (instance G, η₀ = 1/8).** I ran an exact deterministic recursion for Λ_T in 2×2 and in the eigenbasis (A symmetric, eigenvalues 1/4 and 1/2). The values of T^{1/3}·max|Λ_T − Λ| are:

| T | T^{1/3}·max\|Λ_T − Λ\| |
| --- | --- |
| 10⁵ | 1488 |
| 10⁶ | 806 |
| 10⁷ | 421 |

They decrease, so the T^{-1/3} order is consistent (the run is still pre-asymptotic, since t₁ ≈ 2.6·10⁵). All values are far below K_Λ ≈ 2.6·10¹⁵. The weight row sums reach about 960, which is below K_β ≈ 8.2·10⁴. This is consistent with F1: K_β ≍ 1/(a³η₀²) is large but T-free.

## 4. Non-vacuity

I re-checked instance G by hand. The data: next state = action, uniform π and μ, γ = 1/2, r(0,0) = 1 and every other reward 0.
- V^π = (3/4, 1/4): with m = (V₀+V₁)/2, V₁ = m/2 and m = 1/2.
- Γ_true(0) = ½·½[(−5/8)² + (5/8)²] = 25/128.
- Γ_true(1) = ½·½[(−1/8)² + (1/8)²] = 1/128.

So Γ ≻ 0 and the noise is non-zero, which makes `linPart` non-trivial. Both main exports instantiate on Z and on G, with μmin = 1/2 and η₀ = 1/8. Neither export has a Γ hypothesis, so the probe shows that the hypotheses are satisfiable and the objects are non-degenerate.

## Required fixes

None.

## Optional fixes and integration

- **F1 (documentation).** The CHECK §7 brief listed a generic B1 lemma (nonnegative diagonal, row sums ≤ 1 − c) for `MatrixContractionSup.lean`. B1 is instead proved TD-specifically in `TDInferenceKernel711.lean` (`norm_linStep_mulVec_le`). This is harmless, but the M5 completion note should state the deviation.
- **F2 (naming).** The plan's M5 table names `norm_linCov_sub_le` (a matrix norm). The export is the entrywise `abs_linCov_sub_le`, which matches the CHECK §7 signature. M8's variance step needs |uᵀ(Λ_T − Λ)u| ≤ ‖u‖₁²K_ΛT^{-1/3}. That is a two-line corollary; add it in M8, or as a small lemma in `LinCov711`.
- **F3 (constant honesty).** K_β ≍ 8/(a³η₀²) and K_Λ ≍ ‖Γ‖K_β³/η₀. They are T-free and adequate for the instance-wise reading (R-inst). They carry no information toward R-univ, so nobody should cite them as the printed coefficient.
- **F4.** `mumin_le_one` and the deduplication note on `prob_le_one` belong to the existing dedup backlog. They are not blocking.
- **I1 (integration, lead).** None of the five modules is imported from `Formalization.lean` yet. The lead must add them at landing so that `Audit.lean` and `scripts/check.py` cover them.
- **Ledger.** M5 is infrastructure only. It must not get a `Statements/` entry or change COVERAGE.

## Notes for M8: what it can rely on

- **Independent-sum structure.**
  - `linPart_eq_sum`: linPart ω = Σ_{k:Fin T} linSummand T k (ω k), where each summand is a function of tuple k only, with deterministic weights.
  - `linSummand_apply`: the explicit form −T^{-1/2}Σ_u W_k(s,u)ξ_x(u).
  - `sum_tupleProb_mul_linSummand`: each summand is centred.
  - `sum_pathWeight_mul_sum` and `sum_pathWeight_mul_sum_mul_sum`: generic mean and covariance of independent sums on `pathWeight`.
  - `sum_pathWeight_linPart_mul_linPart`: the exact covariance is linCov T.
- **Positivity.** `linWeight_last` gives linCov ⪰ T⁻¹η_T²diag(Γ_true). M8/M9 must add ∀ s, 0 < trueGamma themselves; M5 does not supply it.
- **Weight bounds.**
  - `norm_linWeight_mulVec_le` (‖W_k v‖_∞ ≤ K_β‖v‖_∞) and `abs_apply_le_of_norm_mulVec_le` (entrywise |W_k(s,u)| ≤ K_β).
  - For uᵀW_ke_s, go through ‖u‖₁K_β (CHECK F7).
  - Also available: `norm_linWeight_sub_inv_mulVec_le` and `sum_linWeightGap_le`.
- **Remainder.**
  - `scaledError_sub_linPart_eq` / `_apply`: E_T = T^{-1/2}[deterministic transient − Σ_k linMartTerm_k].
  - `abs_linTransient_le`: transient ≤ K_βD/η₀.
  - `weightedL2_scaledError_sub_linPart_le`: per coordinate. For uᵀE use the triangle inequality, ‖uᵀE‖₂ ≤ ‖u‖₁K_ET^{-1/3}.
  - `sum_pathWeight_mul_sq_linMart_le`.
- **Recursions.**
  - `tdError_succ`: the exact linearised one-step identity, aligned with `tdIter` (`ω t` drives V_t → V_{t+1} with `stepSize η₀ (t+1)`).
  - `linRec_eq` and `sum_linRec_eq`: generic variation of constants, reusable for the leave-one-out difference recursion.
- **Caveat for H3.** B1 (`norm_linStep_mulVec_le`) contracts only the *mean* step I − η′A. The leave-one-out zero-noise recursion with random A_k still needs the separate second-moment decay lemma (CHECK F6, `max_secondMoment_zeroNoise_le`). M5 does not provide it.
- **Index map.** Lean k ∈ [0, T) corresponds to paper sample k+1, and η′_k = η_{k+1}. `linCov` sums over `range T`, while `linPart` sums over `Fin T`; F3 reconciles the two once.

## Artifacts

- `reviewer-probes/CriticM5All.lean`: the concatenated scratch compile with the axiom audit and probe.
- `reviewer-probes/critic.out`: the Lean output, exit 0.
- The numerics scripts were scratchpad-only (pure Python); their results are quoted in §3.
