# CHECK: the builder's private plan (corrected Theorem 7.9, FedSynQ) — independent source-level critic

Public copy of the independent critic report; local paths removed.

Status: independent paper-proof check. No Lean was compiled. Nothing is certified, and there is no author approval.
Inputs (sha256):
- `source/upstream/tex/chapters/federated_RL.tex` `c9df1d9f6187d79644d6c55ae9be97cb68e5578fa2b963b490a3d94ef45b0320` (matches the plan)
- the builder's private plan `117d155250d749121aa9fc1866a9d0f9c5d8dd938966f3156234a8789d7f06ea`
- `<builder plan folder>/check_thm7_9_plan.py` `dcfa0d0855f91d54f73885fe49569e41bf0c3e41e90456e8e3e10e92acf693f1`
- my script: `<reviewer check folder>/critic_thm7_9.py` `91bc1db8b08321f0a73eb779ade4beb570558b3fa14aa8796d250662d2d00e2d`
- its output: `<reviewer check folder>/run.log` `e90f5bdf2a58763169fcca56ee6c7b6b6cc07d92a9c0ba746dd81f55123d37fd`

Run with `python3 -I critic_thm7_9.py` (about 30 s). All checks passed.

The plan cites woo2023blessing but did not consult it, and neither did I. Its proof is self-contained, and I re-derived each step below.

## 0. Printed statement, reconstructed before reading the plan

Setting: a discounted MDP with finite S and A, rewards in [0,1] and γ ∈ [0,1). K agents each have a generative model, and every draw s_t^k(s,a) ~ P(·|s,a) is independent (:23–26).

FedSynQ runs from Q_0^k = Q₀ with constant η. The source requires 0<η<1, but only as an algorithm input range (:51, :76). Each step applies the local update (:47–49). The agents average Q_{t−1/2} whenever t ≡ 0 (mod τ), with τ ≥ 1 (:59–64). The output is Q_T = (1/K)Σ_k Q_T^k (:68), and τ ∣ T is assumed "WLOG" (:70).

Theorem (:99–117). Fix δ ∈ (0,1), ε ∈ (0, 1/(1−γ)] and 0 ≤ Q₀ ≤ 1/(1−γ). Assume τ ≤ 1 + η⁻¹ min{(1−γ)/(8γ), 1/K}. Then for some sufficiently large c_T and sufficiently small c_η the following holds: if T ≥ c_T/(K(1−γ)⁵ε²)·log³(SAKT/(δε(1−γ)²)) and η = c_η K(1−γ)⁴ε²/log(SAKT/δ), then w.p. ≥ 1−δ, ‖Q_T − Q⋆‖_∞ ≤ ε.

The plan's §1.1 matches this reconstruction. Two points are implicit in the source: γ > 0 (the τ condition divides by γ), and K, τ, T ≥ 1.

## 1. Diagnosis and the weakest correction — verdict: CONFIRMED (with notes)

- **η > 1 is the only error. CONFIRMED.** The C41 witness (S=A=1, r≡1, K large, so Q_1 = η) is correct. Apart from η, every printed premise is used and suffices, and the proof in §2 below closes once η ≤ 1 holds.
  - I found no other false component.
  - The ε range is not needed (x ≤ 1 only gives log(1/x) ≥ 0). Keeping it is harmless.
  - K ≥ 1 and τ ≥ 1 are needed and are source conventions:
    - K = 0 gives Lean `Fin 0` and 1/0.
    - τ = 0 never synchronizes in Lean's `t % 0`.
  - τ ∣ T and T ≥ 1 are unused (the T premise forces T > 0). Keeping them as printed is faithful.
  - γ > 0 is a definedness convention, not a correction. It is acceptable as kept.
    - Optional: under the "(1−γ)/(8γ) = +∞" reading, γ = 0 makes the run deterministic, (1−η)Q + ηr, and the theorem holds there too. The disclosure should call γ > 0 a definedness convention, not a correction.
- **Added hypothesis `c_η K(1−γ)⁴ε² < log(SAKT/δ)` (i.e. η < 1). CONFIRMED sufficient.**
  - Minimality is correctly *not* claimed. My check W shows that a deterministic one-state run with η = 1.5 still converges.
  - The rationale for η ≤ 1 (iterates stay in [0,H]) is right. The export may use η ≤ 1, which implies the entry's η < 1.
  - η > 0 is automatic, since SAKT ≥ 1 > δ.
- **True law and true Q⋆. CONFIRMED faithful, and the corrected entry is STRONGER than `Thm7_9_at` + (η<1).**
  - `Thm7_9_at` asks only for ∃(Ω, μ, samples, Q⋆ with `IsOptimalQ`). The corrected entry fixes Ω = `FedSamples`, μ = `fedSamplingLaw M T K 1` (a product of `rowMeasure`s, so a probability measure), the adapter `fedSamplesExtend … 0`, and Q⋆ = `M.optimalityFixedPoint`.
  - The bridge to `IsOptimalQ` exists: `optimalityFixedPoint_bellman` in `InnerConstant710.lean:59`, with `vStar = greedyValue`. So the corrected entry implies the existential form, and the converse is false in general.
  - Indexing checks out:
    - `fedRun (t+1)` uses `samples (t+1)`.
    - `fedSamplesExtend` maps iteration t ∈ [1,T] to coordinate t−1.
    - The synchronization test `t % τ = 0` uses the 1-based t, as at :59–64.
    - `FedIndex` is lexicographic (time, agent), then (s,a), then batch. This is the time-first order needed for causality.
  - Measurability: `fedSamplingLaw` uses the local `⊤` instance on `State`. `FedSamples` is a finite type with the product σ-algebra, which has measurable singletons, so every event is measurable. `.real` is therefore the honest probability, not an outer-measure bound.
- **Constants quantified first (universal). CONFIRMED.** This order is stronger than the printed order and agrees with `Thm7_9_at`.

## 2. Proof — verdict per step

| Step | Claim | Verdict |
|---|---|---|
| 0 | With η ∈ [0,1] and Q₀ ∈ [0,H], all Q_t^k, Q_{t−1/2}^k and Q̄_t stay in [0,H] (r ∈ [0,1] is a field of `DiscountedMDP`); Q⋆ ∈ [0,H] | correct |
| 1 | Q̄_t = mean of Q_{t−1/2}^k at every t (needs K ≥ 1); Δ recursion with ξ_t; D recursion with ζ_t^k; D_t^k = 0 when τ∣t; N, M and noise-free Y, E as stated | correct (re-derived; numerically Δ = Y+γN and D = E+γM in the plan's A, and the closed-form window sums in my P) |
| 2 | ‖P(V^k−V⋆)‖ ≤ ‖Δ‖+‖D^k‖; ‖PV^k − avg PV^j‖ ≤ 2d | correct |
| 3 | e_u ≤ (1−η+2ηγ)e_{u−1} + 2ηγ²m ≤ (1+ηγ)e_{u−1}+2ηγ²m (uses 1−η ≥ 0 and γ ≤ 1); e ≤ 2ηγ²m·j(1+ηγ)^{j−1} ≤ 2γm(ηγj)e^{ηγj}; the first half of (106) gives ηγ(τ−1) ≤ (1−γ)/8, so e ≤ γ(1−γ)e^{1/8}m/4 ≈ 0.283γ(1−γ)m and d ≤ γm(1+0.29(1−γ)) ≤ m | correct. The plan writes j(1+ηγ)^j, which is looser but valid. Numerically: drift violation ≤ 2.3e-13 (float) on adversarial paths |
| 4 | ‖Y_t‖ ≤ (1−ηg)‖Y_{t−1}‖ + ηγ(1+γ)σ ≤ (1−ηg)‖Y_{t−1}‖ + 2ηγσ, so (★) ‖Q̄_T−Q⋆‖ ≤ (1−ηg)^T H + 2γσ/g + γσ ≤ (1−ηg)^T H + 3σ/g | correct. It needs ‖N_u‖ ≤ σ for u ≤ T and ‖M_u^k‖ ≤ σ for u ≤ T−1. (★) holds pathwise on ADVERSARIAL paths, with next states chosen as argmax, argmin or mixed (check P, 400 runs, with τ at its maximum, γ near 0 and 1, and η up to 1) |
| 5 | Time-first lexicographic filtration. V_{u−1}^j depends only on times < u, through averaging across all agents, so increments are centered and their bounds are deterministic. For N: ΣB² = (η²H²/K)Σ(1−η)^{2i} ≤ ηH²/K (uses η ≤ 1). For M: ΣB² ≤ η²(τ−1)(1−1/K)H² ≤ ηH²/K (second half of (106); M ≡ 0 if τ = 1). The Azuma bound P(\|S\| > √(2ΣB² log(2/δ'))) < δ' matches `azuma_filtration_strict` (hypotheses: \|X_i\| ≤ B_i, μ[X_i\|ℱ_i] = 0, X_i ℱ_{i+1}-measurable). Union bound over SAT(K+1) ≤ 2SAKT events with δ' = δ/(2SAKT) gives L = log(4SAKT/δ) and σ = H√(2ηL/K) | correct. The linear speedup comes from the K independent per-agent increments of size 1/K. Check V confirms ΣB²/(η/K) ≤ 0.9999 (N) and 0.9873 (M). Check Z confirms the per-event tail frequency ≤ δ'. The plan's remark that Freedman is unsuitable for M is right: its range term ηHL is not ≤ σ uniformly in K |
| 6 general | SAKT ≥ 2 ⇒ ℓ > log 2 ⇒ L ≤ 3ℓ; 3σ/g ≤ ε/2 ⟺ ηL ≤ Kg⁴ε²/72 ⇐ 3c_η ≤ 1/72. Tηg ≥ c_T c_η ℓ_T³/ℓ (exact identity g⁵ε²/(g³x²) = 1) ≥ c_T c_η ℓ_T² ≥ c_T c_η log2·ℓ_T ≥ ℓ_T ≥ log(2/x), so (1−ηg)^T H ≤ ε/2 | correct. Check R: 127,071 admissible draws, including T up to 1000× the minimum, K up to 10⁹, δ → 0 and δ → 1, γ → 0 and γ → 1. The worst relative slack is −0.70; the plan's sampling found a tighter −0.10 |
| 6 degenerate | S=A=K=T=1 has no noise; \|Q_1−Q⋆\| = (1−ηg)\|Q₀−Q⋆\|. From the T condition, ℓ_T ≤ c_T^{−1/3} ≈ 0.0464 and g, x ≥ e^{−ℓ_T}, so ηg ≥ c_η e^{−5ℓ_T}/ℓ_T ≥ ℓ_T ≥ 1−x, since 0.00463·e^{−0.232} = 0.00367 ≥ c_T^{−2/3} = 0.00215 | correct. Check D, a grid of 175,107 admissible points: worst err−ε = −0.10. S = 1 with AKT ≥ 2 is covered by the general case (noise is 0) |
| constants | c_η = 1/216, c_T = 10⁴ satisfy (K1) with equality, (K2) 32.1 ≥ 1, and (K3) 2.149 ≥ 1.261 | correct |

## 3. Max-norm, union bound, log term — verdict: CORRECT

- The ‖·‖_∞ error over all (s,a) follows deterministically from (★) on the event that every N_t(s,a) and every M_t^k(s,a) is bounded. That event is a union over (t,s,a) and (k,t,s,a): SAT(K+1) ≤ 2SAKT scalar Azuma events.
- The resulting log is log(4SAKT/δ) ≤ 3 log(SAKT/δ) once SAKT ≥ 2. The degenerate SAKT = 1 case, where log(1/δ) can be tiny, is correctly split off and handled noise-free.
- The printed log³ in the T condition is slack: the proof uses ℓ_T³/ℓ ≥ ℓ_T².

## 4. Required corrections

None of these block the plan.
1. In the §2.3 docstring, list explicitly what the entry fixes or strengthens beyond the added hypothesis:
   - the true law and the true Q⋆ (stronger than the old existential Prop);
   - universal constants first;
   - γ > 0 as a definedness convention for (106).

   The current text already says most of this. Its phrase "differs … only by the added hypothesis" should read "differs in hypotheses only by …".
2. §3.4: e ≤ 2ηγ²m·j(1+ηγ)^{j−1} is the exact unrolling. The plan's j(1+ηγ)^j is fine, but the builder should use one form consistently.
3. §3.5 and §3.6: state the index ranges used. The N bound is needed for u ≤ T; the M bound for u ≤ T−1, on non-synchronized u only. The union-bound count SAT(K+1) ≤ 2SAKT then needs K ≥ 1.
4. Lean caution, not a math issue: (K3) as stated says "c_T ≥ 125". The real requirement is c_T^{−1/3} ≤ 1/5 for the bound e^{−5ℓ_T}, together with the c_η inequality. Prove these with explicit numerals, not `nlinarith` on cube roots.
5. The plan script's check C tests only the minimal T. My check R covers larger T. The proof does not depend on minimality.

## 5. Go / no-go

**GO.** These parts are sound:
- the diagnosis: C41 is the only defect, and η < 1 is a sufficient correction;
- the corrected entry: it is faithful and stronger than the existential printed Prop;
- every proof step, with explicit constants c_η = 1/216 and c_T = 10⁴.

The main Lean risks are the ones the plan names:
- causality and factorization of `fedRun` through the time-first prefix;
- instance unification between `fedSamplingLaw` (local `⊤`) and the MVP reveal filtration.

A builder must not mark the result proved until the Lean export compiles and a critic reviews the integrated entry.
