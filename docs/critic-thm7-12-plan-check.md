# CHECK: the builder's private plan (online VPO regret, `thm_online`) — independent source/paper-proof critic

Public copy of the independent critic report; local paths removed.

Critic: independent agent, source-first, no Lean compiled, cen2025vpo not consulted. Date 2026-11-07.
Source `source/upstream/tex/chapters/RLHF.tex` sha256 `e60115c355d44cba835b2323cc76fef50bfbfb646644686d989115af54f4df90`.
Plan script sha256 `bc972b5b…1c68` (matches the plan). Critic script
`<reviewer check folder>/check_local_route.py` (sha256 `f3ce98c0e49e44ca9c2282fdd5d7281ab87ca1d2430228f83879a07b322e2c7a`),
run with `python3 -I check_local_route.py`, output `<reviewer check folder>/run.log`
(sha256 `3287f83b4a3ba16ea8e653477965fb4e9785a9ec9c21bf45db0e53c2e9204b58`), 4 PASS, `ALL PASS`, exit 0, seed 20261107.
Not author-approved. Evidence only.

## 0. Source reconstruction (done before reading the plan)

Setting: BT oracle `P(y1≻y2|x)=σ(r⋆(x,y1)−r⋆(x,y2))` (:24–28); NLL ℓ (:31–39); `J(r,π)` (:41–47); Gibbs
closed form and Z (:52–59, sum over 𝒴, so 𝒴 is at most countable); calibrated `J(r,π;π_cal)` (:92–96); `J⋆` as a
max (:99–102); VPO with α > 0 (:109–113); policy form (:126–134); linear reward with ‖φ‖₂ ≤ 1, r⋆ = ⟨φ,θ⋆⟩
(:146–153). Online procedure (:158–177): `D^{(t)} = {(x^{(s)},y₊^{(s)},y₋^{(s)})}_{s=1}^{t}` (:162). Algorithm
(:182–203): loop `t = 0,1,2,…` (:188); sample `x^{(t)}∼ρ`, `y1,y2 ∼ π^{(t)}(·|x)` (:190); update `π^{(t+1)}` by the
printed argmin with `∑_{s=1}^{t}` (:196) plus `αβ E_{ρ,π_cal}[log π − log π_ref]`.
Theorem 7.12 (:208–215): under linear reward, with `r_{θ^{(t)}}` the reward of `π^{(t)}`, assuming
`‖θ⋆‖ ≤ r_max` and `‖θ^{(t)}‖ ≤ r_max ∀ t ≥ 0`, with probability 1−δ,
`∑_{t=1}^{T}[J⋆(r⋆;π_cal) − J(r⋆,π^{(t)};π_cal)] ≤ Õ(e^{2r_max + r_max/β} √(κ d T))` for
`α = e^{−(2r_max+r_max/β)} √(T/(κ min{d log T, T}))`, `κ = sup π_cal/π_ref`.

My reconstruction agrees with plan §1.1 in every quantifier, constant and index. Note `∀ t ≥ 0` covers `θ^{(0)}`,
which the regret (t = 1..T) does not use; harmless.

## 1. Verdicts on (1) transcription and findings

| Item | Verdict |
|---|---|
| §1.1 transcription | **Confirmed.** |
| 1.2.1–1.2.4 (C44: α at T=1, no minimizer, iterate hypothesis, free δ) | **Confirmed** (already in C44). |
| 1.2.6 off-by-one (:188 vs :196, also :162) | **Confirmed**, correctly classified as an index quirk, not an error. Round-0 sample is never used; `π^{(1)}` comes from the empty dataset (pure regularizer, which is exactly C44's unbounded-below case). The plan's indexing `θ_t = sel(D^{(t−1)})`, round s sampled from `π^{(s)}` matches :190/:196. |
| 1.2.7 unspecified objects | Confirmed. Finite 𝒳 is a genuine restriction (source allows general ρ); must be disclosed. |
| **1.2.5 "Õ hides a factor d"** | **Refuted as worded; must be rewritten.** What is true: printed α is the tuning of `T·B/α + α·K·Γ` with `B = O(1)` (polylog) and `Γ = min{d log T,T}`, and every *uniform* likelihood-ratio width over a d-ball is `≍ d log`. Hence the *plan's* argument cannot give `√(κdT)`. It does **not** follow that the printed rate is false or hides a d: §4 below gives a different argument for the same algorithm that achieves the printed `√(dT)` scaling (for T ≳ d³ polylog). The plan's "rate" lines are circular (they divide the plan's own bound formula by d) and are not evidence about the true rate. |

## 2. Verdict on (2) the restricted formulation

**Sound and essentially the weakest well-posed reading, with two disclosures to add.**
- Ball-constrained argmin over Gibbs policies `{π_θ : ‖θ‖ ≤ R}` of the printed objective is the right repair: the printed
  theorem already presupposes `π^{(t)}` is Gibbs-linear ("corresponding reward model", :209), and the unconstrained
  argmin need not exist (C44). It is not weaker than the printed reading — it *subsumes* it per trajectory: the rule
  `sel(D) := unconstrained Gibbs minimizer if one exists in the ball, else any ball minimizer` is an admissible
  selection rule, and the statement quantifies over every rule. Add this remark to the docstring.
- Same R for `‖θ⋆‖` and the constraint, as printed. `θ⋆` in the ball is used (optimism). No hidden hypothesis found.
- Sampling model per round, realized (pseudo-)regret w.h.p., explicit δ, any α > 0 with T ≥ 1, `κ` as a finite max:
  all faithful. Disclose finite 𝒳 (and finite 𝒴) as a restriction.
- Nothing hidden in B′, Γ, K: I re-derived them (§3).

## 3. Verdict on (3) proof steps — all re-derived, **correct**

- Decomposition `reg_t = [J⋆(θ⋆) − J⋆(θ_t)] + Δ_t` via `J⋆(θ_t) = J(θ_t,π_t)` (L1): correct.
- Optimism: `L(θ_t) ≤ L(θ⋆)` ⇒ `J⋆(θ⋆) − J⋆(θ_t) ≤ (ℓ(θ⋆) − ℓ(θ_t))/α`: correct sign.
- L1 (Gibbs variational, `β log Z − (Σpr − βKL(p‖q)) = βKL(p‖π_r)`), L2, L3 (Z cancels in differences; cal term = −αJ⋆): correct.
- L5: KL cancels, `Δ = −E_x Σ π_cal (g − m_x)`, CS gives `√(max π_cal/π_t) ≤ √κ e^{R/β}`, `Var = D/2`, Jensen: `c₁ = √(κ/2) e^{R/β}`. Correct.
- L6 (`(p−q)² ≤ 1−BC² ≤ 2H²`), L7 (`σ' ≥ 1/(3+e^{2R}) ≥ 1/(4e^{2R})`, ⇒ `⟨d,w⟩² ≤ 32e^{4R}H²`): correct; `c_H = 2/32·e^{−4R}` from `ℓ⋆−ℓ′ < 2log − 2ΣH²`: correct.
- E₁: `E[√(p_{θ'}/p⋆)] = BC = 1−H²` under `o∼p⋆` given (h_{<s}, z_s), product = `exp(½(ℓ(θ⋆)−ℓ(θ')))`; L8 with a joint (z,o) kernel; union over T·N; transfer `2n/T ≤ 2` and `16R·c_H ≤ 1/(4e)`: correct, B′ = B + 1.
- Step 3 (`Σ⟨d_s,w⟩² ≥ ‖w‖²_V − 16R²`, λ = 4), Step 4 AM–GM, `K = c₁²/(4c_H) = 2κe^{4R+2R/β}`, Step 5 (`R²e^{−4R} ≤ 1`): correct.
- E₂ (`X_t ∈ [0,1]` since λ = 4, ‖d‖ ≤ 2; conditional mean u_t; `e^{−x} ≤ e^{−(1−1/e)x}`-type supermartingale), L11 (`x ≤ 2log(1+x)` on [0,1], det lemma, `det ≤ (tr/d)^d`, `tr ≤ 4d+4T`): correct.
- Grid cover (side `1/(T√d)`, diameter 1/T, `M = ⌈2RT√d⌉ ≥ 1`): correct.
- Printed-α instance `e^{c}√(κT)(B′√m + 2Γ/√m)` with `c = 2R+R/β`: correct arithmetic.
Conclusion: **`Regret ≤ T·B′/α + K·Γ·α` w.p. ≥ 1−δ is a correct theorem**; at tuned α it is `O(e^{2R+R/β} d √(κT) · log)`.

## 4. KEY QUESTION: is the printed `√(κdT)` rate false, open, or reachable?

**No d√T lower bound applies; the printed rate is not refuted.** Two reasons.

(a) *Information-theoretic.* The per-round regret is a KL-regularized gap: `J⋆(r⋆) − J(r⋆,π) = β E_x KL(π(·|x)‖π_{θ⋆}(·|x))`
(check R1, exact to 1e−15). This is quadratic in the parameter error, unlike unregularized linear/dueling bandits
where `Ω(d√T)` (infinite action sets) is the relevant lower bound. For fixed β the KL-regularized problem admits
logarithmic-in-T regret (consistent with the KL-regularized contextual-bandit literature; I did not rely on it). So no
algorithm-independent `d√T` lower bound exists for this objective at fixed β, R; a refutation would have to be
VPO-specific, and I found none.

(b) *A sharper argument for VPO itself (new; "local-curvature route").* Using only pieces already in the plan (E₁, E₂, L11):
1. Bregman form: `β KL(π_θ‖π_{θ⋆}) = A(θ⋆) − A(θ) − ⟨∇A(θ), θ⋆−θ⟩` with `A(θ) = β E log Z`, `∇²A = β⁻¹ Cov_{π_θ}φ`; on the ball,
   density ratios between Gibbs policies are ≤ `e^{4R/β}`, so `reg_t ≤ (e^{4R/β}/(4β)) · D_t` (check R2, max ratio 0.70).
2. `D_t ≤ ‖w_t‖²_{V_t} u_t` (L10).
3. Optimism the other way: `ℓ(θ_t) − ℓ(θ⋆) ≤ α(J⋆(θ_t) − J⋆(θ⋆)) ≤ 2α‖w_t‖ ≤ 4Rα` (‖∇J⋆‖ ≤ 2, check R3), and E₁ gives
   `c_H Σ_{s<t}⟨d_s,w_t⟩² ≤ B + ℓ(θ_t) − ℓ(θ⋆) ≤ B + 4Rα`, so `‖w_t‖²_{V_t} ≤ 16R² + 16e^{4R}(B′ + 4Rα)`.
4. Sum with E₂: **`Regret ≤ (e^{4R/β}/(4β)) · (16R² + 16e^{4R}(B′ + 4Rα)) · Γ`** w.p. ≥ 1−δ.
At the printed α this is `≍ (R/β) e^{2R+3R/β} √(dT log T / κ) + (1/β) e^{4R+4R/β} d² log² T` (check R4: the α-term
normalized by `√(dT log T)` stays in 5.8k–8.1k over d ∈ {1..64}, T ∈ {10⁸..10¹⁶}). Hence VPO with the printed α has
regret `Õ(√(dT))` in its (d,T) scaling whenever `T ≳ d³`, matching the printed rate up to the exponential/β/κ constants.
(It also shows small α — near-greedy — gives `O(d² log² T)` regret, consistent with (a).)

What remains open: the printed form exactly, i.e. constant `e^{2R+R/β}√κ` (the local route has `e^{2R+3R/β}·R/β·κ^{−1/2}`
plus an additive `e^{4R+4R/β} d² log²T/β`) and the regime `d ≤ T ≲ d³`. Neither argument implies the printed bound;
nothing refutes it. **Status: printed rate neither proved nor refuted** (open, not false).

Route to the printed rate: not available from the two arguments here; combining them gives
`Regret ≤ min{T B′/α + KΓα, C_loc(B′ + 4Rα)Γ}`, which at the printed α is `Õ(min{d^{3/2}√T, √(dT) + d²})` — i.e.
`Õ(√(dT))` in d,T for `T ≳ d³` but with `e^{3R/β}/β` in place of `e^{R/β}` and a different κ-power. Matching the printed exponent would
need a variance-aware (local Fisher) confidence width; I do not see a short proof.

## 5. Naming decision (AGENTS.md "Statement index")

The export assumes something different (ball-constrained argmin; finite 𝒳,𝒴; T ≥ 1 free α) and concludes something
not implying the printed rate. Per AGENTS.md this needs a suffixed entry pointing to SOURCE-ISSUES. Because the printed
statement is ill-posed (C44) and the conclusion is changed (explicit bound, different constants/d-power), it is a
**corrected** statement, not a restriction of a true printed claim. **Use `Thm7_12_corrected`**, not `_restricted`.

Proposed docstring (core wording):
> Corrected, well-posed variant of `thm_online` (RLHF.tex:208–215; algorithm :182–203; setup :21–59, :92–102, :146–153).
> Differs from the printed result: (i) the update is the printed VPO objective minimized over Gibbs policies
> `{π_θ : ‖θ‖₂ ≤ r_max}` (any minimizer; the printed argmin over all π need not exist, C44), which covers every printed
> run whose iterates exist with `‖θ^{(t)}‖ ≤ r_max`; (ii) 𝒳, 𝒴 finite; (iii) any α > 0 and T ≥ 1 (printed α is an
> instance only for T ≥ 2); (iv) δ explicit; (v) the conclusion is the explicit bound `T·B′/α + K·Γ·α`
> [optionally `min{…, C_loc(B′+4Rα)Γ}`], which at tuned α is `O(e^{2r+r/β} d√(κT)·log)`. **The printed rate
> `Õ(e^{2r+r/β}√(κdT))` is neither proved nor refuted here.** See SOURCE-ISSUES.md#C44.

Optional second entry if the local route is built: `Thm7_12_corrected_local` (same hypotheses, conclusion
`Regret ≤ (e^{4R/β}/(4β))(16R² + 16e^{4R}(B′+4Rα))Γ`), docstring noting it gives the printed `√(dT)` scaling for `T ≳ d³`
at the printed α with different constants.

## 6. Required corrections before builders start

1. Rename `Thm7_12_restricted` → `Thm7_12_corrected`; use the docstring of §5.
2. Rewrite plan §1.2.5 and the proposed C44 addendum: drop "Õ hides a factor d"; say instead "our likelihood-ratio
   argument gives `d√(κT)·log`; the printed `√(κdT)` is neither proved nor refuted; no `d√T` lower bound applies to the
   KL-regularized regret; a local-curvature argument yields `Õ(√(dT))` scaling for `T ≳ d³` with constant
   `e^{2R+3R/β}R/β`". Remove the "rate" lines as evidence (circular).
3. Add to the docstring the per-trajectory subsumption remark (§2) and the finite-𝒳 disclosure.
4. Recommended (cheap, ~150 Lean lines in `VPOGibbs712`/`VPORegret712`): prove the Bregman/variance lemma R2 and the
   local bound, exporting the min of both bounds. Not required for honesty.
5. The plan's numerical evidence is fine as lemma spot-checks; do not cite it for rates.

## 7. Go / no-go

**GO** for building the plan's proof (all steps verified), **conditional on corrections 1–3** (naming and the
rewording of finding 1.2.5 / C44 addendum). NO-GO for any wording that calls the printed rate false, says Õ "hides" a
d, or labels the entry `_restricted` of the printed claim.
