# Critic report: Theorem 7.11 (corrected), M8 TD half

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Independent critic, 2026-11-09. Not the builder.

Files under review:
- `Formalization/TDInference/QuadraticForm.lean` (55 lines)
- `Formalization/TDInference/ZeroNoiseDecay.lean` (250 lines)
- `Formalization/TDInference/LeaveOneOut.lean` (273 lines)
- `Formalization/TDInference/LeaveOneOutBound.lean` (615 lines)

Briefs: the private corrected-theorem plan (M8), critic-thm7-11-corrected-plan-check.md §4 (F6–F8), critic-thm7-11-m5.md.

## Verdict: ACCEPT WITH FIXES

The fixes are minor: integration and hygiene. None of them is mathematical. Every reviewed export is
proved, axiom-clean, and states what the plan needs. Nothing hides a hypothesis.

## Evidence (commands actually run)

All runs used `bash scripts/lean-local.sh`, one Lean process at a time. Scratch files are in `reviewer-probes/`.

- **Fresh compile of each source file:** QuadForm, ZeroNoiseDecay, LeaveOneOut and LeaveOneOutBound each exit 0, with no errors and no warnings (`compile-*.out`).
  - The fast times (2–8 s) are genuine elaboration on the existing oleans.
  - A negative control (`Neg.lean`, a false `rfl` that imports LeaveOneOutBound) fails as expected.
- **`CriticProbe.lean`:** imports the full `Formalization` olean together with the four new modules, then runs `#print axioms` on all 43 declarations in the four files.
  - Result: exit 0, and all 43 depend only on `[propext, Classical.choice, Quot.sound]` (parsed with a script; 0 "does not depend").
  - Importing alongside the full library raised no name-collision errors.
  - A textual scan of `Formalization/` for each of the 43 names found no second definition.
- **grep of the four files:** no `sorry`, `admit`, `axiom` or `set_option`.
- **Oleans:** the `.olean` mtimes are later than the source mtimes for all four files and for LinCov711.

## Re-derivations

**(1) `looRemainder_eq`: correct, and the objects are the real ones.**
- **Definitions:**
  - `looDiff i x⋆ t ω = tdIter ω t − tdIter (update ω i x⋆) t`.
  - `looRemainder = (scaledError ω − scaledError ω') − (linPart ω − linPart ω')`, where `ω' = Function.update ω i x⋆`.
- **Indexing:** consistent with `tdIter`. `ω ⟨t,_⟩` drives `V_t → V_{t+1}` with `stepSize(t+1)`. `linWeight T k` and `linSummand T k (ω k)` carry the same `k` (`linPart_eq_sum`).
- **By hand,** with `δ_t` = looDiff:
  - `δ_t = 0` for `t ≤ i`.
  - `δ_{i+1} = −η'_i[(A_{ωi} − A_{x⋆})Δ_i + ξ_{ωi} − ξ_{x⋆}]`, from `tdStep_sub_value_eq` applied to the same `V_i`.
  - For `t > i`: `δ_{t+1} = δ_t − η'_t A_{ωt} δ_t = (I − η'_t A)δ_t − η'_t (A_{ωt} − A)δ_t`.
  - Variation of constants with `u_t = δ_{t+1} − (I − η'_tA)δ_t` gives `Σ_{t<T} δ_{t+1} = Σ_k (Σ_{t∈[k,T)} G_{k+1,t+1}) u_k = −linWeight_i z − Σ_{k>i} linWeight_k (A_{ωk} − A)δ_k`.
- **The cancellation:**
  - `scaledError` difference: `T^{-1/2}Σ δ_{t+1}`.
  - `linPart` difference: `linSummand_i(ω i) − linSummand_i(x⋆) = −T^{-1/2} linWeight_i (ξ_{ωi} − ξ_{x⋆})`.
  - The noise terms cancel exactly, which leaves the stated formula.
- `linIter` uses the same `noiseVec` as `tdStep_sub_value_eq`, so the cancellation is genuine and not a definitional accident.
- The Lean statement matches this derivation symbol for symbol.

**(2) Zero-noise decay: correct, and the hypotheses hold where used.**
- **Step formula:** `zeroNoiseStep_apply` gives `(1−η)v(s) + ηγ v(s')` at `s = x.1`, and `v(s)` elsewhere. That is the TD step with noise 0.
- **Jensen** (`sq_zeroNoise_le`): exact SOS identity, valid for `η, γ ∈ [0,1]`.
- **One-step conditional bound:**
  - `E_x[·] ≤ (1−μ(s))v(s)² + μ(s)((1−η)v(s)² + ηγ E_{P_π(s,·)} v²)`.
  - Under a uniform-in-`s` bound `Q`, this gives `(1 − μ(s)η(1−γ))Q ≤ (1 − μmin(1−γ)η)Q`.
  - `μmin` may have any sign. With negative `μmin` the conclusion is only weaker, so dropping `0 < μmin` is legitimate.
- **Invariance hypothesis:** `secondMoment_zeroNoiseStep_le` requires `g (update ω k x) = g ω`, which is used via `sum_pathWeight_mul_eq_sum_update`.
  - That resampling identity is proved by an involution on `(ω, x)`. It is correct for an arbitrary `g`.
- **Use site** (`sum_pathWeight_sq_looMart_le`):
  - `hinv` is discharged by `looDiff_update_of_le` with `t ≤ t`: `looDiff t` does not read `ω t`, because `tdIter_update_of_le` holds for both runs and `update_comm` covers `k ≠ i`.
  - `hrec` needs `i < t`, which follows from `i+1 ≤ t`.
  - `Q = (cη'_i)²` comes from the pathwise jump bound.
- **(R3, optional)** `max_secondMoment_zeroNoise_le` asks for `hinv` at every `t < T`, not only `t ≥ m`. This is stronger than necessary, but it is satisfied at the use site.

**(3) `weightedL2_looRemainder_le`: correct.**
- **First term:**
  - Pathwise, `|W_i(A_{ωi} − A_{x⋆})Δ_i (s)| ≤ K_β·(|Δ(ωi.1)| + |Δ(ωi.2.2)| + |Δ(x⋆.1)| + |Δ(x⋆.2.2)|)`.
  - So the square is at most `16K_β² Σ_u Δ_i(u)²`.
  - Taking expectations with `E Δ_i(s)² ≤ C'η'_i` gives `16K_β²SC'η'_i`.
  - `C' = 2C + D²/η₀` covers `i = 0` through `tdPathBound`. For `i ≥ 1` it uses `tdSecondMoment_le` together with `η_i ≤ 2η_{i+1}` (proved through the cube roots).
- **Martingale term:**
  - Orthogonality holds for adapted, centred terms. Centring uses `E_x(A_x − A)v = 0`.
  - The per-increment bound is `K²E_x(2δ_k(x.1)² + 2δ_k(x.2.2)²) ≤ 4K²Q_k`. It uses entrywise `|W_k(s,u)| ≤ K_β`, and the fact that `δ_k` does not depend on the fresh `x`.
  - With `Q_k = p_{i+1,k}(cη'_i)²`, the sum over `k > i` is at most `4K²c²η'_i·(η'_iσ_i) ≤ 4K³c²η'_i`, by `linStepSeq_mul_contrSum_le` from M5.
  - The reindexing from `k` to `t = k−1 ∈ [i,T)` is an over-count by nonnegative terms, so the bound is valid.
- **The constant:** `looConst = √(16K²SC') + √(4K³c²)` depends only on `(M, π, V₀, μmin, η₀)`, together with `card State` through the type. It is free of `i`, `T`, `x⋆` and `s`, as the signature confirms.
- **Hypotheses:** only `0 < η₀ ≤ 1` and `0 < μmin ≤ μ(s)`. `T ≥ 1` is implicit in `i : Fin T`.

**(4) Chen–Shao sum and `sum_range_sqrt_stepSize_le`: correct.**
- **Square-root sum:** `Σ_{t<n} √η₀ (t+1)^{-1/3} ≤ (3/2)√η₀ n^{2/3}`.
  - The termwise key inequality `1 ≤ (3/2)(u_{t+1}² − u_t²)u_{t+1}` with `u³` telescoping is checked by nlinarith via the SOS `(y−x)²(y+2x) ≥ 0`.
  - The bound needs no hypothesis on `η₀`: if `η₀ < 0`, both sides are ≤ 0 / `sqrt` clamps.
- **Chen–Shao sum:** `Σ_i (‖u‖₁T^{-1/2}K_βB)·(‖u‖₁K_loo T^{-1/2}√η'_i)` is at most `‖u‖₁²K_βBK_loo T^{-1}(3/2)√η₀ T^{2/3}`, which equals `‖u‖₁²K_CS T^{-1/3}`.
  - This uses `natCubeRoot_sq_div`, `E|b| ≤ ‖b‖₂`, and the projected L² bound via Minkowski.
  - The sup bound on `|uᵀlinSummand|` goes through `‖u‖₁` (CHECK F7).
  - `x⋆_i` may be an arbitrary deterministic family.

**(5) Quadratic form: correct.** An entrywise `|X(s,s')| ≤ c` gives `|uᵀXu| ≤ ‖u‖₁²c`, applied to M5's `abs_linCov_sub_le`. The target is `A⁻¹diag(Γ_true)A⁻ᵀ`, which is the C43-corrected Λ, with the same hypotheses as M5.

**(6) Interface for the Chen–Shao half: mathematically correct, with these precisions for M9.**
- **Summands:** `W = Σ_i w_i(ω i)`, with `w_i = uᵀlinSummand_i/σ` and `σ² = uᵀlinCov_T u`.
  - The `w_i` are independent under the product `pathWeight`.
  - Each is centred (`sum_tupleProb_mul_linSummand`).
  - `Σ E w_i² = 1` exactly (`sum_pathWeight_linPart_mul_linPart`).
- **Leave-one-out difference:** `Δ − Δ^{(i)} = uᵀlooRemainder_i/σ` holds definitionally whenever `Δ := uᵀ(scaledError − linPart − c)/σ` for any deterministic `c`.
  - **Recommendation:** take `c = 0`, keeping the transient inside Δ. Then `W + Δ = uᵀscaledError/σ` exactly, with no shift to absorb.
  - `weightedL2_proj_scaledError_sub_linPart_le` already bounds that Δ (transient included) at `‖u‖₁K_E T^{-1/3}`.
  - DESIGN.md still mentions a separate "transient" in Δ. No Lean object of that name is defined in these files. Treat it as stale prose (R2).
- **The `E|WΔ|` term:** `E|WΔ| ≤ ‖W‖₂‖Δ‖₂ = ‖Δ‖₂ ≤ ‖u‖₁K_E T^{-1/3}/σ`. This is correct.
- **The leave-one-out term:** `Σ_i E|w_i(Δ−Δ^{(i)})| = σ^{-2}·(sum in sum_looChenShao_le) ≤ ‖u‖₁²K_CS T^{-1/3}/σ²`. This is correct.
- **Independence:** the Chen–Shao (2007, Thm 2.1) hypothesis is that `ξ_i` is independent of the pair `(W − ξ_i, Δ^{(i)})`, jointly, not only of `Δ^{(i)}`.
  - Both `W − w_i` and `Δ(update ω i x⋆)` are functions of `ω_{−i}`, so this holds under `pathWeight`.
  - The generic H2 export must state its hypothesis in this joint form (or as functions of the other coordinates).
- **β-terms:** `|w_i| ≤ ‖u‖₁T^{-1/2}K_βB/σ` (`abs_proj_linSummand_le`), so `Σ E|w_i|³ ≤ max|w_i|`, which is `O(T^{-1/2})/σ`.

**(7) Hidden hypotheses and non-vacuity.**
- No signature in the four files contains `Γ ≻ 0`, stationarity, `T`-large, or any `trueGamma` positivity.
- The only hypotheses are `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, and `1 ≤ T` where needed.
- The builder's probe on instance G is meaningful:
  - It discharges every hypothesis with `η₀ = 1/8` and `μmin = 1/2`.
  - It shows `Γ_true = (25/128, 1/128) ≻ 0`.
  - It shows the TD noise is non-zero at `(0,0,0)`, so `linSummand` is not identically zero and the Chen–Shao sum is not trivially 0.
- These are upper-bound statements with finite explicit constants, so they cannot be vacuous in the "false premise" sense.

## Findings

- **R1 (hygiene, required before landing):** `norm_noiseVec_le_tdNoiseBound` (LeaveOneOutBound711:160) duplicates `TDInferenceSmooth711.norm_noiseVec_le` (same statement, same namespace).
  - Use the existing lemma and import Smooth711, or move one copy into a shared lower module (e.g. Operator711).
  - Not a correctness issue.
- **R2 (docs, required):** update the DESIGN interface note.
  - Δ should keep the transient, i.e. `Δ = uᵀ(scaledError − linPart)/σ`.
  - Record the joint-independence form of the Chen–Shao hypothesis (see (6)).
- **R3 (optional):** weaken `hinv` in `max_secondMoment_zeroNoise_le` to `m ≤ t`.
- **R4 (integration, lead):** the four modules are not yet imported from `Formalization.lean`. Add them so that `Audit.lean` / `scripts/check.py` covers them. Verified: no collisions when importing them alongside the full library.
- **No R/F findings against mathematics, statements, or source fidelity.** These are infrastructure lemmas only, and no source result is claimed.

## Notes for M9

1. **Normalisation.** Use `σ² = uᵀlinCov_T u > 0`, and add `∀ s, 0 < trueGamma` yourself (CRITIC-M5).
   - For a lower bound uniform in `T`, combine `abs_quadForm_linCov_sub_le` with `σ_u² ≥ minΓ‖u‖_∞²/4` and `‖u‖₁ ≤ S‖u‖_∞`.
   - For `T < T₀`, use the trivial bound (CHECK F7).
2. **Stated rates.** All rates above carry `‖u‖₁` or `‖u‖₁²` over `σ` or `σ²`. Under the `‖u‖_∞` normalisation these are instance constants. Keep that scale invariance explicit.
3. **Chen–Shao instantiation.** Instantiate the generic H2 export with `p_i = tupleProb` (identical laws) and `ξ_i = w_i(ω i)`.
   - Use `Δ^{(i)}(ω) = Δ(update ω i (xs i))` for any fixed `xs`.
   - The H2 export must accept `Δ^{(i)}` as a function not reading coordinate `i`. `looRemainder` is stated with exactly that `update`.
4. **The variance step and F8 projection** remain M9 obligations, untouched here.
