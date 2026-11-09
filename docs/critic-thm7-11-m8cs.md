# CRITIC: Theorem 7.11 (corrected), milestone M8, generic half (Chen–Shao, H2)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Critic: independent reviewer (not the builder). Date: 2026-11-09.
Files reviewed (sha256 matches builder STATUS):
- `Formalization/Probability/SteinRandomConcentration.lean`, 296 lines, `d3576651…1123009`
- `Formalization/Probability/ChenShaoNonlinear.lean`, 337 lines, `38431670…161e3e`

## Verdict: ACCEPT

There are no blocking findings, and no R/F findings against the mathematics or the statements. R1–R3 below are docs and integration items.

## Evidence (commands I ran myself; one Lean process at a time)

- `bash scripts/lean-local.sh Formalization/Probability/SteinRandomConcentration.lean`: exit 0, no output.
- `bash scripts/lean-local.sh Formalization/Probability/ChenShaoNonlinear.lean`: exit 0, no output.
- `bash scripts/lean-local.sh reviewer-probes/Probe.lean`: exit 0. Output is in `reviewer-probes/probe.out`.
  - The probe does `import Formalization` + `import Formalization.Probability.ChenShaoNonlinear`. That combination raises no name collisions with the full library.
  - A grep for each declared name in all other `Formalization/**` files also found nothing.
  - `#print axioms` on all 28 named declarations gives `[propext, Classical.choice, Quot.sound]`.
  - An environment scan of every constant whose home module is one of the two files (62 constants, auxiliaries included) found no other axiom.
  - Two adversarial examples elaborate. In the first, `chenShao_nonlinear` is applied with `Δ = −W/2`, which reads every coordinate and is negative on half the space, and `Δ⁽ⁱ⁾ = −W⁽ⁱ⁾/2`; every hypothesis is discharged. The second proves that `hΔi` rejects a `Δ⁽ⁱ⁾` that reads `ω i`, so the hypothesis is not vacuous.
- A grep for `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|set_option` in both files finds nothing.

## Reconstruction

### (1) The sandwich, with closed `intervalInd` and either sign of Δ
`intervalInd a b v = 1{a ≤ v ≤ b}` (`SteinGaussian.lean:215`).

- **`ite_add_le_ite_add_intervalInd`.** Suppose `T = W+Δ ≤ z` and `W > z`. Then `z < W ≤ z − Δ ≤ z + |Δ|`, so `W ∈ [z, z+|Δ|]`. Hence `1{T≤z} ≤ 1{W≤z} + 1{z≤W≤z+|Δ|}`.
- **`ite_le_ite_add_add_intervalInd`.** Suppose `W ≤ z` and `T > z`. Then `W > z − Δ ≥ z − |Δ|`, so `W ∈ [z−|Δ|, z]`.
- Using `|Δ|` covers both signs of Δ. The closed intervals only enlarge the events and appear only on the upper-bound side, so this is correct.
- In `chenShao_nonlinear`, `PT ≤ PW + P_up` and `PW ≤ PT + P_low` combine with BE (`26β`) and the two concentration bounds (each `2β + …`) to give `28β + E|WΔ| + Σ E|ξᵢ(Δ−Δ⁽ⁱ⁾)|` in both directions. I checked this by hand, and it matches the Lean `linarith` close.

### (2) Randomized concentration (`pexp_intervalInd_random_le`)
I re-derived the proof:
- `f = ramp(Δ₁,Δ₂,δ)` with `|f| ≤ (Δ₂−Δ₁)/2 + δ`, which needs `Δ₁ ≤ Δ₂` (`h12`). So `E[Wf(W)] ≤ Q/2 + δ·E|W| ≤ Q/2 + δ`, using `E|W| ≤ 1` from `EW² = 1`.
- Stein step: `E[ξᵢ fᵢ(W⁽ⁱ⁾)] = 0`, where `fᵢ = ramp(D₁ᵢ, D₂ᵢ, δ)`. Here `fᵢ` and `W⁽ⁱ⁾` do not read `ω i`, and the law is a product with `Eξᵢ = 0`. This is N1, via `pexp_comp_coord`. It needs exactly the `hD₁`/`hD₂` invariance, and both endpoints' leave-one-out versions must be invariant. They are hypotheses, so this is fine.
- Split: `ξᵢ(f(W)−fᵢ(W⁽ⁱ⁾)) = ξᵢ(f(W)−f(W−ξᵢ)) + ξᵢ(f(W⁽ⁱ⁾)−fᵢ(W⁽ⁱ⁾))`.
  - The first sum is `≥ 1{Δ₁≤W≤Δ₂}·Σ|ξᵢ|min(δ,|ξᵢ|)` pathwise (slope-1 segment of length ≥ δ around `[Δ₁,Δ₂]`; elsewhere the term is ≥ 0 by monotonicity).
  - The second is `≥ −|ξᵢ|(|Δ₁−D₁ᵢ|+|Δ₂−D₂ᵢ|)/2`, by N2 (`abs_ramp_sub_ramp_le`). N2 has no ordering requirement on `D`, which is correct: the D's are not assumed ordered.
- Variance part (`pexp_mul_steinH_le`):
  - `x² − |x|³/(4δ) ≤ |x|min(δ,|x|)`, which is `(t−2δ)² ≥ 0`.
  - `Var H ≤ Σ E h(ξᵢ)² ≤ δ²Σ Eξᵢ² ≤ δ²`.
  - `E[A]·m ≤ E[AH] + E|H−m|` for `A ∈ [0,1]`.
  - Together: `E[A](1 − β/(4δ)) ≤ E[AH] + δ`.
- With `δ = β/2` we get `β/(4δ) = 1/2`, so `P/2 ≤ (Q/2 + δ + R/2) + δ`, i.e. `P ≤ Q + 4δ + R = Q + 2β + R`. This is exact. `δ > 0` comes from `lyapunov_pos`, which needs `hvar` and `hp0`.

### (3) Coefficients and comparison with Chen–Shao (2007, Thm 2.1), from memory
- Chen–Shao: `|P(W+Δ≤z) − Φ(z)| ≤ 4.1(β₂+β₃) + E|WΔ| + Σᵢ E|ξᵢ(Δ−Δ⁽ⁱ⁾)|`, with truncated moments β₂, β₃. Their randomized concentration lemma has the shape `4δ + E|W(Δ₂−Δ₁)| + Σ E|ξᵢ(Δ₁−Δ₁⁽ⁱ⁾)| + Σ E|ξᵢ(Δ₂−Δ₂⁽ⁱ⁾)|`.
- The export has coefficient 1 on `E|WΔ|` and coefficient 1 on the leave-one-out sum, which is the Chen–Shao form.
  - For the upper interval, `|Δ₂−D₂ᵢ| = ||Δ|−|Δ⁽ⁱ⁾|| ≤ |Δ−Δ⁽ⁱ⁾|` and `D₁ = Δ₁ = z`.
  - For the lower interval it is symmetric.
- Only the β-constant differs: `28β`, with untruncated third moments, instead of `4.1(β₂+β₃)`. This is weaker but legitimate, and on finite spaces third moments exist.
- Independence: ξᵢ depends on `ω i` only. `W−ξᵢ = looStat` and `Δ⁽ⁱ⁾` are functions of `ω_{−i}` (`looStat_update`, `hΔi`). The law is a product. So the Chen–Shao joint hypothesis (ξᵢ ⫫ (W−ξᵢ, Δ⁽ⁱ⁾)) is built into the encoding, as TD-critic R2 requires.

### (4) Gaussian lemmas (N4)
- `φ ≤ (2π)^{-1/2} ≤ 1/2`. `|x|φ(x) ≤ 1/2` follows from `|x| ≤ e^{x²/2}` (true value `φ(1) ≈ 0.242`). `Φ` is ½-Lipschitz by the mean value theorem.
- `abs_stdCDF_div_sub_le_of_le`: `|d/ds Φ(z/s)| = |z/s|φ(z/s)/s ≤ 1/(2a)` on `[a,b]`. I checked all three cases of `abs_stdCDF_div_sub_le`:
  - `b ≤ a` needs `b ≤ 4(a+b)`.
  - `a ≤ b ≤ 2a` needs `b² ≤ 4a(a+b)`.
  - `b ≥ 2a` uses the trivial bound 1 and `a²/b² ≤ 1/4`.
- The bound is uniform in z.
- The CDF here is `stdCDF`, while the Chen–Shao exports use `(gaussianReal 0 1).real (Iic ·)`. The bridge `gaussianReal_real_Iic` exists, and `berryEsseen_stein` uses it.

### (5) Hidden hypotheses and junk
- z is arbitrary. Δ is an arbitrary real function. `Δi` carries only the invariance hypothesis. There is no boundedness, measurability or sign condition, and no β-smallness (the old `β ≤ 1/8` of `pexp_intervalInd_looStat_le` is gone).
- Empty index: `hvar` (`Σ Var = 1`) or `σ > 0` with `Σ Var = σ²` cannot hold. This is intrinsic to the normalisation, not a smuggled premise.
- `chenShao_nonlinear_of_var` parses as `(28β)/σ³ + E|WΔ|/σ² + (Σ …)/σ²`, which is the correct scaling for `W' = W/σ`, `Δ' = Δ/σ`.
- `chenShao_nonlinear_zero` honestly gives 28, not 26.

### (6) Adequacy for the TD instantiation (DESIGN.md, CRITIC-m8td R2)
- Take `X i = Tuple`, `p i = tupleProb`, `ξᵢ = wᵢ`, `Δ = uᵀ(scaledError − linPart)/σ` with the transient kept inside, and `Δ⁽ⁱ⁾ = Δ(update ω i x⋆)`. Then `chenShao_nonlinear_update` / `_of_var` apply directly.
- `Δ − Δ⁽ⁱ⁾ = uᵀlooRemainder/σ`, which is what `sum_looChenShao_le` bounds.
- `E|WΔ|` goes through N3 (`pexp_abs_mul_le_sqrt`) and `weightedL2_proj_scaledError_sub_linPart_le`.
- The interface is adequate.

## Required / recommended items

- **R1 (docs, required):** fix the stale line in `builder-probes/STATUS.md` ("Design"). It still states the planned bounds with coefficient **2** on the leave-one-out sum. The delivered exports have coefficient 1, a sharper bound than planned, and the note must not be copied into ledgers.
- **R2 (integration, lead):** neither module is imported from `Formalization.lean`, so `Audit.lean` / `scripts/check.py` do not cover them yet. Add them, or add the M9 module that imports them (`Ch7Rest/TDInferenceHalfSpace711.lean` already imports `ChenShaoNonlinear`). I verified there are no collisions alongside the full library.
- **R3 (optional):** the `28β` constant could be documented next to Chen–Shao's `4.1(β₂+β₃)` in the module docstring, so readers do not mistake the export for the original constant. Nothing in the source of Thm 7.11 depends on the constant.
- No F-findings. These are infrastructure lemmas, and no source result is claimed.

## Notes for M9
1. **The two Φ forms.** Chen–Shao exports compare with `(gaussianReal 0 1).real (Iic (z/σ))`. `abs_stdCDF_div_sub_le` is stated for `stdCDF`. Rewrite with `gaussianReal_real_Iic`.
2. **Variance mismatch.** Use `a = σ_T`, `b = σ_true` (or vice versa), giving `2|σ_T²/σ_true² − 1| = 2|uᵀ(linCov_T − Γ)u|/σ_true²`. Then apply `abs_quadForm_linCov_sub_le` with the `σ_true² ≥ c‖u‖²` lower bound. Both sides must be > 0, so this needs `Γ_true ≻ 0` and `σ_T > 0`. For small T where `σ_T` may vanish, use the trivial bound (CHECK F7).
3. **`hvar`.** `hvar` must be exactly `Σᵢ E wᵢ² = σ_T²`, i.e. `uᵀlinCov_T u` must equal the sum of per-coordinate second moments of `linSummand` under `tupleProb`. Check that this identity, and `E wᵢ = 0`, are available from M5.
4. **`pexp` vs `pathWeight`.** M9 needs `pexp (fun _ ↦ tupleProb) F = Σ_ω pathWeight ω · F ω`. This should be definitional or a one-line `rfl`/`simp`.
5. **Rates.** `β = Σ E|wᵢ|³ ≤ maxᵢ|wᵢ|·Σ E wᵢ²`, which is `O(T^{-1/2})‖u‖₁/σ`. `28β/σ³` in `_of_var` is in the original ξ scale, so keep the σ powers consistent: β is computed for unnormalised `wᵢ`.
