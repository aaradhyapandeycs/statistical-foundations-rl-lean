import Formalization.Ch7Rest.TDInferencePluginSingular711
import Formalization.Ch7Rest.TDInferenceMartingale711

/-!
# Plug-in estimator consistency, first steps: `Ā_T → A` (C3(a)) and oracle `Γ̂ → Γ_true` (C3(b))

Source: `chapters/inference.tex:166` (definitions of `A_t` and `Ā_T`), :172 (`Ā_T` and `Γ̂_T` as
estimators of `A` and `Γ`), `A = diag(μ)(I − γP_π)` :110. Not a printed claim; it is the first input to the consistency of `Λ̂_T` for the corrected
`Λ = A⁻¹Γ_trueA⁻ᵀ` (SOURCE-ISSUES C43, C47(4)).

* `sum_tupleProb_mul_sampleAMat`: `E[A_t] = A` entrywise.
* `abs_sampleAMat_apply_le`: every entry of `A_t` lies in `[−1, 1]`.
* `sum_pathWeight_mul_sq_aBar_sub_le`: `E(Ā_T − A)²_{sj} ≤ 1/T` for `T ≥ 1`.
* `pathProb_abs_aBar_sub_gt_le`: Chebyshev, `P(|Ā_T(s,j) − A(s,j)| > ε) ≤ 1/(ε²T)`.
* `pathProb_exists_abs_aBar_sub_gt_le`: all entries at once, `≤ S²/(ε²T)`.
* `oracleGammaHat`: `Γ̂_T(s,s)` with `V̄_T` replaced by `V^π`; `E` of each summand is `Γ_true(s)`
  (`sum_tupleProb_mul_oracleTerm`), so it targets the corrected `Γ_true`, not the printed `Γ` (C43).
* `pathProb_abs_oracleGammaHat_sub_gt_le`: `P(|Γ̂^{or}_T(s) − Γ_true(s)| > ε) ≤ 2B⁴/(ε²T)`,
  `B = tdNoiseBound` (uses `∑_t w_{t,T}² ≤ 2/T`).

The remaining steps (the substitution `V̄_T → V^π` in `Γ̂_T`, the inverse perturbation for
`Ā_T⁻¹`, and the assembly) are in `TDInferencePluginCorrected711.lean`, which proves
`P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) → 0`: convergence in probability, with no rate.

Norms are entrywise absolute values (matrix norms are only scoped instances in Mathlib).
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

omit [DecidableEq State] in
/-- Chebyshev/Markov for path functions: `P(ε < |g|) ≤ E g² / ε²`. -/
theorem pathProb_lt_abs_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (g : (Fin T → Tuple State Action) → ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    pathProb M π μ T {ω | ε < |g ω|} ≤ (∑ ω, pathWeight M π μ ω * g ω ^ 2) / ε ^ 2 := by
  rw [le_div_iff₀ (by positivity), pathProb, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
  by_cases h : ε < |g ω|
  · rw [Set.indicator_of_mem (show ω ∈ {ω | ε < |g ω|} from h), one_mul, ← sq_abs (g ω)]
    exact pow_le_pow_left₀ hε.le h.le 2
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ε < |g ω|} from h), zero_mul]
    positivity

/-- `E[A_t] = A` entrywise. -/
theorem sum_tupleProb_mul_sampleAMat (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s j : State) :
    ∑ x, tupleProb M π μ x * sampleAMat M x s j = tdA M π μ s j := by
  have hrow : ∀ x : Tuple State Action, tupleProb M π μ x * sampleAMat M x s j =
      (if x.1 = s then tupleProb M π μ x else 0) * (if j = s then 1 else 0) -
        M.discount * (if x.1 = s ∧ x.2.2 = j then tupleProb M π μ x else 0) := by
    intro x
    rw [sampleAMat_apply]
    by_cases h1 : x.1 = s
    · subst h1
      by_cases h2 : x.2.2 = j
      · subst h2; simp; split_ifs <;> ring
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_tupleProb_fst_eq]
  have h2 : ∑ x : Tuple State Action, (if x.1 = s ∧ x.2.2 = j then tupleProb M π μ x else 0) =
      μ.prob s * (M.policyTransition π s).prob j := by
    simp only [Fintype.sum_prod_type, DiscountedMDP.policyTransition_prob,
      FiniteDistribution.expectation, tupleProb]
    rw [Finset.sum_eq_single s]
    · simp only [true_and, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      ring
    · intro b _ hb; simp [hb]
    · simp
  rw [h2]
  simp only [tdA, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    policyMatrix, Matrix.of_apply, smul_eq_mul]
  by_cases hjs : j = s
  · subst hjs; simp; ring
  · simp [hjs, Ne.symm hjs]; ring

/-- Every entry of `A_t` lies in `[−1, 1]`. -/
theorem abs_sampleAMat_apply_le (M : DiscountedMDP State Action) (x : Tuple State Action)
    (s j : State) : |sampleAMat M x s j| ≤ 1 := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  rw [sampleAMat_apply]
  split_ifs <;> simp <;> (try rw [abs_le]) <;> constructor <;> linarith

/-- `E(Ā_T − A)²_{sj} ≤ 1/T` for `T ≥ 1`. -/
theorem sum_pathWeight_mul_sq_aBar_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    (s j : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (aBar M ω s j - tdA M π μ s j) ^ 2 ≤
      1 / T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set m := tdA M π μ s j
  let f : ℕ → (State → ℝ) → Tuple State Action → ℝ := fun _ _ x ↦ sampleAMat M x s j - m
  have hf : ∀ k V, ∑ x, tupleProb M π μ x * f k V x = 0 := by
    intro k V
    simp only [f, mul_sub, Finset.sum_sub_distrib, sum_tupleProb_mul_sampleAMat, ← Finset.sum_mul,
      sum_tupleProb, one_mul]
    exact sub_self _
  have key := sum_pathWeight_mul_sq_sum_eq M π μ 0 0 f hf T
  have hvar : ∑ x, tupleProb M π μ x * (sampleAMat M x s j - m) ^ 2 ≤ 1 := by
    calc ∑ x, tupleProb M π μ x * (sampleAMat M x s j - m) ^ 2
        ≤ ∑ x, tupleProb M π μ x * (sampleAMat M x s j) ^ 2 := by
          have e : ∑ x, tupleProb M π μ x * (sampleAMat M x s j - m) ^ 2 =
              ∑ x, tupleProb M π μ x * (sampleAMat M x s j) ^ 2 - m ^ 2 := by
            have h1 := sum_tupleProb_mul_sampleAMat M π μ s j
            have h2 := sum_tupleProb M π μ
            have : ∀ x : Tuple State Action, tupleProb M π μ x * (sampleAMat M x s j - m) ^ 2 =
                tupleProb M π μ x * (sampleAMat M x s j) ^ 2 -
                  2 * m * (tupleProb M π μ x * sampleAMat M x s j) + m ^ 2 * tupleProb M π μ x := by
              intro x; ring
            simp_rw [this]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              h1, h2]
            ring
          rw [e]; nlinarith [sq_nonneg m]
      _ ≤ ∑ x, tupleProb M π μ x * 1 := by
          refine Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)
          have := abs_sampleAMat_apply_le M x s j
          rw [← sq_abs]; nlinarith [abs_nonneg (sampleAMat M x s j)]
      _ = 1 := by simp [sum_tupleProb]
  have hpt : ∀ ω : Fin T → Tuple State Action, aBar M ω s j - m =
      (T : ℝ)⁻¹ * ∑ k : Fin T, f k (tdIter M 0 0 ω k) (ω k) := by
    intro ω
    simp only [f, aBar, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hpt, mul_pow, ← mul_assoc, mul_comm _ (((T : ℝ)⁻¹) ^ 2), mul_assoc, ← Finset.mul_sum,
    key]
  have hle : ∑ k ∈ range T, ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
      ∑ x, tupleProb M π μ x * f k (tdIter M 0 0 ω k) x ^ 2 ≤ T := by
    calc _ ≤ ∑ k ∈ range T, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          calc _ ≤ ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω * 1 :=
                Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left hvar (pathWeight_nonneg M π μ ω)
            _ = 1 := by simp [sum_pathWeight]
      _ = T := by simp
  calc ((T : ℝ)⁻¹) ^ 2 * _ ≤ ((T : ℝ)⁻¹) ^ 2 * T := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / T := by field_simp

/-- **C3(a).** `P(|Ā_T(s,j) − A(s,j)| > ε) ≤ 1/(ε²T)` for `T ≥ 1`, `ε > 0`. -/
theorem pathProb_abs_aBar_sub_gt_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    (s j : State) {ε : ℝ} (hε : 0 < ε) :
    pathProb M π μ T {ω | ε < |aBar M ω s j - tdA M π μ s j|} ≤ 1 / (ε ^ 2 * T) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  refine (pathProb_lt_abs_le M π μ T (fun ω ↦ aBar M ω s j - tdA M π μ s j) hε).trans ?_
  rw [div_le_div_iff₀ (pow_pos hε 2) (mul_pos (pow_pos hε 2) hT0)]
  have h := sum_pathWeight_mul_sq_aBar_sub_le M π μ hT s j
  rw [le_div_iff₀ hT0] at h
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ε)]

/-- All entries at once: `P(∃ s j, |Ā_T(s,j) − A(s,j)| > ε) ≤ S²/(ε²T)`. -/
theorem pathProb_exists_abs_aBar_sub_gt_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    pathProb M π μ T {ω | ∃ s j, ε < |aBar M ω s j - tdA M π μ s j|} ≤
      (Fintype.card State : ℝ) ^ 2 / (ε ^ 2 * T) := by
  have hset : {ω : Fin T → Tuple State Action | ∃ s j, ε < |aBar M ω s j - tdA M π μ s j|} =
      {ω | ∃ p : State × State, ω ∈ {ω : Fin T → Tuple State Action |
        ε < |aBar M ω p.1 p.2 - tdA M π μ p.1 p.2|}} := by
    ext ω; simp
  rw [hset]
  refine (pathProb_exists_le M π μ T _).trans ?_
  calc ∑ p : State × State, pathProb M π μ T {ω | ε < |aBar M ω p.1 p.2 - tdA M π μ p.1 p.2|}
      ≤ ∑ _p : State × State, 1 / (ε ^ 2 * T) :=
        Finset.sum_le_sum fun p _ ↦ pathProb_abs_aBar_sub_gt_le M π μ hT p.1 p.2 hε
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast; ring

/-! ## C3(b): the oracle `Γ̂` (with `V^π` in place of `V̄_T`) estimates `Γ_true` -/

/-- The weight `w_{k+1,T} = 2(k+1)/(T(T+1))` as a function of `k : ℕ`. -/
noncomputable def pluginWeightNat (T k : ℕ) : ℝ := 2 * ((k : ℝ) + 1) / ((T : ℝ) * (T + 1))

/-- The oracle diagonal entry `∑_t w_{t,T} 1[s_t = s] ξ_t²` with `ξ_t = V^π(s_t) − r_t − γV^π(s'_t)`,
i.e. `Γ̂_T(s,s)` with `V̄_T` replaced by `V^π` (`gammaHatAt_valueFixedPoint_diag`). -/
noncomputable def oracleGammaHat (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) : ℝ :=
  ∑ t, pluginWeight T t * (if s = (ω t).1 then tdNoise M π (ω t) ^ 2 else 0)

/-- Link to the printed formula (critic R3): the diagonal of `Γ̂` evaluated at `V^π` is
`oracleGammaHat`. -/
theorem gammaHatAt_valueFixedPoint_diag (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) :
    gammaHatAt M (M.valueFixedPoint π) ω s s = oracleGammaHat M π ω s := by
  rw [gammaHatAt_apply, if_pos rfl, oracleGammaHat]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases h : (ω t).1 = s
  · subst h; simp only [if_true, tdNoise]; ring
  · simp [h, Ne.symm h]

/-- `E[1[s_t = s] ξ_t²] = Γ_true(s)`. -/
theorem sum_tupleProb_mul_oracleTerm (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s : State) :
    ∑ x : Tuple State Action, tupleProb M π μ x *
      (if s = x.1 then tdNoise M π x ^ 2 else 0) = trueGamma M π μ s := by
  rw [trueGamma_eq, ← sum_tupleProb_mul_ite_zero M π μ s fun a s' ↦ tdNoise M π (s, a, s') ^ 2]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : s = x.1
  · subst h; rfl
  · simp [h]

theorem oracleTerm_mem (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (x : Tuple State Action) :
    0 ≤ (if s = x.1 then tdNoise M π x ^ 2 else 0) ∧
      (if s = x.1 then tdNoise M π x ^ 2 else 0) ≤ tdNoiseBound M π ^ 2 := by
  have hB := tdNoiseBound_pos M π
  have h := abs_tdNoise_le M π x
  split_ifs
  · refine ⟨sq_nonneg _, ?_⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  · exact ⟨le_refl 0, by positivity⟩

theorem trueGamma_mem (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) :
    0 ≤ trueGamma M π μ s ∧ trueGamma M π μ s ≤ tdNoiseBound M π ^ 2 := by
  rw [← sum_tupleProb_mul_oracleTerm M π μ s]
  constructor
  · exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg (tupleProb_nonneg M π μ x) (oracleTerm_mem M π s x).1
  · calc _ ≤ ∑ x : Tuple State Action, tupleProb M π μ x * tdNoiseBound M π ^ 2 :=
          Finset.sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left (oracleTerm_mem M π s x).2 (tupleProb_nonneg M π μ x)
      _ = _ := by rw [← Finset.sum_mul, sum_tupleProb, one_mul]

/-- `∑_{k<T} w_{k+1,T}² ≤ 2/T`. -/
theorem sum_sq_pluginWeightNat_le {T : ℕ} (hT : 1 ≤ T) :
    ∑ k ∈ range T, pluginWeightNat T k ^ 2 ≤ 2 / T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : ∑ k ∈ range T, pluginWeightNat T k = 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ pluginWeightNat T k), ← sum_pluginWeight hT]
    exact Finset.sum_congr rfl fun k _ ↦ (pluginWeight_eq T k).symm
  have hle : ∀ k ∈ range T, pluginWeightNat T k ≤ 2 / T := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ T := by
      have := Finset.mem_range.1 hk; exact_mod_cast this
    rw [pluginWeightNat, div_le_div_iff₀ (by positivity) hT0]
    nlinarith
  have hnn : ∀ k ∈ range T, 0 ≤ pluginWeightNat T k := fun k _ ↦ by
    unfold pluginWeightNat; positivity
  calc ∑ k ∈ range T, pluginWeightNat T k ^ 2
      ≤ ∑ k ∈ range T, 2 / T * pluginWeightNat T k :=
        Finset.sum_le_sum fun k hk ↦ by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hle k hk) (hnn k hk)
    _ = 2 / T := by rw [← Finset.mul_sum, hsum, mul_one]

/-- `E(Γ̂^{or}_T(s) − Γ_true(s))² ≤ 2B⁴/T`, `B = tdNoiseBound`. -/
theorem sum_pathWeight_mul_sq_oracleGammaHat_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (oracleGammaHat M π ω s - trueGamma M π μ s) ^ 2 ≤ 2 * tdNoiseBound M π ^ 4 / T := by
  set m := trueGamma M π μ s with hm
  set B := tdNoiseBound M π with hBdef
  let g : Tuple State Action → ℝ := fun x ↦ if s = x.1 then tdNoise M π x ^ 2 else 0
  let f : ℕ → (State → ℝ) → Tuple State Action → ℝ := fun k _ x ↦ pluginWeightNat T k * (g x - m)
  have hf : ∀ k V, ∑ x, tupleProb M π μ x * f k V x = 0 := by
    intro k V
    have e : ∀ x, tupleProb M π μ x * f k V x =
        pluginWeightNat T k * (tupleProb M π μ x * g x - m * tupleProb M π μ x) := by
      intro x; simp only [f]; ring
    simp_rw [e]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_tupleProb]
    simp only [g]
    rw [sum_tupleProb_mul_oracleTerm M π μ s]
    ring
  have key := sum_pathWeight_mul_sq_sum_eq M π μ 0 0 f hf T
  have hw : ∀ k : Fin T, pluginWeight T k = pluginWeightNat T k := fun k ↦ pluginWeight_eq T k
  have hw1 : ∑ k : Fin T, pluginWeightNat T k = 1 := by
    rw [← sum_pluginWeight hT]; exact Finset.sum_congr rfl fun k _ ↦ (hw k).symm
  have hpt : ∀ ω : Fin T → Tuple State Action, oracleGammaHat M π ω s - m =
      ∑ k : Fin T, f k (tdIter M 0 0 ω k) (ω k) := by
    intro ω
    simp only [f, g, oracleGammaHat, hw, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1,
      one_mul]
  simp_rw [hpt]
  rw [key]
  have hgm : ∀ x, (g x - m) ^ 2 ≤ B ^ 4 := by
    intro x
    have h1 := oracleTerm_mem M π s x
    have h2 := trueGamma_mem M π μ s
    have habs : |g x - m| ≤ B ^ 2 := by
      rw [abs_le]; constructor <;> simp only [g] <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc (g x - m) ^ 2 = |g x - m| ^ 2 := (sq_abs _).symm
      _ ≤ (B ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = B ^ 4 := by ring
  calc ∑ k ∈ range T, ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * f k (tdIter M 0 0 ω k) x ^ 2
      ≤ ∑ k ∈ range T, pluginWeightNat T k ^ 2 * B ^ 4 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hx : ∀ V : State → ℝ, ∑ x, tupleProb M π μ x * f k V x ^ 2 ≤
            pluginWeightNat T k ^ 2 * B ^ 4 := by
          intro V
          calc ∑ x, tupleProb M π μ x * f k V x ^ 2
              ≤ ∑ x, tupleProb M π μ x * (pluginWeightNat T k ^ 2 * B ^ 4) := by
                refine Finset.sum_le_sum fun x _ ↦
                  mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)
                simp only [f, mul_pow]
                exact mul_le_mul_of_nonneg_left (hgm x) (sq_nonneg _)
            _ = _ := by rw [← Finset.sum_mul, sum_tupleProb, one_mul]
        calc _ ≤ ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
              (pluginWeightNat T k ^ 2 * B ^ 4) :=
              Finset.sum_le_sum fun ω _ ↦
                mul_le_mul_of_nonneg_left (hx (tdIter M 0 0 ω k)) (pathWeight_nonneg M π μ ω)
          _ = _ := by rw [← Finset.sum_mul, sum_pathWeight, one_mul]
    _ ≤ 2 / T * B ^ 4 := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (sum_sq_pluginWeightNat_le hT) (by positivity)
    _ = 2 * B ^ 4 / T := by ring

/-- **C3(b).** `P(|Γ̂^{or}_T(s) − Γ_true(s)| > ε) ≤ 2B⁴/(ε²T)` for `T ≥ 1`, `ε > 0`. -/
theorem pathProb_abs_oracleGammaHat_sub_gt_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    (s : State) {ε : ℝ} (hε : 0 < ε) :
    pathProb M π μ T {ω | ε < |oracleGammaHat M π ω s - trueGamma M π μ s|} ≤
      2 * tdNoiseBound M π ^ 4 / (ε ^ 2 * T) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  refine (pathProb_lt_abs_le M π μ T (fun ω ↦ oracleGammaHat M π ω s - trueGamma M π μ s)
    hε).trans ?_
  have h := sum_pathWeight_mul_sq_oracleGammaHat_sub_le M π μ hT s
  rw [div_le_div_iff₀ (pow_pos hε 2) (mul_pos (pow_pos hε 2) hT0)]
  rw [le_div_iff₀ hT0] at h
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ε)]

end StatisticalRL.Ch7Rest.TDInference
