import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.QuadraticDiscriminant
import Formalization.Ch7Rest.VPOElementary712

/-!
# Corrected Theorem 7.12: elliptical potential (L10, L11)

Gram matrices `V_n = 4 I + ∑_{j<n} v_j v_jᵀ` on `Fin d → ℝ`, the inverse norm
`‖a‖²_{V⁻¹} = a ⬝ (V⁻¹ a)`, the Cauchy–Schwarz inequality `(a ⬝ w)² ≤ ‖a‖²_{V⁻¹} · wᵀ V w`,
and the elliptical potential bound `∑_{n<N} ‖v_n‖²_{V_n⁻¹} ≤ 2 d log(1 + N/d)` for
`‖v_n‖² ≤ 4` (determinant lemma `Matrix.det_add_replicateCol_mul_replicateRow`, and
`log det ≤ d log(tr/d)` through the eigenvalues).
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Matrix Real

variable {d : ℕ}

/-- Cauchy–Schwarz from a nonnegative quadratic. -/
theorem sq_le_of_quad_nonneg {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ B * (t * t) + (-2 * C) * t + A) :
    C ^ 2 ≤ A * B := by
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

theorem dot_self_nonneg' (a : Fin d → ℝ) : 0 ≤ a ⬝ᵥ a :=
  sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- Cauchy–Schwarz for `⬝ᵥ`. -/
theorem dot_sq_le (a b : Fin d → ℝ) : (a ⬝ᵥ b) ^ 2 ≤ (b ⬝ᵥ b) * (a ⬝ᵥ a) := by
  refine sq_le_of_quad_nonneg fun t ↦ ?_
  have h := dot_self_nonneg' (b - t • a)
  have : (b - t • a) ⬝ᵥ (b - t • a) = (a ⬝ᵥ a) * (t * t) + (-2 * (a ⬝ᵥ b)) * t + b ⬝ᵥ b := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm b a]
    ring
  linarith

/-- Gram matrix `V_n = 4 I + ∑_{j<n} v_j v_jᵀ`. -/
noncomputable def gramMat (v : ℕ → Fin d → ℝ) (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (4 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) + ∑ j ∈ range n, vecMulVec (v j) (v j)

/-- `‖a‖²_{V⁻¹} = a ⬝ (V⁻¹ a)`. -/
noncomputable def invNormSq (V : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) : ℝ :=
  a ⬝ᵥ (V⁻¹ *ᵥ a)

variable (v : ℕ → Fin d → ℝ)

theorem vecMulVec_mulVec' (u w : Fin d → ℝ) : vecMulVec u u *ᵥ w = (u ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  refine sum_congr rfl fun j _ ↦ by ring

theorem gramMat_mulVec (n : ℕ) (w : Fin d → ℝ) :
    gramMat v n *ᵥ w = (4 : ℝ) • w + ∑ j ∈ range n, (v j ⬝ᵥ w) • v j := by
  unfold gramMat
  rw [add_mulVec, smul_mulVec, one_mulVec, sum_mulVec]
  congr 1
  exact sum_congr rfl fun j _ ↦ vecMulVec_mulVec' (v j) w

/-- Bilinear form of the Gram matrix. -/
theorem dot_gramMat_mulVec (n : ℕ) (x y : Fin d → ℝ) :
    x ⬝ᵥ (gramMat v n *ᵥ y) = 4 * (x ⬝ᵥ y) + ∑ j ∈ range n, (v j ⬝ᵥ x) * (v j ⬝ᵥ y) := by
  rw [gramMat_mulVec, dotProduct_add, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (v j), mul_comm]

theorem dot_gramMat_mulVec_comm (n : ℕ) (x y : Fin d → ℝ) :
    x ⬝ᵥ (gramMat v n *ᵥ y) = y ⬝ᵥ (gramMat v n *ᵥ x) := by
  rw [dot_gramMat_mulVec, dot_gramMat_mulVec, dotProduct_comm x y]
  congr 1
  exact sum_congr rfl fun j _ ↦ mul_comm _ _

/-- `wᵀ V_n w = 4 ‖w‖² + ∑_{j<n} (v_j ⬝ w)²`. -/
theorem quad_gramMat (n : ℕ) (w : Fin d → ℝ) :
    w ⬝ᵥ (gramMat v n *ᵥ w) = 4 * (w ⬝ᵥ w) + ∑ j ∈ range n, (v j ⬝ᵥ w) ^ 2 := by
  rw [dot_gramMat_mulVec]
  congr 1
  exact sum_congr rfl fun j _ ↦ (sq _).symm

theorem quad_gramMat_ge (n : ℕ) (w : Fin d → ℝ) :
    4 * (w ⬝ᵥ w) ≤ w ⬝ᵥ (gramMat v n *ᵥ w) := by
  rw [quad_gramMat]
  linarith [sum_nonneg fun j (_ : j ∈ range n) ↦ sq_nonneg (v j ⬝ᵥ w)]

theorem gramMat_det_ne_zero (n : ℕ) : (gramMat v n).det ≠ 0 := by
  intro h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 h
  have h1 := quad_gramMat_ge v n w
  rw [hw, dotProduct_zero] at h1
  have h2 : w ⬝ᵥ w = 0 := le_antisymm (by linarith) (dot_self_nonneg' w)
  exact hw0 (dotProduct_self_eq_zero.1 h2)

theorem gramMat_mulVec_inv (n : ℕ) (a : Fin d → ℝ) :
    gramMat v n *ᵥ ((gramMat v n)⁻¹ *ᵥ a) = a := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gramMat_det_ne_zero v n)),
    one_mulVec]

theorem invNormSq_eq (n : ℕ) (a : Fin d → ℝ) :
    invNormSq (gramMat v n) a =
      ((gramMat v n)⁻¹ *ᵥ a) ⬝ᵥ (gramMat v n *ᵥ ((gramMat v n)⁻¹ *ᵥ a)) := by
  rw [gramMat_mulVec_inv, dotProduct_comm]; rfl

theorem invNormSq_nonneg (n : ℕ) (a : Fin d → ℝ) : 0 ≤ invNormSq (gramMat v n) a := by
  rw [invNormSq_eq]
  exact le_trans (mul_nonneg (by norm_num) (dot_self_nonneg' _)) (quad_gramMat_ge v n _)

/-- L10: `(a ⬝ w)² ≤ ‖a‖²_{V⁻¹} · wᵀ V w`. -/
theorem dot_sq_le_invNormSq_mul (n : ℕ) (a w : Fin d → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤ invNormSq (gramMat v n) a * (w ⬝ᵥ (gramMat v n *ᵥ w)) := by
  set V := gramMat v n
  set b := V⁻¹ *ᵥ a
  have hab : a ⬝ᵥ w = b ⬝ᵥ (V *ᵥ w) := by
    rw [← gramMat_mulVec_inv v n a, dotProduct_comm]
    exact dot_gramMat_mulVec_comm v n w b
  rw [hab, invNormSq_eq]
  refine sq_le_of_quad_nonneg fun t ↦ ?_
  have h := le_trans (mul_nonneg (by norm_num) (dot_self_nonneg' _)) (quad_gramMat_ge v n (b - t • w))
  have hexp : (b - t • w) ⬝ᵥ (V *ᵥ (b - t • w)) =
      (w ⬝ᵥ (V *ᵥ w)) * (t * t) + (-2 * (b ⬝ᵥ (V *ᵥ w))) * t + b ⬝ᵥ (V *ᵥ b) := by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [dot_gramMat_mulVec_comm v n w b]
    ring
  linarith

/-- `‖a‖²_{V⁻¹} ≤ ‖a‖²/4`. -/
theorem invNormSq_le (n : ℕ) (a : Fin d → ℝ) : invNormSq (gramMat v n) a ≤ (a ⬝ᵥ a) / 4 := by
  set V := gramMat v n
  set b := V⁻¹ *ᵥ a
  set N := invNormSq V a
  have hN : N = a ⬝ᵥ b := rfl
  have hNq : N = b ⬝ᵥ (V *ᵥ b) := invNormSq_eq v n a
  have h4 : 4 * (b ⬝ᵥ b) ≤ N := hNq ▸ quad_gramMat_ge v n b
  have hcs := dot_sq_le a b
  rw [← hN] at hcs
  have ha := dot_self_nonneg' a
  have hb := dot_self_nonneg' b
  rcases le_or_gt N 0 with hN0 | hN0
  · linarith
  · have : N * N ≤ (a ⬝ᵥ a) * (N / 4) := by nlinarith
    have : N ≤ (a ⬝ᵥ a) / 4 := by nlinarith
    exact this

/-- Determinant update `det V_{n+1} = det V_n (1 + ‖v_n‖²_{V_n⁻¹})`. -/
theorem det_gramMat_succ (n : ℕ) :
    (gramMat v (n + 1)).det = (gramMat v n).det * (1 + invNormSq (gramMat v n) (v n)) := by
  have hV : gramMat v (n + 1) = gramMat v n + vecMulVec (v n) (v n) := by
    unfold gramMat; rw [sum_range_succ, add_assoc]
  rw [hV, vecMulVec_eq (Fin 1), det_add_mul _ _
    (isUnit_iff_ne_zero.2 (gramMat_det_ne_zero v n))]
  congr 1
  rw [Matrix.mul_assoc, ← replicateCol_mulVec, det_fin_one, add_apply, one_apply_eq,
    replicateRow_mul_replicateCol_apply]
  rfl

theorem det_gramMat_zero : (gramMat v 0).det = 4 ^ d := by
  simp [gramMat]

theorem det_gramMat_eq_prod (N : ℕ) :
    (gramMat v N).det = 4 ^ d * ∏ n ∈ range N, (1 + invNormSq (gramMat v n) (v n)) := by
  induction N with
  | zero => simp [det_gramMat_zero]
  | succ N ih => rw [det_gramMat_succ, ih, prod_range_succ, mul_assoc]

theorem trace_gramMat (N : ℕ) : (gramMat v N).trace = 4 * d + ∑ j ∈ range N, v j ⬝ᵥ v j := by
  unfold gramMat
  rw [trace_add, trace_smul, trace_one, trace_sum]
  simp [trace_vecMulVec]

theorem gramMat_isHermitian (N : ℕ) : (gramMat v N).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  unfold gramMat
  rw [transpose_add, transpose_smul, transpose_one, transpose_sum]
  simp [transpose_vecMulVec]

theorem gramMat_posSemidef (N : ℕ) : (gramMat v N).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨gramMat_isHermitian v N, fun x ↦ ?_⟩
  simp only [star_trivial]
  exact le_trans (mul_nonneg (by norm_num) (dot_self_nonneg' _)) (quad_gramMat_ge v N x)

/-- `log det A ≤ d log(tr A / d)` for a positive semidefinite `A` with `det A > 0`. -/
theorem log_det_le_of_posSemidef (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    (hdet : 0 < A.det) : log A.det ≤ d * log (A.trace / d) := by
  have hdetE := hA.1.det_eq_prod_eigenvalues
  have htrE := hA.1.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdetE htrE
  set ev := hA.1.eigenvalues
  have hev0 : ∀ i, 0 ≤ ev i := hA.eigenvalues_nonneg
  have hevpos : ∀ i, 0 < ev i := by
    intro i
    rcases (hev0 i).eq_or_lt with h | h
    · exfalso
      have : A.det = 0 := by rw [hdetE]; exact prod_eq_zero (mem_univ i) h.symm
      linarith
    · exact h
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hne : (univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, mem_univ _⟩
  have htr : 0 < A.trace := by rw [htrE]; exact sum_pos (fun i _ ↦ hevpos i) hne
  set μ := A.trace / d
  have hμ : 0 < μ := div_pos htr hdR
  rw [hdetE, log_prod (fun i _ ↦ (hevpos i).ne')]
  have hterm : ∀ i, log (ev i) ≤ ev i / μ - 1 + log μ := by
    intro i
    have := log_le_sub_one_of_pos (div_pos (hevpos i) hμ)
    rw [log_div (hevpos i).ne' hμ.ne'] at this
    linarith
  calc ∑ i, log (ev i) ≤ ∑ i, (ev i / μ - 1 + log μ) := sum_le_sum fun i _ ↦ hterm i
    _ = (∑ i, ev i) / μ - d + d * log μ := by
        rw [sum_add_distrib, sum_sub_distrib, ← sum_div]; simp
    _ = d * log μ := by
        rw [← htrE]
        have : A.trace / μ = d := by
          simp only [μ]; field_simp
        rw [this]; ring

/-- L11 (elliptical potential): for `‖v_j‖² ≤ 4`, `∑_{n<N} ‖v_n‖²_{V_n⁻¹} ≤ 2 d log(1 + N/d)`. -/
theorem elliptical_potential (hd : 0 < d) (hv : ∀ j, v j ⬝ᵥ v j ≤ 4) (N : ℕ) :
    ∑ n ∈ range N, invNormSq (gramMat v n) (v n) ≤ 2 * d * log (1 + N / d) := by
  set X := fun n ↦ invNormSq (gramMat v n) (v n)
  have hX0 : ∀ n, 0 ≤ X n := fun n ↦ invNormSq_nonneg v n (v n)
  have hX1 : ∀ n, X n ≤ 1 := fun n ↦ le_trans (invNormSq_le v n (v n)) (by linarith [hv n])
  have hdet := det_gramMat_eq_prod v N
  have hprod : 0 < ∏ n ∈ range N, (1 + X n) := prod_pos fun n _ ↦ by linarith [hX0 n]
  have h4 : (0 : ℝ) < 4 ^ d := by positivity
  have hdetpos : 0 < (gramMat v N).det := by rw [hdet]; exact mul_pos h4 hprod
  have hlogdet : log (gramMat v N).det = d * log 4 + ∑ n ∈ range N, log (1 + X n) := by
    rw [hdet, log_mul h4.ne' hprod.ne', log_pow, log_prod (fun n _ ↦ by linarith [hX0 n])]
  have hle := log_det_le_of_posSemidef hd _ (gramMat_posSemidef v N) hdetpos
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have htr : (gramMat v N).trace / d ≤ 4 * (1 + N / d) := by
    rw [trace_gramMat, div_le_iff₀ hdR]
    have : ∑ j ∈ range N, v j ⬝ᵥ v j ≤ ∑ j ∈ range N, (4 : ℝ) := sum_le_sum fun j _ ↦ hv j
    simp only [sum_const, card_range, nsmul_eq_mul] at this
    have : (4 : ℝ) * (1 + (N : ℝ) / d) * d = 4 * d + 4 * N := by field_simp
    nlinarith
  have htrpos : 0 < (gramMat v N).trace / d := by
    rw [trace_gramMat]
    exact div_pos (by
      linarith [sum_nonneg fun j (_ : j ∈ range N) ↦ dot_self_nonneg' (v j)]) hdR
  have hlogtr : log ((gramMat v N).trace / d) ≤ log 4 + log (1 + N / d) := by
    rw [← log_mul (by norm_num) (by positivity)]
    exact log_le_log htrpos htr
  have hsum : ∑ n ∈ range N, X n ≤ ∑ n ∈ range N, 2 * log (1 + X n) :=
    sum_le_sum fun n _ ↦ le_two_log_one_add (hX0 n) (hX1 n)
  rw [← mul_sum] at hsum
  have := mul_le_mul_of_nonneg_left hlogtr hdR.le
  nlinarith

end StatisticalRL.Ch7Rest.Rlhf
