import Formalization.ModelFree.QLearningPinskerBinaryCurvature

/-! Finite zero-safe log-sum with KL oriented from first argument to second. -/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Zero-safe atomic KL summand. A zero numerator contributes zero even when
the reference mass is zero; positive numerators require positive reference
mass through the support premise of the consuming theorems. -/
noncomputable def qFiniteKLTerm (a b : ℝ) : ℝ :=
  if a = 0 then 0 else a * Real.log (a / b)

variable {Ω : Type*} [Fintype Ω]

/-- Finite KL expression with explicit zero-numerator convention. -/
noncomputable def qFiniteKLOn (s : Finset Ω) (a b : Ω → ℝ) : ℝ :=
  ∑ i ∈ s, qFiniteKLTerm (a i) (b i)

/-- A normalized finite KL expression is nonnegative, including zero atoms.
Only support inclusion `a i>0 → b i>0` is required. -/
theorem qFiniteKLOn_nonneg {s : Finset Ω} (a b : Ω → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hsumA : (∑ i ∈ s, a i) = 1) (hsumB : (∑ i ∈ s, b i) = 1)
    (hsupport : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    0 ≤ qFiniteKLOn s a b := by
  have hterm (i : Ω) (hi : i ∈ s) :
      a i - b i ≤ qFiniteKLTerm (a i) (b i) := by
    by_cases hzero : a i = 0
    · rw [qFiniteKLTerm, if_pos hzero]
      simpa [hzero] using (hb i hi)
    · have haPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hzero)
      have hbPos : 0 < b i :=
        lt_of_le_of_ne (hb i hi) (Ne.symm (hsupport i hi hzero))
      have hlog := Real.log_le_sub_one_of_pos (div_pos hbPos haPos)
      have hlogdiv : Real.log (b i / a i) = Real.log (b i) - Real.log (a i) :=
        Real.log_div (ne_of_gt hbPos) (ne_of_gt haPos)
      have hlogdiv' : Real.log (a i / b i) = Real.log (a i) - Real.log (b i) :=
        Real.log_div (ne_of_gt haPos) (ne_of_gt hbPos)
      have hmul := mul_le_mul_of_nonneg_left hlog haPos.le
      have hmul' : a i * (Real.log (b i) - Real.log (a i)) ≤ b i - a i := by
        rw [hlogdiv] at hmul
        calc
          a i * (Real.log (b i) - Real.log (a i)) ≤
              a i * (b i / a i - 1) := hmul
          _ = b i - a i := by field_simp [ne_of_gt haPos]
      rw [qFiniteKLTerm, if_neg hzero, hlogdiv']
      nlinarith [hmul']
  unfold qFiniteKLOn
  calc
    0 = (∑ i ∈ s, a i) - (∑ i ∈ s, b i) := by rw [hsumA, hsumB]; ring
    _ ≤ ∑ i ∈ s, qFiniteKLTerm (a i) (b i) := by
      calc
        _ = ∑ i ∈ s, (a i - b i) := by rw [Finset.sum_sub_distrib]
        _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ hterm i hi)

/-- Zero-safe finite log-sum inequality. The numerator support may be a
strict subset of the denominator support. Empty cells and all-zero numerator
cells contribute zero; positive numerator mass implies positive denominator
mass, so no logarithm is evaluated through a division by a zero baseline. -/
theorem qFiniteKL_logSum {s : Finset Ω} (a b : Ω → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hsupport : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      qFiniteKLOn s a b := by
  let A : ℝ := ∑ i ∈ s, a i
  let B : ℝ := ∑ i ∈ s, b i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi ↦ ha i hi)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi ↦ hb i hi)
  by_cases hAzero : A = 0
  · have hsumA0 : (∑ i ∈ s, a i) = 0 := by simpa [A] using hAzero
    have haZero : ∀ i ∈ s, a i = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ ha i hi)).mp hsumA0
    have hKLzero : qFiniteKLOn s a b = 0 := by
      unfold qFiniteKLOn
      apply Finset.sum_eq_zero
      intro i hi
      simp [qFiniteKLTerm, haZero i hi]
    change A * Real.log (A / B) ≤ qFiniteKLOn s a b
    rw [hAzero, hKLzero]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hex : ∃ i ∈ s, 0 < a i := by
      by_contra hn
      have hz : ∀ i ∈ s, a i = 0 := by
        intro i hi
        have hn' : ¬ 0 < a i := by
          intro hp
          exact hn ⟨i, hi, hp⟩
        exact le_antisymm (le_of_not_gt hn') (ha i hi)
      have hsum : A = 0 := by simp [A, Finset.sum_eq_zero hz]
      exact hAzero hsum
    obtain ⟨i₀, hi₀, hai₀⟩ := hex
    have hbi₀ : 0 < b i₀ :=
      lt_of_le_of_ne (hb i₀ hi₀) (Ne.symm (hsupport i₀ hi₀ (ne_of_gt hai₀)))
    have hBle : b i₀ ≤ B := Finset.single_le_sum (fun i hi ↦ hb i hi) hi₀
    have hBpos : 0 < B := lt_of_lt_of_le hbi₀ hBle
    let w : Ω → ℝ := fun i ↦ a i / A
    let v : Ω → ℝ := fun i ↦ b i / B
    have hsumW : (∑ i ∈ s, w i) = 1 := by
      dsimp [w]
      calc
        _ = ∑ i ∈ s, a i * A⁻¹ := by simp [div_eq_mul_inv]
        _ = (∑ i ∈ s, a i) * A⁻¹ := by rw [← Finset.sum_mul]
        _ = 1 := by simpa [A] using div_self (ne_of_gt hApos)
    have hsumV : (∑ i ∈ s, v i) = 1 := by
      dsimp [v]
      calc
        _ = ∑ i ∈ s, b i * B⁻¹ := by simp [div_eq_mul_inv]
        _ = (∑ i ∈ s, b i) * B⁻¹ := by rw [← Finset.sum_mul]
        _ = 1 := by simpa [B] using div_self (ne_of_gt hBpos)
    have hw : ∀ i ∈ s, 0 ≤ w i := fun i hi ↦ div_nonneg (ha i hi) hApos.le
    have hv : ∀ i ∈ s, 0 ≤ v i := fun i hi ↦ div_nonneg (hb i hi) hBpos.le
    have hwsupport : ∀ i ∈ s, w i ≠ 0 → v i ≠ 0 := by
      intro i hi hwi
      have hai : a i ≠ 0 := by
        intro hz
        apply hwi
        simp [w, hz]
      have hbi := hsupport i hi hai
      intro hvi
      have hbPos : 0 < b i := lt_of_le_of_ne (hb i hi) (Ne.symm hbi)
      exact (ne_of_gt (div_pos hbPos hBpos)) hvi
    have hnorm := qFiniteKLOn_nonneg (s := s) w v hw hv hsumW hsumV hwsupport
    have hterm (i : Ω) (hi : i ∈ s) :
        qFiniteKLTerm (a i) (b i) =
          A * qFiniteKLTerm (w i) (v i) + a i * Real.log (A / B) := by
      by_cases hai : a i = 0
      · simp [qFiniteKLTerm, hai, w, A]
      · have haiPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hai)
        have hbiPos : 0 < b i :=
          lt_of_le_of_ne (hb i hi) (Ne.symm (hsupport i hi hai))
        have hwiPos : 0 < w i := div_pos haiPos hApos
        have hviPos : 0 < v i := div_pos hbiPos hBpos
        have hratio : w i / v i = (a i / b i) / (A / B) := by
          dsimp [w, v]
          field_simp [ne_of_gt haiPos, ne_of_gt hbiPos, ne_of_gt hApos, ne_of_gt hBpos]
        have hlog : Real.log (w i / v i) =
            Real.log (a i / b i) - Real.log (A / B) := by
          rw [hratio, Real.log_div (div_ne_zero (ne_of_gt haiPos) (ne_of_gt hbiPos))
            (div_ne_zero (ne_of_gt hApos) (ne_of_gt hBpos))]
        have hleft : qFiniteKLTerm (a i) (b i) = a i * Real.log (a i / b i) := by
          simp [qFiniteKLTerm, hai]
        have hright : qFiniteKLTerm (w i) (v i) = w i * Real.log (w i / v i) := by
          simp [qFiniteKLTerm, (ne_of_gt hwiPos)]
        rw [hleft, hright, hlog]
        dsimp [w, v]
        field_simp [ne_of_gt haiPos, ne_of_gt hbiPos, ne_of_gt hApos, ne_of_gt hBpos]
        ring
    have hsumIdentity : qFiniteKLOn s a b =
        A * qFiniteKLOn s w v + A * Real.log (A / B) := by
      unfold qFiniteKLOn
      calc
        _ = ∑ i ∈ s, (A * qFiniteKLTerm (w i) (v i) +
            a i * Real.log (A / B)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i hi
        _ = (∑ i ∈ s, A * qFiniteKLTerm (w i) (v i)) +
              (∑ i ∈ s, a i * Real.log (A / B)) := by
          rw [Finset.sum_add_distrib]
        _ = A * (∑ i ∈ s, qFiniteKLTerm (w i) (v i)) +
              (∑ i ∈ s, a i) * Real.log (A / B) := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by simp [qFiniteKLOn, A]
    change A * Real.log (A / B) ≤ qFiniteKLOn s a b
    rw [hsumIdentity]
    nlinarith [mul_nonneg hApos.le hnorm]

end StatisticalRL.QLearning
