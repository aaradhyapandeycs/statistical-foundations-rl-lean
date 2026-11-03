import Formalization.ModelFree.QLearningFiniteLogSumPinsker

/-! Two-cell coarsening and the finite half-L1 total-variation identity. -/

open scoped BigOperators
namespace StatisticalRL.QLearning

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Total variation in the half-L1 convention. -/
noncomputable def qFiniteTotalVariation (p q : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

/-- The cell on which the first law has positive excess. -/
noncomputable def qFinitePositiveDifferenceCell (p q : Ω → ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun i ↦ q i ≤ p i)

/-- For normalized finite laws, total variation equals the mass difference on
the positive-excess cell. Equality cases `p i=q i` are assigned to this cell
and contribute zero. -/
theorem qFiniteTotalVariation_eq_positiveCell
    (p q : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : (∑ i, p i) = 1) (hq1 : (∑ i, q i) = 1) :
    qFiniteTotalVariation p q =
      (∑ i ∈ qFinitePositiveDifferenceCell p q, p i) -
        (∑ i ∈ qFinitePositiveDifferenceCell p q, q i) := by
  classical
  let E := qFinitePositiveDifferenceCell p q
  let Ec := Finset.univ \ E
  let d : Ω → ℝ := fun i ↦ p i - q i
  have hdZero : (∑ i, d i) = 0 := by
    simp only [d, Finset.sum_sub_distrib, hp1, hq1]
    ring
  have hdisj : Disjoint E Ec := Finset.disjoint_sdiff
  have hunion : E ∪ Ec = Finset.univ := by
    dsimp [Ec]
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ E)
  have hsplit (f : Ω → ℝ) :
      (∑ i, f i) = (∑ i ∈ E, f i) + (∑ i ∈ Ec, f i) := by
    rw [← Finset.sum_union hdisj, hunion]
  have hpos : (∑ i ∈ E, |d i|) = ∑ i ∈ E, d i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hle : q i ≤ p i := (Finset.mem_filter.mp hi).2
    have hdi : 0 ≤ d i := by dsimp [d]; linarith
    exact abs_of_nonneg hdi
  have hneg : (∑ i ∈ Ec, |d i|) = -∑ i ∈ Ec, d i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hnot : ¬ q i ≤ p i := by
      have hi' : i ∉ E := Finset.mem_sdiff.mp hi |>.2
      simpa [E, qFinitePositiveDifferenceCell] using hi'
    have hdi : d i ≤ 0 := by dsimp [d]; linarith
    rw [abs_of_nonpos hdi]
  have hsumSplit := hsplit (fun i ↦ |d i|)
  have hdSplit := hsplit d
  have htv : (∑ i, |d i|) =
      2 * ((∑ i ∈ E, d i)) := by
    rw [hsumSplit, hpos, hneg] at *
    rw [hdSplit] at hdZero
    linarith
  unfold qFiniteTotalVariation
  rw [htv]
  dsimp [E, d, qFinitePositiveDifferenceCell]
  rw [Finset.sum_sub_distrib]
  ring

/-- If the second law has zero mass on a cell, support inclusion forces the
first law to have zero mass there as well. -/
theorem qFinite_cell_zero_of_support
    (p q : Ω → ℝ) (s : Finset Ω)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hsupport : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0)
    (hqzero : (∑ i ∈ s, q i) = 0) :
    (∑ i ∈ s, p i) = 0 := by
  have hqAtom : ∀ i ∈ s, q i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ hq i hi)).mp hqzero
  have hpAtom : ∀ i ∈ s, p i = 0 := by
    intro i hi
    by_contra hpi
    have hpiPos : 0 < p i := lt_of_le_of_ne (hp i hi) (Ne.symm hpi)
    exact (hsupport i hi (ne_of_gt hpiPos)) (hqAtom i hi)
  exact Finset.sum_eq_zero hpAtom

/-- Aggregate zero-safe KL term is the log-sum expression, once positive
numerator mass guarantees positive denominator mass. -/
theorem qFiniteKLTerm_sum_eq_log
    (p q : Ω → ℝ) (s : Finset Ω)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hsupport : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0) :
    qFiniteKLTerm (∑ i ∈ s, p i) (∑ i ∈ s, q i) =
      (∑ i ∈ s, p i) * Real.log ((∑ i ∈ s, p i) / (∑ i ∈ s, q i)) := by
  classical
  let A := ∑ i ∈ s, p i
  let B := ∑ i ∈ s, q i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi ↦ hp i hi)
  by_cases hAzero : A = 0
  · simp [qFiniteKLTerm, A, hAzero]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hex : ∃ i ∈ s, 0 < p i := by
      by_contra hn
      have hzero : ∀ i ∈ s, p i = 0 := by
        intro i hi
        have hnot : ¬ 0 < p i := by
          intro hpos
          exact hn ⟨i, hi, hpos⟩
        exact le_antisymm (le_of_not_gt hnot) (hp i hi)
      exact hAzero (by simp [A, Finset.sum_eq_zero hzero])
    obtain ⟨i₀, hi₀, hpi₀⟩ := hex
    have hqi₀ : 0 < q i₀ :=
      lt_of_le_of_ne (hq i₀ hi₀) (Ne.symm (hsupport i₀ hi₀ (ne_of_gt hpi₀)))
    have hBpos : 0 < B := lt_of_lt_of_le hqi₀
      (Finset.single_le_sum (fun i hi ↦ hq i hi) hi₀)
    simp [qFiniteKLTerm, A, B, ne_of_gt hApos]

/-- Zero-safe binary coarsening: grouping a finite pair into a cell and its
complement cannot increase KL. The first argument is the numerator law. -/
theorem qFiniteKL_binaryCoarsen
    (p q : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : (∑ i, p i) = 1) (hq1 : (∑ i, q i) = 1)
    (hsupport : ∀ i, p i ≠ 0 → q i ≠ 0) (E : Finset Ω) :
    qFiniteKLTerm (∑ i ∈ E, p i) (∑ i ∈ E, q i) +
      qFiniteKLTerm (∑ i ∈ Finset.univ \ E, p i)
        (∑ i ∈ Finset.univ \ E, q i) ≤
      qFiniteKLOn Finset.univ p q := by
  classical
  let Ec := Finset.univ \ E
  have hE := qFiniteKL_logSum (s := E) p q
    (fun i hi ↦ hp i) (fun i hi ↦ hq i) (fun i hi hpi ↦ hsupport i hpi)
  have hEc := qFiniteKL_logSum (s := Ec) p q
    (fun i hi ↦ hp i) (fun i hi ↦ hq i) (fun i hi hpi ↦ hsupport i hpi)
  rw [← qFiniteKLTerm_sum_eq_log p q E (fun i hi ↦ hp i) (fun i hi ↦ hq i)
        (fun i hi hpi ↦ hsupport i hpi)] at hE
  rw [← qFiniteKLTerm_sum_eq_log p q Ec (fun i hi ↦ hp i) (fun i hi ↦ hq i)
        (fun i hi hpi ↦ hsupport i hpi)] at hEc
  have hdisj : Disjoint E Ec := Finset.disjoint_sdiff
  have hunion : E ∪ Ec = Finset.univ := by
    dsimp [Ec]
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ E)
  have hsplit : qFiniteKLOn Finset.univ p q =
      qFiniteKLOn E p q + qFiniteKLOn Ec p q := by
    unfold qFiniteKLOn
    rw [← Finset.sum_union hdisj, hunion]
  rw [hsplit]
  linarith

/-- Binary KL in entropy-Bregman form is the sum of its two zero-safe atomic
KL terms whenever binary absolute continuity holds. This lemma makes the
endpoint convention explicit instead of simplifying through division by zero. -/
theorem qBinaryKL_eq_twoFiniteKLTerms
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hsupport₀ : q = 0 → p = 0) (hsupport₁ : q = 1 → p = 1) :
    qBinaryKL p q = qFiniteKLTerm p q + qFiniteKLTerm (1 - p) (1 - q) := by
  by_cases hq0 : q = 0
  · have hp0 : p = 0 := hsupport₀ hq0
    subst p
    subst q
    simp [qBinaryKL, qFiniteKLTerm, qBinaryPotential]
  · by_cases hq1 : q = 1
    · have hp1 : p = 1 := hsupport₁ hq1
      subst p
      subst q
      simp [qBinaryKL, qFiniteKLTerm, qBinaryPotential]
    · have hqpos : 0 < q := lt_of_le_of_ne hq₀ (Ne.symm hq0)
      have hqlt : q < 1 := lt_of_le_of_ne hq₁ hq1
      have h1qpos : 0 < 1 - q := sub_pos.mpr hqlt
      by_cases hp0 : p = 0
      · subst p
        have hlog : Real.log (1 / (1 - q)) = -Real.log (1 - q) := by
          rw [Real.log_div (by norm_num) (ne_of_gt h1qpos)]
          simp
        simp [qBinaryKL, qBinaryPotential, qFiniteKLTerm, hq0, hq1]
        ring
      · by_cases hp1 : p = 1
        · subst p
          have hlog : Real.log (1 / q) = -Real.log q := by
            rw [Real.log_div (by norm_num) (ne_of_gt hqpos)]
            simp
          simp [qBinaryKL, qBinaryPotential, qFiniteKLTerm, hq0, hq1]
          ring
        · have hppos : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hp0)
          have hplt : p < 1 := lt_of_le_of_ne hp₁ hp1
          have h1pne : 1 - p ≠ 0 := by
            intro h
            apply hp1
            linarith
          have h1ppos : 0 < 1 - p := sub_pos.mpr hplt
          have hlog1 := Real.log_div (ne_of_gt hppos) (ne_of_gt hqpos)
          have hlog2 := Real.log_div (ne_of_gt h1ppos) (ne_of_gt h1qpos)
          unfold qBinaryKL qBinaryPotential qFiniteKLTerm
          simp only [if_neg hq0, if_neg hq1, if_neg hp0, if_neg h1pne]
          rw [hlog1, hlog2]
          ring

/-- The source finite Pinsker inequality: half-L1 total variation and
`KL(P || Q)` use the exact coefficient 2. Absolute continuity is the only
support premise; zero-mass atoms are retained. -/
theorem qFinitePinsker
    (p q : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : (∑ i, p i) = 1) (hq1 : (∑ i, q i) = 1)
    (hsupport : ∀ i, p i ≠ 0 → q i ≠ 0) :
    2 * qFiniteTotalVariation p q ^ 2 ≤ qFiniteKLOn Finset.univ p q := by
  classical
  let E := qFinitePositiveDifferenceCell p q
  let Ec := Finset.univ \ E
  let pE := ∑ i ∈ E, p i
  let qE := ∑ i ∈ E, q i
  have hdisj : Disjoint E Ec := Finset.disjoint_sdiff
  have hunion : E ∪ Ec = Finset.univ := by
    dsimp [Ec]
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ E)
  have hsplitP : pE + (∑ i ∈ Ec, p i) = 1 := by
    have h := Finset.sum_union hdisj (f := p)
    rw [hunion] at h
    simpa [pE] using h.symm.trans hp1
  have hsplitQ : qE + (∑ i ∈ Ec, q i) = 1 := by
    have h := Finset.sum_union hdisj (f := q)
    rw [hunion] at h
    simpa [qE] using h.symm.trans hq1
  have hpE0 : 0 ≤ pE := Finset.sum_nonneg (fun i hi ↦ hp i)
  have hqE0 : 0 ≤ qE := Finset.sum_nonneg (fun i hi ↦ hq i)
  have hpEc0 : 0 ≤ ∑ i ∈ Ec, p i := Finset.sum_nonneg (fun i hi ↦ hp i)
  have hqEc0 : 0 ≤ ∑ i ∈ Ec, q i := Finset.sum_nonneg (fun i hi ↦ hq i)
  have hpE1 : pE ≤ 1 := by linarith
  have hqE1 : qE ≤ 1 := by linarith
  have hsuppE : qE = 0 → pE = 0 := by
    intro hzero
    exact qFinite_cell_zero_of_support p q E (fun i hi ↦ hp i) (fun i hi ↦ hq i)
      (fun i hi hpi ↦ hsupport i hpi) hzero
  have hsuppE1 : qE = 1 → pE = 1 := by
    intro hfull
    have hqEc : (∑ i ∈ Ec, q i) = 0 := by linarith
    have hpEc : (∑ i ∈ Ec, p i) = 0 :=
      qFinite_cell_zero_of_support p q Ec (fun i hi ↦ hp i) (fun i hi ↦ hq i)
        (fun i hi hpi ↦ hsupport i hpi) hqEc
    linarith
  have hbinary := qBinaryPinsker_source_complete pE qE hpE0 hpE1 hqE0 hqE1
    hsuppE hsuppE1
  have hbinaryKL := qBinaryKL_eq_twoFiniteKLTerms pE qE hpE0 hpE1 hqE0 hqE1
    hsuppE hsuppE1
  have hcoarse := qFiniteKL_binaryCoarsen p q hp hq hp1 hq1 hsupport E
  have htv := qFiniteTotalVariation_eq_positiveCell p q hp hq hp1 hq1
  change qFiniteTotalVariation p q = pE - qE at htv
  rw [← htv] at hbinary
  have hpc : (∑ i ∈ Ec, p i) = 1 - pE := by linarith
  have hqc : (∑ i ∈ Ec, q i) = 1 - qE := by linarith
  have hcoarse' : qBinaryKL pE qE ≤ qFiniteKLOn Finset.univ p q := by
    have hc : qFiniteKLTerm pE qE + qFiniteKLTerm (1 - pE) (1 - qE) ≤
        qFiniteKLOn Finset.univ p q := by
      dsimp [pE, qE]
      rw [← hpc, ← hqc]
      exact hcoarse
    rw [hbinaryKL]
    exact hc
  exact hbinary.trans hcoarse'

end StatisticalRL.QLearning
