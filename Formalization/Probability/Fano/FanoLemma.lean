import Formalization.Probability.Fano.ReverseFanoInfimum
import Formalization.Probability.Fano.TestTransports
import Formalization.Probability.Fano.ReverseTest
import Formalization.Probability.Fano.FinitePartitionKL
import Formalization.Generative.GenerativeLowerBoundFiniteDataProcessing
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing
import Formalization.Generative.GenerativeLowerBoundWeightedLog
import Formalization.Generative.GenerativeLowerBoundAffinityOverlap

/-!
# Fano's lemma for the source testing-error infima

Proof of Lemma 2.10 (`lem:fano`, `chapters/prelim.tex:1140–1202`; printed parts (i) at
1145–1152 and (ii) at 1154–1168; part (iii) at 1170–1199 is commented out in the source and is
not formalized). The error infima are the existing `averageErrorInfimum` (`p̄_e`,
`eq:defn-avg-prob-error-prelim`) and `minimaxErrorInfimum` (`p_e`,
`eq:defn-minimax-prob-error-prelim`) over measurable tests on an arbitrary measurable space.
KL is Mathlib's extended-valued `klDiv` (natural logarithm). The book prints no proof
(it cites Tsybakov 2009, §2.7.1), so the argument below is supplied here:

* (ii): per-cell binary data processing (`event_binaryKL_le_toReal_klDiv`) against `P 0`,
  then zero-tolerant log-sum inequalities (`fano_binaryKL_sum_lower`);
* (i): Bretagnolle–Huber with zero atoms (`binary_exp_neg_kl_le_two_overlap`) and the
  event Pinsker inequality (`event_sq_gap_le_klDiv`) on the cell `{ψ = 1}`.

Source fidelity of the exported statements is subject to independent review.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatisticalRL.PrelimFano

open StatisticalRL.GenerativeLowerBound

/-- Log-sum inequality on a finite set with zero first-masses allowed. -/
theorem finite_logSum_of_support {ι : Type*} [Fintype ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hab : ∀ i ∈ s, 0 < a i → 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  have hcell := finite_cell_logSum (s.filter (fun i => 0 < a i)) a b
    (fun i hi => (Finset.mem_filter.1 hi).2)
    (fun i hi => hab i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2)
  have hA : ∑ i ∈ s.filter (fun i => 0 < a i), a i = ∑ i ∈ s, a i :=
    Finset.sum_filter_of_ne (fun i hi hne => lt_of_le_of_ne (ha i hi) (Ne.symm hne))
  have hR : ∑ i ∈ s.filter (fun i => 0 < a i), a i * Real.log (a i / b i) =
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
    apply Finset.sum_filter_of_ne
    intro i hi hne
    refine lt_of_le_of_ne (ha i hi) ?_
    intro h0
    apply hne
    rw [← h0, zero_mul]
  rw [hA, hR] at hcell
  refine le_trans ?_ hcell
  rcases (Finset.sum_nonneg ha).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · apply mul_le_mul_of_nonneg_left _ hpos.le
    have hne : (s.filter (fun i => 0 < a i)).Nonempty := by
      have h : ∑ i ∈ s.filter (fun i => 0 < a i), a i ≠ 0 := by
        rw [hA]
        exact hpos.ne'
      exact Finset.nonempty_of_sum_ne_zero h
    have hB' : 0 < ∑ i ∈ s.filter (fun i => 0 < a i), b i :=
      Finset.sum_pos
        (fun i hi => hab i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2) hne
    have hBB : ∑ i ∈ s.filter (fun i => 0 < a i), b i ≤ ∑ i ∈ s, b i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => hb i hi)
    exact Real.log_le_log (div_pos hpos (hB'.trans_le hBB))
      (div_le_div_of_nonneg_left hpos.le hB' hBB)

/-- Pure-real Fano core: the summed binary relative entropies of the
per-hypothesis decision cells dominate `K (log K - log 2) - T log M`, where
`K = M + 1` and `T = ∑ (1 - a j)` is the total error mass. -/
theorem fano_binaryKL_sum_lower (M : ℕ) (hM : 1 ≤ M) (a b : Fin (M+1) → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1)
    (hbsum : ∑ j, b j = 1)
    (hpos : ∀ j, 0 < a j → 0 < b j) (hlt : ∀ j, 0 < 1 - a j → 0 < 1 - b j) :
    ((M : ℝ) + 1) * (Real.log ((M : ℝ) + 1) - Real.log 2) -
        (∑ j, (1 - a j)) * Real.log (M : ℝ) ≤
      ∑ j, (a j * Real.log (a j / b j) + (1 - a j) * Real.log ((1 - a j) / (1 - b j))) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set S := ∑ j, a j with hS
  set T := ∑ j, (1 - a j) with hT
  have hST : S + T = (M : ℝ) + 1 := by
    rw [hS, hT, Finset.sum_sub_distrib]
    simp
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => ha0 j)
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => sub_nonneg.2 (ha1 j))
  have hb' : ∑ j, (1 - b j) = (M : ℝ) := by
    rw [Finset.sum_sub_distrib, hbsum]
    simp
  have h1 := finite_logSum_of_support Finset.univ a b (fun j _ => ha0 j) (fun j _ => hb0 j)
    (fun j _ => hpos j)
  rw [hbsum, div_one] at h1
  have h2 := finite_logSum_of_support Finset.univ (fun j => 1 - a j) (fun j => 1 - b j)
    (fun j _ => sub_nonneg.2 (ha1 j)) (fun j _ => sub_nonneg.2 (hb1 j)) (fun j _ => hlt j)
  rw [hb'] at h2
  have h3 := finite_logSum_of_support (Finset.univ : Finset (Fin 2)) ![S, T] ![1, 1]
    (fun i _ => by fin_cases i <;> simp [hS0, hT0])
    (fun i _ => by fin_cases i <;> simp)
    (fun i _ _ => by fin_cases i <;> simp)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    div_one] at h3
  rw [hST, one_add_one_eq_two, Real.log_div (by positivity) two_ne_zero] at h3
  have hTlog : T * Real.log (T / M) = T * Real.log T - T * Real.log M := by
    rcases hT0.eq_or_lt with h | h
    · rw [← h]
      simp
    · rw [Real.log_div h.ne' hMpos.ne']
      ring
  rw [hTlog] at h2
  rw [Finset.sum_add_distrib]
  linarith

/-- Absolute continuity transfers positivity of the real mass of any set. -/
theorem measureReal_pos_of_ac {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) {S : Set Ω}
    (h : 0 < μ.real S) : 0 < ν.real S := by
  rcases (measureReal_nonneg (μ := ν) (s := S)).eq_or_lt with h0 | h0
  · exfalso
    have hν : ν S = 0 := (measureReal_eq_zero_iff (measure_ne_top ν S)).1 h0.symm
    have hμ : μ.real S = 0 := (measureReal_eq_zero_iff (measure_ne_top μ S)).2 (hac hν)
    linarith
  · exact h0

/-- Binary data processing for one measurable event: the binary relative
entropy of the event probabilities is at most the (finite) KL divergence. -/
theorem event_binaryKL_le_toReal_klDiv {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfin : InformationTheory.klDiv μ ν ≠ ∞) {A : Set Ω} (hA : MeasurableSet A) :
    μ.real A * Real.log (μ.real A / ν.real A) +
        (1 - μ.real A) * Real.log ((1 - μ.real A) / (1 - ν.real A)) ≤
      (InformationTheory.klDiv μ ν).toReal := by
  classical
  have hf : Measurable (eventIndicatorBool A) := measurable_eventIndicatorBool hA
  letI : IsProbabilityMeasure (μ.map (eventIndicatorBool A)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (ν.map (eventIndicatorBool A)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hdpi := finiteValued_klDiv_map_le μ ν (eventIndicatorBool A) hf
  have hac : μ.map (eventIndicatorBool A) ≪ ν.map (eventIndicatorBool A) :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin).1.map hf
  have hexpr := finite_klDiv_eq_expression_of_ac (μ.map (eventIndicatorBool A))
    (ν.map (eventIndicatorBool A)) hac
  have htrue : eventIndicatorBool A ⁻¹' {true} = A := by
    ext ω; simp [eventIndicatorBool]
  have hfalse : eventIndicatorBool A ⁻¹' {false} = Aᶜ := by
    ext ω; simp [eventIndicatorBool]
  have hcellT : ∀ ρ : Measure Ω, (ρ.map (eventIndicatorBool A)).real {true} = ρ.real A := by
    intro ρ
    rw [measureReal_def, Measure.map_apply hf (measurableSet_singleton _), htrue]
    rfl
  have hcellF : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] →
      (ρ.map (eventIndicatorBool A)).real {false} = 1 - ρ.real A := by
    intro ρ _
    rw [measureReal_def, Measure.map_apply hf (measurableSet_singleton _), hfalse,
      ← measureReal_def, probReal_compl_eq_one_sub hA]
  unfold finiteKLExpression at hexpr
  rw [Fintype.sum_bool] at hexpr
  dsimp only at hexpr
  rw [hcellT μ, hcellT ν, hcellF μ, hcellF ν] at hexpr
  rw [← hexpr]
  exact ENNReal.toReal_mono hfin hdpi

/-- Per-test Fano bound for `M ≥ 2`, with every KL divergence to `P 0` finite. -/
theorem fano_test_average_error_lower {Ω : Type*} [MeasurableSpace Ω] (M : ℕ) (hM : 2 ≤ M)
    (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin : ∀ j, InformationTheory.klDiv (P j) (P 0) ≠ ∞)
    (ψ : MeasurableTest (Ω := Ω) (I := Fin (M+1))) :
    (Real.log ((M : ℝ) + 1) - Real.log 2 -
        (∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal) / ((M : ℝ) + 1)) /
      Real.log (M : ℝ) ≤ averageTestError P ψ := by
  classical
  let A : Fin (M+1) → Set Ω := fun j => ψ.1 ⁻¹' {j}
  have hA : ∀ j, MeasurableSet (A j) := fun j => ψ.2 (measurableSet_singleton j)
  let a : Fin (M+1) → ℝ := fun j => (P j).real (A j)
  let b : Fin (M+1) → ℝ := fun j => (P 0).real (A j)
  have hbsum : ∑ j, b j = 1 := by
    have h := sum_measureReal_preimage_singleton (μ := P 0)
      (Finset.univ : Finset (Fin (M+1))) (f := ψ.1) (fun y _ => hA y)
    simpa [b, A, probReal_univ] using h
  have hac : ∀ j, P j ≪ P 0 := fun j => (InformationTheory.klDiv_ne_top_iff.mp (hfin j)).1
  have hpos : ∀ j, 0 < a j → 0 < b j := fun j h => measureReal_pos_of_ac (hac j) h
  have hlt : ∀ j, 0 < 1 - a j → 0 < 1 - b j := by
    intro j h
    have h1 : 0 < (P j).real (A j)ᶜ := by
      rw [probReal_compl_eq_one_sub (hA j)]
      exact h
    have h2 := measureReal_pos_of_ac (hac j) h1
    rwa [probReal_compl_eq_one_sub (hA j)] at h2
  have hcore := fano_binaryKL_sum_lower M (by omega) a b
    (fun j => measureReal_nonneg) (fun j => measureReal_le_one)
    (fun j => measureReal_nonneg) (fun j => measureReal_le_one) hbsum hpos hlt
  have hsum : ∑ j, (a j * Real.log (a j / b j) + (1 - a j) * Real.log ((1 - a j) / (1 - b j))) ≤
      ∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal :=
    Finset.sum_le_sum (fun j _ => event_binaryKL_le_toReal_klDiv (P j) (P 0) (hfin j) (hA j))
  have havg : averageTestError P ψ = (∑ j, (1 - a j)) / ((M : ℝ) + 1) := by
    rw [averageTestError_fin_eq M P ψ]
    have herr : ∀ j, (P j).real {ω | ψ.1 ω ≠ j} = 1 - a j := by
      intro j
      have hset : {ω | ψ.1 ω ≠ j} = (A j)ᶜ := by
        ext ω; simp [A]
      rw [hset, probReal_compl_eq_one_sub (hA j)]
    simp_rw [herr]
    ring
  rw [havg]
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hK : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hlogM]
  set KLsum := ∑ j, (InformationTheory.klDiv (P j) (P 0)).toReal
  set T := ∑ j, (1 - a j)
  have key : ((M : ℝ) + 1) * (Real.log ((M : ℝ) + 1) - Real.log 2) - KLsum ≤
      T * Real.log (M : ℝ) := by linarith
  calc Real.log ((M : ℝ) + 1) - Real.log 2 - KLsum / ((M : ℝ) + 1)
      = (((M : ℝ) + 1) * (Real.log ((M : ℝ) + 1) - Real.log 2) - KLsum) / ((M : ℝ) + 1) := by
        field_simp
    _ ≤ (T * Real.log (M : ℝ)) / ((M : ℝ) + 1) := div_le_div_of_nonneg_right key hK.le
    _ = T / ((M : ℝ) + 1) * Real.log (M : ℝ) := by ring

/-- Lemma 2.10 (ii) (`lem:fano`, `eq:fano-multi`, `chapters/prelim.tex:1154–1168`) for the
source error infima: if `M ≥ 2`, `0 < β < 1` and `(1/(M+1)) ∑_{j=1}^M KL(P_j‖P_0) ≤ β log M`
(in `ℝ≥0∞`), then `p_e ≥ p̄_e ≥ (log(M+1) - log 2)/log M - β`. The printed premise `β < 1`
is kept in the signature although the proof does not use it. -/
theorem fano_multi_infimum_lower {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)] (β : ℝ)
    (hM : 2 ≤ M) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (hKL : ENNReal.ofReal (1 / ((M : ℝ) + 1)) *
        ∑ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≤
      ENNReal.ofReal (β * Real.log (M : ℝ))) :
    averageErrorInfimum P ≤ minimaxErrorInfimum P ∧
      (Real.log ((M : ℝ) + 1) - Real.log 2) / Real.log (M : ℝ) - β ≤
        averageErrorInfimum P := by
  refine ⟨averageErrorInfimum_le_minimaxErrorInfimum P, ?_⟩
  have hK : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hcne : ENNReal.ofReal (1 / ((M : ℝ) + 1)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hprod_ne : ENNReal.ofReal (1 / ((M : ℝ) + 1)) *
      ∑ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hsum_ne : ∑ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hcne] at hprod_ne
    exact hprod_ne rfl
  have hsucc_ne : ∀ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≠ ∞ :=
    fun j => (ENNReal.sum_ne_top.1 hsum_ne) j (Finset.mem_univ j)
  have hfin : ∀ j : Fin (M+1), InformationTheory.klDiv (P j) (P 0) ≠ ∞ := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
    · rw [h, InformationTheory.klDiv_self]
      exact ENNReal.zero_ne_top
    · exact hsucc_ne i
  have hreal : (1 / ((M : ℝ) + 1)) *
      ∑ j : Fin M, (InformationTheory.klDiv (P j.succ) (P 0)).toReal ≤
        β * Real.log (M : ℝ) := by
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hKL
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_sum (fun j _ => hsucc_ne j)] at h
  have hKLsumEq : ∑ j : Fin (M+1), (InformationTheory.klDiv (P j) (P 0)).toReal =
      ∑ j : Fin M, (InformationTheory.klDiv (P j.succ) (P 0)).toReal := by
    rw [Fin.sum_univ_succ, InformationTheory.klDiv_self, ENNReal.toReal_zero, zero_add]
  apply lower_bound_averageErrorInfimum_of_forall_tests P
  intro ψ
  refine le_trans ?_ (fano_test_average_error_lower M hM P hfin ψ)
  rw [hKLsumEq]
  set KLsum := ∑ j : Fin M, (InformationTheory.klDiv (P j.succ) (P 0)).toReal
  have hb : KLsum / ((M : ℝ) + 1) ≤ β * Real.log (M : ℝ) := by
    rw [div_eq_mul_inv, mul_comm, ← one_div]
    exact hreal
  rw [le_div_iff₀ hlogM]
  have e : ((Real.log ((M : ℝ) + 1) - Real.log 2) / Real.log (M : ℝ) - β) * Real.log (M : ℝ) =
      Real.log ((M : ℝ) + 1) - Real.log 2 - β * Real.log (M : ℝ) := by
    field_simp
  rw [e]
  linarith

/-- Finite Bretagnolle–Huber bound with zero masses allowed: only the support
of the first law must be charged by the second. -/
theorem exp_neg_finiteKL_le_two_overlap_of_support {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hsupp : ∀ i, 0 < u i → 0 < v i) (hsumu : ∑ i, u i = 1) (hsumv : ∑ i, v i = 1) :
    Real.exp (-finiteKLExpression u v) ≤ 2 * ∑ i, min (u i) (v i) := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => 0 < u i)
  have hsu : ∑ i ∈ s, u i = 1 := by
    rw [Finset.sum_filter_of_ne (fun i _ hne => lt_of_le_of_ne (hu i) (Ne.symm hne))]
    exact hsumu
  have hne : s.Nonempty := by
    have h : ∑ i ∈ s, u i ≠ 0 := by
      rw [hsu]
      exact one_ne_zero
    exact Finset.nonempty_of_sum_ne_zero h
  haveI : Nonempty s := hne.to_subtype
  have hlog := finite_log_affinity_lower (fun i : s => u i) (fun i : s => v i)
    (fun i => (Finset.mem_filter.1 i.2).2) (fun i => hsupp i (Finset.mem_filter.1 i.2).2)
    (by rw [Finset.sum_coe_sort s u]; exact hsu)
  have hKL : finiteKLExpression (fun i : s => u i) (fun i : s => v i) =
      finiteKLExpression u v := by
    unfold finiteKLExpression
    rw [Finset.sum_coe_sort s (fun i => u i * Real.log (u i / v i))]
    apply Finset.sum_filter_of_ne
    intro i _ hne
    refine lt_of_le_of_ne (hu i) ?_
    intro h0
    apply hne
    rw [← h0, zero_mul]
  have hAff : finiteAffinity (fun i : s => u i) (fun i : s => v i) = finiteAffinity u v := by
    unfold finiteAffinity
    rw [Finset.sum_coe_sort s (fun i => Real.sqrt (u i) * Real.sqrt (v i))]
    apply Finset.sum_filter_of_ne
    intro i _ hne
    refine lt_of_le_of_ne (hu i) ?_
    intro h0
    apply hne
    rw [← h0, Real.sqrt_zero, zero_mul]
  rw [hKL, hAff] at hlog
  obtain ⟨i0, hi0⟩ := hne
  have hi0' : 0 < u i0 := (Finset.mem_filter.1 hi0).2
  have hAffpos : 0 < finiteAffinity u v := by
    unfold finiteAffinity
    calc (0 : ℝ) < Real.sqrt (u i0) * Real.sqrt (v i0) :=
          mul_pos (Real.sqrt_pos.2 hi0') (Real.sqrt_pos.2 (hsupp i0 hi0'))
      _ ≤ ∑ i, Real.sqrt (u i) * Real.sqrt (v i) :=
          Finset.single_le_sum (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (Finset.mem_univ i0)
  have hexp : Real.exp (-finiteKLExpression u v / 2) ≤ finiteAffinity u v := by
    calc Real.exp (-finiteKLExpression u v / 2) ≤ Real.exp (Real.log (finiteAffinity u v)) :=
          Real.exp_le_exp.2 hlog
      _ = finiteAffinity u v := Real.exp_log hAffpos
  have hsq := finite_affinity_sq_le_two_overlap u v hu hv hsumu hsumv
  have hsplit : Real.exp (-finiteKLExpression u v) =
      Real.exp (-finiteKLExpression u v / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsplit]
  calc Real.exp (-finiteKLExpression u v / 2) ^ 2 ≤ (finiteAffinity u v) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hexp 2
    _ ≤ 2 * ∑ i, min (u i) (v i) := hsq

/-- Two-point Bretagnolle–Huber bound for event probabilities, zeros allowed. -/
theorem binary_exp_neg_kl_le_two_overlap (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hpos : 0 < a → 0 < b) (hlt : 0 < 1 - a → 0 < 1 - b) :
    Real.exp (-(a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)))) ≤
      2 * (min a b + min (1 - a) (1 - b)) := by
  have h := exp_neg_finiteKL_le_two_overlap_of_support ![a, 1 - a] ![b, 1 - b]
    (fun i => by fin_cases i <;> simp [ha0, ha1])
    (fun i => by fin_cases i <;> simp [hb0, hb1])
    (fun i => by
      fin_cases i
      · simpa using hpos
      · simpa using hlt)
    (by simp [Fin.sum_univ_two])
    (by simp [Fin.sum_univ_two])
  simp only [finiteKLExpression, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  exact h

/-- Per-test two-point bounds (Le Cam/Bretagnolle–Huber and Pinsker branches). -/
theorem fano_binary_test_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Fin 2 → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin : InformationTheory.klDiv (P 1) (P 0) ≠ ∞)
    (ψ : MeasurableTest (Ω := Ω) (I := Fin 2)) :
    1 / 4 * Real.exp (-(InformationTheory.klDiv (P 1) (P 0)).toReal) ≤
        averageTestError P ψ ∧
      (1 - Real.sqrt ((InformationTheory.klDiv (P 1) (P 0)).toReal / 2)) / 2 ≤
        averageTestError P ψ := by
  classical
  set K := (InformationTheory.klDiv (P 1) (P 0)).toReal with hK
  let A : Set Ω := ψ.1 ⁻¹' {1}
  have hA : MeasurableSet A := ψ.2 (measurableSet_singleton 1)
  set a := (P 1).real A with ha
  set b := (P 0).real A with hb
  have hset0 : {x | ψ.1 x ≠ 0} = A := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, A]
    constructor
    · exact Fin.eq_one_of_ne_zero _
    · intro h
      rw [h]
      decide
  have hset1 : {x | ψ.1 x ≠ 1} = Aᶜ := by
    ext x
    simp [A]
  have havg : averageTestError P ψ = (b + (1 - a)) / 2 := by
    unfold averageTestError testError
    rw [Fin.sum_univ_two, hset0, hset1, probReal_compl_eq_one_sub hA, Fintype.card_fin]
    push_cast
    ring
  have hac : P 1 ≪ P 0 := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  constructor
  · have hkl := event_binaryKL_le_toReal_klDiv (P 1) (P 0) hfin hA
    have hpos : 0 < a → 0 < b := fun h => measureReal_pos_of_ac hac h
    have hlt : 0 < 1 - a → 0 < 1 - b := by
      intro h
      have h1 : 0 < (P 1).real Aᶜ := by
        rw [probReal_compl_eq_one_sub hA]
        exact h
      have h2 := measureReal_pos_of_ac hac h1
      rwa [probReal_compl_eq_one_sub hA] at h2
    have hbh := binary_exp_neg_kl_le_two_overlap a b measureReal_nonneg measureReal_le_one
      measureReal_nonneg measureReal_le_one hpos hlt
    have hmono : Real.exp (-K) ≤
        Real.exp (-(a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)))) :=
      Real.exp_le_exp.2 (by linarith)
    have hmin : min a b + min (1 - a) (1 - b) ≤ b + (1 - a) :=
      add_le_add (min_le_right _ _) (min_le_left _ _)
    rw [havg]
    linarith
  · have hpin := event_sq_gap_le_klDiv (P 1) (P 0) hA
    rw [ENNReal.ofReal_le_iff_le_toReal hfin] at hpin
    have hsq : (a - b) ^ 2 ≤ K / 2 := by
      rw [← hK] at hpin
      linarith
    have hroot : a - b ≤ Real.sqrt (K / 2) := Real.le_sqrt_of_sq_le hsq
    rw [havg]
    linarith

/-- Lemma 2.10 (i) (`lem:fano`, `eq:fano-binary`, `chapters/prelim.tex:1145–1152`) for the
source error infima with two hypotheses `P 0, P 1`: if `KL(P_1‖P_0)` is finite and at most
`β`, then `p_e ≥ p̄_e ≥ max{exp(-β)/4, (1 - √(β/2))/2}`. -/
theorem fano_binary_infimum_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Fin 2 → Measure Ω) [∀ j, IsProbabilityMeasure (P j)] (β : ℝ)
    (hfin : InformationTheory.klDiv (P 1) (P 0) ≠ ∞)
    (hβ : (InformationTheory.klDiv (P 1) (P 0)).toReal ≤ β) :
    averageErrorInfimum P ≤ minimaxErrorInfimum P ∧
      max (1 / 4 * Real.exp (-β)) ((1 - Real.sqrt (β / 2)) / 2) ≤
        averageErrorInfimum P := by
  refine ⟨averageErrorInfimum_le_minimaxErrorInfimum P, ?_⟩
  apply lower_bound_averageErrorInfimum_of_forall_tests P
  intro ψ
  obtain ⟨h1, h2⟩ := fano_binary_test_lower P hfin ψ
  apply max_le
  · refine le_trans ?_ h1
    have : Real.exp (-β) ≤ Real.exp (-(InformationTheory.klDiv (P 1) (P 0)).toReal) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · refine le_trans ?_ h2
    have : Real.sqrt ((InformationTheory.klDiv (P 1) (P 0)).toReal / 2) ≤ Real.sqrt (β / 2) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith

end StatisticalRL.PrelimFano
