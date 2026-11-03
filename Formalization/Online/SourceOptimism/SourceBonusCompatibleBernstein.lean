import Formalization.Online.SourceOptimism.VarianceGapTransfer
import Formalization.Probability.EmpiricalBernsteinCombined

/-! Substitute for the source fixed-vector empirical
Bernstein step. It retains the exact source bonus conditions and failure2δ',
using a proved production concentration radius rather than assuming14/3. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State : Type*} [Fintype State]
local instance onlineBonusCompatibleStateMeasurable : MeasurableSpace State := ⊤

/-- Algebraic mean-gap absorption of the existing combined-Bernstein radius
fits the actual source bonus at its unchanged c1≥4,c2≥c1² constants. -/
theorem onlineCombinedBernstein_source_bonus
    (p d : FiniteDistribution State) (V U : State → ℝ)
    (H t q c₁ c₂ : ℝ) (hH : 0<H) (ht : 0≤t) (hq : 0≤q) (htq : t≤2*q)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hV : ∀ s,0≤V s) (hVU : ∀ s,V s≤U s) (hU : ∀ s,U s≤H)
    (hfixed : p.expectation V-d.expectation V ≤
      Real.sqrt (2*t)*(Real.sqrt (d.variance V)+4*H*Real.sqrt t)+(2/3)*H*t) :
    p.expectation V ≤ d.expectation U+c₁*Real.sqrt (d.variance U*q)+c₂*H*q := by
  have hc : p.expectation V-d.expectation V ≤
      Real.sqrt (2*t)*Real.sqrt (d.variance V)+
        (4*H*Real.sqrt (2*t)*Real.sqrt t+(2/3)*H*t) := by nlinarith [hfixed]
  have htransfer := onlineOptimisticGap_transition_certificate p d V U H
    (Real.sqrt (2*t)) (4*H*Real.sqrt (2*t)*Real.sqrt t+(2/3)*H*t)
    hH (Real.sqrt_nonneg _) hV hVU hU hc
  have hsq : (Real.sqrt (2*t))^2=2*t := Real.sq_sqrt (by positivity)
  rw [hsq] at htransfer
  have hroot2 : Real.sqrt 2≤(3/2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hcross : Real.sqrt (2*t)*Real.sqrt t≤(3/2)*t := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤2)]
    have heq : Real.sqrt 2*Real.sqrt t*Real.sqrt t=Real.sqrt 2*t := by
      nlinarith [Real.sq_sqrt ht]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hroot2 ht
  have hA : Real.sqrt (2*t)≤2*Real.sqrt q := by
    have h := Real.sqrt_le_sqrt (by linarith : 2*t≤4*q)
    have heq : Real.sqrt (4*q)=2*Real.sqrt q := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤4)]
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact h.trans_eq heq
  have hroot := mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg (d.variance U))
  have hcrossH := mul_le_mul_of_nonneg_left hcross (by positivity : 0≤4*H)
  have htH := mul_le_mul_of_nonneg_left htq (by positivity : 0≤(43/6)*H)
  have hcoeff₂ : (43/3 : ℝ)≤c₂ := by nlinarith [sq_nonneg (c₁-4)]
  have hlinear := mul_le_mul_of_nonneg_right hcoeff₂ (mul_nonneg hH.le hq)
  have hcoeff₁ : (2 : ℝ)≤c₁ := by linarith
  have hmainroot := mul_le_mul_of_nonneg_right hcoeff₁
    (mul_nonneg (Real.sqrt_nonneg q) (Real.sqrt_nonneg (d.variance U)))
  rw [Real.sqrt_mul (d.variance_nonneg U)]
  nlinarith [htransfer,hroot,hcrossH,htH,hlinear,hmainroot]

/-- Source confidence allocation is small enough to absorb log(5/(2δ'))
into twice log(1/δ'), with no confidence change. -/
theorem onlineSourceConfidence_log_compare (δ : ℝ) (hδ : 0<δ) (hδsmall : δ≤2/5) :
    0<Real.log (5/(2*δ)) ∧
      Real.log (5/(2*δ))≤2*Real.log (1/δ) := by
  have hden : 0<2*δ := by positivity
  have hratio : 1<5/(2*δ) := (lt_div_iff₀ hden).2 (by linarith)
  refine ⟨Real.log_pos hratio,?_⟩
  have harg : 5/(2*δ)≤(1/δ)^2 := by
    apply (div_le_iff₀ hden).2
    field_simp [ne_of_gt hδ]
    nlinarith
  have hp : 0<5/(2*δ) := by positivity
  have hlog := Real.log_le_log hp harg
  simpa only [Real.log_pow] using hlog

/-- One fixed true vector yields a good event uniform over every bounded
optimistic empirical continuation, so U may be selected after seeing data.
This remains a fixed deterministic sample-size theorem, not random-count iid. -/
theorem onlineFixedPrefix_source_bonus_confidence
    (p : FiniteDistribution State) (V : State → ℝ) (N : ℕ) (hN : 0<N)
    (H δ c₁ c₂ : ℝ) (hH : 0<H) (hδ : 0<δ) (hδsmall : δ≤2/5)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) (hV : ∀ s,V s∈Set.Icc 0 H) :
    1-2*δ ≤ (p.sampleMeasure N).real {data | ∀ U : State → ℝ,
      (∀ s,V s≤U s ∧ U s≤H) →
      p.expectation V≤(FiniteDistribution.empiricalRow N hN data).expectation U+
        c₁*Real.sqrt ((FiniteDistribution.empiricalRow N hN data).variance U*
          (Real.log (1/δ)/N))+c₂*H*(Real.log (1/δ)/N)} := by
  classical
  let x := Real.log (5/(2*δ))
  let q := Real.log (1/δ)/(N : ℝ)
  let t := x/(N : ℝ)
  let bad : Set (Fin N → State) := {data |
    Real.sqrt (2*x/N)*(Real.sqrt (FiniteDistribution.empiricalVariance N hN V data)+
      4*H*Real.sqrt (x/N))+2*H*x/(3*N) <
        |(FiniteDistribution.empiricalRow N hN data).expectation V-p.expectation V|}
  have hlog := onlineSourceConfidence_log_compare δ hδ hδsmall
  have hδ1 : 2*δ<1 := by linarith
  have hbad : (p.sampleMeasure N).real bad≤2*δ := by
    simpa [bad,x] using p.empiricalBernstein_combined_confidence V N hN H (2*δ)
      hH (by positivity) hδ1 hV
  have hgoodSubset : badᶜ ⊆ {data | ∀ U : State → ℝ,
      (∀ s,V s≤U s ∧ U s≤H) →
      p.expectation V≤(FiniteDistribution.empiricalRow N hN data).expectation U+
        c₁*Real.sqrt ((FiniteDistribution.empiricalRow N hN data).variance U*q)+c₂*H*q} := by
    intro data hd U hU
    simp only [Set.mem_compl_iff, bad, Set.mem_setOf_eq] at hd
    have hraw := le_of_not_gt hd
    have hfixed : p.expectation V-(FiniteDistribution.empiricalRow N hN data).expectation V≤
        Real.sqrt (2*t)*(Real.sqrt ((FiniteDistribution.empiricalRow N hN data).variance V)+
          4*H*Real.sqrt t)+(2/3)*H*t := by
      have h := (le_abs_self (p.expectation V-
        (FiniteDistribution.empiricalRow N hN data).expectation V)).trans
        (by simpa only [abs_sub_comm] using hraw)
      simpa [t,x,bad,FiniteDistribution.empiricalVariance,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
    apply onlineCombinedBernstein_source_bonus p (FiniteDistribution.empiricalRow N hN data)
      V U H t q c₁ c₂ hH (by dsimp [t]; exact div_nonneg hlog.1.le (Nat.cast_nonneg _))
      (by dsimp [q]; exact div_nonneg (by linarith [hlog.1,hlog.2]) (Nat.cast_nonneg _))
      (by
        dsimp [t,q]
        calc
          x/(N : ℝ) ≤ (2*Real.log (1/δ))/(N : ℝ) :=
            div_le_div_of_nonneg_right hlog.2 (Nat.cast_nonneg _)
          _ = 2*(Real.log (1/δ)/(N : ℝ)) := by ring)
      hc₁ hc₂ (fun s => (hV s).1) (fun s => (hU s).1) (fun s => (hU s).2) hfixed
  have hcomp := measureReal_compl (μ := p.sampleMeasure N) ((Set.to_countable bad).measurableSet)
  rw [probReal_univ] at hcomp
  have hmono := measureReal_mono hgoodSubset (measure_ne_top (p.sampleMeasure N) _)
  have hgood : 1-2*δ ≤ (p.sampleMeasure N).real badᶜ := by
    linarith only [hbad, hcomp]
  exact hgood.trans hmono

end StatisticalRL.OnlineRL
