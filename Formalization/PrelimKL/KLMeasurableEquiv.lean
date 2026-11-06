import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Pi
import Formalization.PrelimKL.KLBinaryProductAllValues

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- KL divergence of probability measures is invariant under a measurable equivalence that
preserves both measures. This is the normalization bridge used in finite-coordinate Pi induction. -/
theorem klDiv_measurePreserving_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (P : Measure α) (P' : Measure β) (Q : Measure α) (Q' : Measure β)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hP : MeasurePreserving e P P') (hQ : MeasurePreserving e Q Q') :
    InformationTheory.klDiv P Q = InformationTheory.klDiv P' Q' := by
  have hac : P ≪ Q ↔ P' ≪ Q' := by
    constructor
    · intro h
      rw [← hP.map_eq, ← hQ.map_eq]
      exact h.map e.measurable
    · intro h
      have h' := h.map e.symm.measurable
      have hPsym : MeasurePreserving e.symm P' P := MeasurePreserving.symm e hP
      have hQsym : MeasurePreserving e.symm Q' Q := MeasurePreserving.symm e hQ
      simpa only [hPsym.map_eq, hQsym.map_eq] using h'
  have hRN0 := e.measurableEmbedding.rnDeriv_map P Q
  have hRN : (fun x => P'.rnDeriv Q' (e x)) =ᵐ[Q] P.rnDeriv Q := by
    simpa only [hP.map_eq, hQ.map_eq] using hRN0
  have hcond : (P ≪ Q ∧ Integrable (MeasureTheory.llr P Q) P) ↔
      (P' ≪ Q' ∧ Integrable (MeasureTheory.llr P' Q') P' ) := by
    constructor
    · rintro ⟨hPQ, hInt⟩
      have hllr : (fun x => MeasureTheory.llr P' Q' (e x)) =ᵐ[P]
          MeasureTheory.llr P Q := by
        filter_upwards [hPQ.ae_le hRN] with x hx
        simp only [MeasureTheory.llr, hx]
      have hIntComp : Integrable (fun x => MeasureTheory.llr P' Q' (e x)) P :=
        (integrable_congr hllr).2 hInt
      exact ⟨hac.1 hPQ,
        (hP.integrable_comp_emb e.measurableEmbedding).mp hIntComp⟩
    · rintro ⟨hP'Q', hInt'⟩
      have hPQ := hac.2 hP'Q'
      have hllr : (fun x => MeasureTheory.llr P' Q' (e x)) =ᵐ[P]
          MeasureTheory.llr P Q := by
        filter_upwards [hPQ.ae_le hRN] with x hx
        simp only [MeasureTheory.llr, hx]
      have hIntComp : Integrable (fun x => MeasureTheory.llr P' Q' (e x)) P :=
        (hP.integrable_comp_emb e.measurableEmbedding).mpr hInt'
      exact ⟨hPQ, (integrable_congr hllr).mp hIntComp⟩
  have hfinite : InformationTheory.klDiv P Q ≠ ∞ ↔
      InformationTheory.klDiv P' Q' ≠ ∞ := by
    simpa only [InformationTheory.klDiv_ne_top_iff] using hcond
  by_cases hfin : InformationTheory.klDiv P Q ≠ ∞
  · have hfin' : InformationTheory.klDiv P' Q' ≠ ∞ := hfinite.mp hfin
    have hPQ : P ≪ Q := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
    have hP'Q' : P' ≪ Q' := (InformationTheory.klDiv_ne_top_iff.mp hfin').1
    have hllr : (fun x => MeasureTheory.llr P' Q' (e x)) =ᵐ[P]
        MeasureTheory.llr P Q := by
      filter_upwards [hPQ.ae_le hRN] with x hx
      simp only [MeasureTheory.llr, hx]
    apply (ENNReal.toReal_eq_toReal_iff' hfin hfin').mp
    rw [InformationTheory.toReal_klDiv_of_measure_eq hPQ (by simp [measure_univ]),
      InformationTheory.toReal_klDiv_of_measure_eq hP'Q' (by simp [measure_univ])] 
    calc
      ∫ x, MeasureTheory.llr P Q x ∂P =
          ∫ x, MeasureTheory.llr P' Q' (e x) ∂P := integral_congr_ae hllr.symm
      _ = ∫ y, MeasureTheory.llr P' Q' y ∂P' :=
        hP.integral_comp' (MeasureTheory.llr P' Q')
  · have hfin' : ¬ InformationTheory.klDiv P' Q' ≠ ∞ := fun h => hfin (hfinite.mpr h)
    have htop : InformationTheory.klDiv P Q = ∞ := by
      by_contra h; exact hfin (by simpa using h)
    have htop' : InformationTheory.klDiv P' Q' = ∞ := by
      by_contra h; exact hfin' (by simpa using h)
    simp [htop, htop']

end StatisticalRL.PrelimKL
