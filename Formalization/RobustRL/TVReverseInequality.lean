import Mathlib
import Formalization.MDP.Basic
import Formalization.RobustRL.TVWeakDuality
import Formalization.RobustRL.TVAllRadiusWitness
import Formalization.RobustRL.TVClip

/-! TV proof source-facing reverse inequality for the finite
TV duality statement. It composes an actual feasible distribution and an
interval scalar with matching objective values, then compares those values
to the source `iInf` and `iSup`. It deliberately does not combine with weak
duality or claim equality/strong duality. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Reverse

variable {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State]

/-- The actual finite-distribution primal infimum is at most the source dual
supremum, for every nonnegative radius. Source `lemma:dual-form` assumes a
strictly positive radius; the zero case is included here as a consistent
endpoint extension. The proof constructs a matching primal row and scalar but
does not state the opposite inequality. -/
theorem tv_primalInf_le_dualSup
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVnonneg : ∀ s, 0 ≤ V s) :
    StatisticalRL.RobustRL.tvPrimalInf p V σ ≤
      StatisticalRL.RobustRL.tvDualSup p V σ := by
  classical
  let vmin := Finset.univ.inf' Finset.univ_nonempty V
  let vmax := Finset.univ.sup' Finset.univ_nonempty V
  have hVmin : ∀ s, vmin ≤ V s := by
    intro s
    exact Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s)
  have hVminAttained : ∃ s, V s = vmin := by
    obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ) (H := Finset.univ_nonempty) V
    exact ⟨s, heq.symm⟩
  have hVmax : ∀ s, V s ≤ vmax := by
    intro s
    exact Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s)
  obtain ⟨s⟩ := (inferInstance : Nonempty State)
  have hminmax : vmin ≤ vmax := le_trans (hVmin s) (hVmax s)
  have hmatch := StatisticalRL.RobustRL.TVProof.AllRadius.all_radius_matching_witness p.prob V vmin vmax σ
      p.prob_nonneg p.sum_prob hVnonneg hVmin hVminAttained hVmax hσ
  obtain ⟨α, q, hαlo, hαhi, hqNonneg, hqSum, hqEvent, hqValue⟩ := hmatch
  let qrow : StatisticalRL.FiniteDistribution State := ⟨q, hqNonneg, hqSum⟩
  have hrowFeasible :
      StatisticalRL.RobustRL.tvFeasibleRow p σ qrow := by
    change StatisticalRL.RobustRL.eventTV p.prob q ≤ σ
    simpa only [StatisticalRL.RobustRL.eventTV,
      StatisticalRL.RobustRL.eventTVMassDifference,
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV,
      StatisticalRL.RobustRL.TVProof.Event.eventMassDifference] using hqEvent
  have hαmem : α ∈ Set.Icc vmin vmax := ⟨hαlo, hαhi⟩
  have hclip (x : State) :
      StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α x =
        StatisticalRL.RobustRL.tvClipAbove V α x := by
    rw [StatisticalRL.RobustRL.TVProof.Clip.clipAbove_eq_min]
    rfl
  have hclipSum :
      (∑ x, p.prob x * StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α x) =
        (∑ x, p.prob x * StatisticalRL.RobustRL.tvClipAbove V α x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hclip]
  have hclipMin :
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α) =
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V α) := by
    congr 1
    funext x
    exact hclip x
  have hscalar :
      StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
        p.prob V σ α =
      StatisticalRL.RobustRL.tvDualObjective p V σ α := by
    unfold StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
      StatisticalRL.RobustRL.tvDualObjective StatisticalRL.FiniteDistribution.expectation
    rw [hclipSum, hclipMin]
  have hprimalBound : BddBelow (Set.range (fun q : StatisticalRL.RobustRL.tvFeasibleRows p σ ↦ q.1.expectation V)) := by
    refine ⟨vmin, ?_⟩
    rintro _ ⟨q, rfl⟩
    rw [← q.1.expectation_const vmin]
    exact q.1.expectation_mono hVmin
  have hdualBound : BddAbove (Set.range (fun a : Set.Icc vmin vmax ↦
      StatisticalRL.RobustRL.tvDualObjective p V σ a.1)) := by
    refine ⟨vmax, ?_⟩
    rintro _ ⟨a, rfl⟩
    have hclipLeAlpha : Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V a.1) ≤ a.1 := by
      obtain ⟨s⟩ := (inferInstance : Nonempty State)
      exact (Finset.inf'_le (s := Finset.univ)
        (f := StatisticalRL.RobustRL.tvClipAbove V a.1) (Finset.mem_univ s)).trans
        (min_le_right _ _)
    have hmean : p.expectation (StatisticalRL.RobustRL.tvClipAbove V a.1) ≤ vmax := by
      apply p.expectation_le_const
      intro s
      exact (min_le_left _ _).trans (hVmax s)
    unfold StatisticalRL.RobustRL.tvDualObjective
    exact (sub_le_self _ (mul_nonneg hσ (sub_nonneg.mpr hclipLeAlpha))).trans hmean
  have hprimal : StatisticalRL.RobustRL.tvPrimalInf p V σ ≤ qrow.expectation V := by
    unfold StatisticalRL.RobustRL.tvPrimalInf
    exact ciInf_le hprimalBound ⟨qrow, hrowFeasible⟩
  have hdual : StatisticalRL.RobustRL.tvDualObjective p V σ α ≤
      StatisticalRL.RobustRL.tvDualSup p V σ := by
    unfold StatisticalRL.RobustRL.tvDualSup
    exact le_ciSup hdualBound ⟨α, hαmem⟩
  have hmatchValue :
      qrow.expectation V =
        StatisticalRL.RobustRL.tvDualObjective p V σ α := by
    calc
      qrow.expectation V =
          StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
            p.prob V σ α := by
        simpa [qrow, StatisticalRL.FiniteDistribution.expectation]
          using hqValue
      _ = StatisticalRL.RobustRL.tvDualObjective p V σ α := hscalar
  exact le_trans hprimal (le_trans hmatchValue.le hdual)

end StatisticalRL.RobustRL.TVProof.Reverse
