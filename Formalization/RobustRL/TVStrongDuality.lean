import Mathlib
import Formalization.MDP.Basic
import Formalization.RobustRL.TVWeakDuality
import Formalization.RobustRL.TVReverseInequality
import Formalization.RobustRL.TVClip

/-!
# Total-variation strong duality and scalar maximum attainment

Combines the constructed reverse inequality and the existing weak bound for
the TV branch of `lemma:dual-form`. Continuity on the exact source interval
gives scalar maximum attainment. The chi-squared branch remains separate.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.StrongDuality

variable {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State]

local notation "TVInf" => StatisticalRL.RobustRL.tvPrimalInf

local notation "TVSup" => StatisticalRL.RobustRL.tvDualSup

local notation "TVObj" => StatisticalRL.RobustRL.tvDualObjective

/-- The scalar source objective is continuous on `[Vmin,Vmax]`. The clipped
minimum term is constant there and equals the attained value minimum. -/
theorem tvDualObjective_continuousOn
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) :
    ContinuousOn (fun α ↦ TVObj p V σ α)
      (Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V)) := by
  classical
  let vmin := Finset.univ.inf' Finset.univ_nonempty V
  let vmax := Finset.univ.sup' Finset.univ_nonempty V
  let f : ℝ → ℝ := fun α ↦
    (∑ s, p.prob s * min (V s) α) - σ * (α - vmin)
  have hvmin : ∀ s, vmin ≤ V s := by
    intro s
    exact Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s)
  have hvminAttained : ∃ s, V s = vmin := by
    obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ) (H := Finset.univ_nonempty) V
    exact ⟨s, heq.symm⟩
  have hvmax : ∀ s, V s ≤ vmax := by
    intro s
    exact Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s)
  have hminmax : vmin ≤ vmax := by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    exact le_trans (hvmin s) (hvmax s)
  have hclipMin (α : ℝ) (hα : α ∈ Set.Icc vmin vmax) :
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V α) = vmin := by
    obtain ⟨hbound, ⟨s, hs⟩⟩ := StatisticalRL.RobustRL.tvClipAbove_minimum V α vmin hvmin hvminAttained hα.1
    apply le_antisymm
    · calc
        Finset.univ.inf' Finset.univ_nonempty
            (StatisticalRL.RobustRL.tvClipAbove V α) ≤
          StatisticalRL.RobustRL.tvClipAbove V α s :=
            Finset.inf'_le (s := Finset.univ)
              (f := StatisticalRL.RobustRL.tvClipAbove V α)
              (Finset.mem_univ s)
        _ = vmin := by simpa [StatisticalRL.RobustRL.tvClipAbove_eq_min] using hs
    · apply Finset.le_inf'
      intro s hs
      exact hbound s
  have hobj (α : ℝ) (hα : α ∈ Set.Icc vmin vmax) :
      TVObj p V σ α = f α := by
    unfold StatisticalRL.RobustRL.tvDualObjective f
    rw [hclipMin α hα]
    simp [StatisticalRL.RobustRL.tvClipAbove, StatisticalRL.FiniteDistribution.expectation]
  have hsumCont : Continuous (fun α ↦
      ∑ s, p.prob s * min (V s) α) := by
    apply continuous_finset_sum
    intro s hs
    exact continuous_const.mul (continuous_const.min continuous_id)
  have hf : Continuous f := by
    dsimp [f]
    exact hsumCont.sub (continuous_const.mul
      (continuous_id.sub continuous_const))
  exact hf.continuousOn.congr (fun α hα ↦ hobj α hα)

/-- The source scalar supremum is attained on the exact closed interval
`[Vmin,Vmax]`; this is the continuity/compactness step needed to report the
source's literal `max` rather than a supremum. -/
theorem tvDualSup_attained
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) :
    ∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      TVObj p V σ α = TVSup p V σ := by
  classical
  let vmin := Finset.univ.inf' Finset.univ_nonempty V
  let vmax := Finset.univ.sup' Finset.univ_nonempty V
  have hminmax : vmin ≤ vmax := by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    exact le_trans
      (Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s))
      (Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s))
  letI : Nonempty (Set.Icc vmin vmax) := ⟨⟨vmin, le_rfl, hminmax⟩⟩
  obtain ⟨α, hα, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨vmin, le_rfl, hminmax⟩)
    (tvDualObjective_continuousOn p V σ)
  have hsup : TVSup p V σ = TVObj p V σ α := by
    unfold StatisticalRL.RobustRL.tvDualSup
    rw [iSup]
    have hbounded : BddAbove (Set.range (fun β : Set.Icc vmin vmax ↦ TVObj p V σ β.1)) := by
      refine ⟨TVObj p V σ α, ?_⟩
      rintro _ ⟨β, rfl⟩
      exact hmax β.property
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨β, rfl⟩
      exact hmax β.property
    · exact le_csSup hbounded ⟨⟨α, hα⟩, rfl⟩
  exact ⟨α, hα, hsup.symm⟩

/-- Compose the weak and reverse inequalities for the source positive-radius TV branch. -/
theorem tvDualSup_eq_tvPrimalInf
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hVnonneg : ∀ s, 0 ≤ V s) :
    TVSup p V σ = TVInf p V σ := by
  apply le_antisymm
  · exact StatisticalRL.RobustRL.tv_dualSup_le_primalInf p V σ hσ hVnonneg
  · exact StatisticalRL.RobustRL.TVProof.Reverse.tv_primalInf_le_dualSup p V σ hσ.le hVnonneg

/-- Source-facing maximum form of the TV duality claim. This statement
combines strong-duality equality with scalar maximum attainment. -/
theorem tvPrimalInf_eq_attained_tvDualMax
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hVnonneg : ∀ s, 0 ≤ V s) :
    ∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      TVObj p V σ α = TVInf p V σ := by
  obtain ⟨α, hα, hmax⟩ := tvDualSup_attained p V σ
  have heq := tvDualSup_eq_tvPrimalInf p V σ hσ hVnonneg
  exact ⟨α, hα, hmax.trans (by rw [heq])⟩

end StatisticalRL.RobustRL.TVProof.StrongDuality
