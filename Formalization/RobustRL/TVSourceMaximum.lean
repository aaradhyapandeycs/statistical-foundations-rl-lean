import Formalization.RobustRL.TVStrongDuality

/-! Source-facing TV maximum, combining the compiled continuity
and TV equality results. The chi-squared branch is separate. -/
namespace StatisticalRL.RobustRL.TVProof.SourceMaximum

variable {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State]

/-- For a positive TV radius and nonnegative finite value vector, the actual
finite-row TV primal infimum equals an attained maximum of the clipped source
objective over the full source interval. -/
theorem tvPrimalInf_eq_source_max
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hVnonneg : ∀ s, 0 ≤ V s) :
    ∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      StatisticalRL.RobustRL.tvPrimalInf p V σ =
        StatisticalRL.RobustRL.tvDualObjective p V σ α ∧
      ∀ β ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
          (Finset.univ.sup' Finset.univ_nonempty V),
        StatisticalRL.RobustRL.tvDualObjective p V σ β ≤
          StatisticalRL.RobustRL.tvDualObjective p V σ α := by
  classical
  let vmin := Finset.univ.inf' Finset.univ_nonempty V
  let vmax := Finset.univ.sup' Finset.univ_nonempty V
  have hminmax : vmin ≤ vmax := by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    exact le_trans
      (Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s))
      (Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s))
  obtain ⟨α, hα, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨vmin, le_rfl, hminmax⟩)
    (StatisticalRL.RobustRL.TVProof.StrongDuality.tvDualObjective_continuousOn p V σ)
  have hbounded : BddAbove (Set.range (fun β : Set.Icc vmin vmax ↦
      StatisticalRL.RobustRL.tvDualObjective p V σ β.1)) := by
    refine ⟨StatisticalRL.RobustRL.tvDualObjective p V σ α, ?_⟩
    rintro _ ⟨β, rfl⟩
    exact hmax β.property
  letI : Nonempty (Set.Icc vmin vmax) := ⟨⟨vmin, le_rfl, hminmax⟩⟩
  have hsup : StatisticalRL.RobustRL.tvDualSup p V σ =
      StatisticalRL.RobustRL.tvDualObjective p V σ α := by
    unfold StatisticalRL.RobustRL.tvDualSup
    rw [iSup]
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨β, rfl⟩
      exact hmax β.property
    · exact le_csSup hbounded ⟨⟨α, hα⟩, rfl⟩
  refine ⟨α, hα, ?_, ?_⟩
  · exact (StatisticalRL.RobustRL.TVProof.StrongDuality.tvDualSup_eq_tvPrimalInf
      p V σ hσ hVnonneg).symm.trans hsup
  · intro β hβ
    exact hmax hβ
end StatisticalRL.RobustRL.TVProof.SourceMaximum
