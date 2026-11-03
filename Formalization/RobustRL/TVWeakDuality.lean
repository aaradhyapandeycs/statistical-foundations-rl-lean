import Formalization.RobustRL.TVCore
import Formalization.RobustRL.TVWeakBound
import Formalization.MDP.Basic

/-! Source-facing weak-duality corollary for the finite-state TV branch of
`lemma:dual-form`. It uses the project's actual `FiniteDistribution` carrier
and the source event-TV ball. The conclusion is only dual-supremum ≤
primal-infimum; strong duality and dual maximizer attainment are not asserted. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL

variable {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State]

/-- Actual finite probability rows allowed by the source TV uncertainty ball.
The radius is the source `σ` (the command `\ror` expands to `\sigma`). -/
def tvFeasibleRow (p : StatisticalRL.FiniteDistribution State) (σ : ℝ)
    (q : StatisticalRL.FiniteDistribution State) : Prop :=
  StatisticalRL.RobustRL.eventTV p.prob q.prob ≤ σ

/-- The actual feasible-row type for a fixed nominal row and radius. -/
abbrev tvFeasibleRows (p : StatisticalRL.FiniteDistribution State) (σ : ℝ) :=
  {q : StatisticalRL.FiniteDistribution State // tvFeasibleRow p σ q}

/-- The exact source clipped-vector dual objective. The final term uses the
actual finite minimum of the clipped vector, as in `robust_RL.tex`; it is not
silently replaced by a candidate parameter. -/
noncomputable def tvDualObjective (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ α : ℝ) : ℝ :=
  p.expectation (StatisticalRL.RobustRL.tvClipAbove V α) -
    σ * (α -
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V α))

/-- The source primal infimum over actual finite distributions in the TV ball. -/
noncomputable def tvPrimalInf (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ : ℝ) : ℝ :=
  ⨅ q : tvFeasibleRows p σ, q.1.expectation V

/-- The source dual supremum over the closed interval `[Vmin,Vmax]`. Once
continuity is established this supremum is a maximum; this file only proves
the weak-duality inequality and does not use attainment. -/
noncomputable def tvDualSup (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ : ℝ) : ℝ :=
  ⨆ α : Set.Icc
      (Finset.univ.inf' Finset.univ_nonempty V)
      (Finset.univ.sup' Finset.univ_nonempty V),
    tvDualObjective p V σ α.1

/-- The nominal row belongs to its own positive-radius TV ball. -/
theorem tvFeasibleRows_nonempty
    (p : StatisticalRL.FiniteDistribution State) (σ : ℝ) (hσ : 0 < σ) :
    Nonempty (tvFeasibleRows p σ) := by
  have hEvent := StatisticalRL.RobustRL.eventTV_eq_finiteTotalVariation
    p.prob p.prob p.prob_nonneg p.prob_nonneg p.sum_prob p.sum_prob
  have hTVzero : StatisticalRL.RobustRL.eventTV
      p.prob p.prob = 0 := by
    rw [hEvent]
    unfold StatisticalRL.QLearning.qFiniteTotalVariation
    simp
  refine ⟨⟨p, ?_⟩⟩
  change StatisticalRL.RobustRL.eventTV
    p.prob p.prob ≤ σ
  rw [hTVzero]
  exact hσ.le

/-- The finite TV branch has weak duality with the source's exact `σ`
normalization and actual finite probability distributions:

`sup_{α ∈ [Vmin,Vmax]} dual(α) ≤ inf_{q : TV(q,p)≤σ} E_q[V]`.

The event-TV/half-L1 normalization is supplied by the finite event bridge in
`Formalization.RobustRL.TVCore`; the source clipped minimum is preserved in
`tvDualObjective`. This is only the weak direction. It does not establish
equality, a saddle point, or the source's strong-duality claim. -/
theorem tv_dualSup_le_primalInf
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hVnonneg : ∀ s, 0 ≤ V s) :
    tvDualSup p V σ ≤ tvPrimalInf p V σ := by
  classical
  have hRows : Nonempty (tvFeasibleRows p σ) := tvFeasibleRows_nonempty p σ hσ
  letI := hRows
  have hInterval : Nonempty (Set.Icc
      (Finset.univ.inf' Finset.univ_nonempty V)
      (Finset.univ.sup' Finset.univ_nonempty V)) := by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    refine ⟨⟨Finset.univ.inf' Finset.univ_nonempty V,
      le_rfl, ?_⟩⟩
    exact le_trans
      (Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s))
      (Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s))
  letI := hInterval
  unfold tvDualSup tvPrimalInf
  rw [iSup, iInf]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨α, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro z ⟨q, rfl⟩
  let vmin := Finset.univ.inf' Finset.univ_nonempty V
  let vmax := Finset.univ.sup' Finset.univ_nonempty V
  have hVmin : ∀ s, vmin ≤ V s := fun s ↦
    Finset.inf'_le (s := Finset.univ) (f := V) (Finset.mem_univ s)
  have hVminAttained : ∃ s, V s = vmin := by
    obtain ⟨s, hs, heq⟩ :=
      Finset.exists_mem_eq_inf' (s := Finset.univ)
        (H := Finset.univ_nonempty) V
    exact ⟨s, heq.symm⟩
  have hVmax : ∀ s, V s ≤ vmax := fun s ↦
    Finset.le_sup' (s := Finset.univ) (f := V) (Finset.mem_univ s)
  have hVminLeMax : vmin ≤ vmax := by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    exact le_trans (hVmin s) (hVmax s)
  have hclipMin :
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V α.1) = vmin := by
    apply le_antisymm
    · obtain ⟨s, hs, heq⟩ :=
        Finset.exists_mem_eq_inf' (s := Finset.univ)
          (H := Finset.univ_nonempty) V
      calc
        Finset.univ.inf' Finset.univ_nonempty
            (StatisticalRL.RobustRL.tvClipAbove V α.1) ≤
            StatisticalRL.RobustRL.tvClipAbove V α.1 s :=
          Finset.inf'_le (s := Finset.univ)
            (f := StatisticalRL.RobustRL.tvClipAbove V α.1)
            (Finset.mem_univ s)
        _ = vmin := by
          dsimp [StatisticalRL.RobustRL.tvClipAbove]
          rw [← heq]
          exact min_eq_left α.2.1
    · apply Finset.le_inf'
      intro s hs
      dsimp [StatisticalRL.RobustRL.tvClipAbove]
      exact le_min (hVmin s) α.2.1
  have hTVhalf :
      StatisticalRL.QLearning.qFiniteTotalVariation p.prob q.1.prob ≤ σ := by
    have hEvent := StatisticalRL.RobustRL.eventTV_eq_finiteTotalVariation
      p.prob q.1.prob p.prob_nonneg q.1.prob_nonneg p.sum_prob q.1.sum_prob
    calc
      StatisticalRL.QLearning.qFiniteTotalVariation p.prob q.1.prob =
          StatisticalRL.RobustRL.eventTV p.prob q.1.prob := hEvent.symm
      _ ≤ σ := q.2
  have hweak := StatisticalRL.RobustRL.tv_clipped_weak_duality
    p.prob q.1.prob V vmin vmax α.1 σ
    p.prob_nonneg q.1.prob_nonneg p.sum_prob q.1.sum_prob hVnonneg
    hVmin hVminAttained hVmax hVminLeMax hσ α.2.1 α.2.2 hTVhalf
  simpa [tvDualObjective, vmin, hclipMin, StatisticalRL.FiniteDistribution.expectation] using hweak

end StatisticalRL.RobustRL
