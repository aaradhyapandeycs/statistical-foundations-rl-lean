import Mathlib
import Formalization.RobustRL.TVClip

/-! TV proof source-specific algebra for the TV branch of
`lemma:dual-form`. It identifies the source scalar objective at
`α = Vmin + λ` with nominal expectation minus the finite positive-part
threshold certificate. It does not prove strong duality or attainment. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.ClipThreshold

variable {State : Type*} [Fintype State] [Nonempty State]

/-- Shifted nonnegative cost relative to an attained source minimum. -/
def shiftedCost (V : State → ℝ) (vmin : ℝ) : State → ℝ :=
  fun s ↦ V s - vmin

/-- The exact source TV scalar objective, keeping the minimum of the clipped
vector explicit. -/
noncomputable def sourceTVScalarObjective
    (p : State → ℝ) (V : State → ℝ) (σ α : ℝ) : ℝ :=
  (∑ s, p s * StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α s) -
    σ * (α - Finset.univ.inf' Finset.univ_nonempty
      (StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α))

/-- Finite threshold penalty on the shifted cost `V - vmin`. -/
def positivePartThresholdCertificate
    (p : State → ℝ) (V : State → ℝ) (vmin σ lam : ℝ) : ℝ :=
  σ * lam + ∑ s, p s *
    max (shiftedCost V vmin s - lam) 0

/-- The nominal source expectation of `V`. -/
def nominalValue (p V : State → ℝ) : ℝ := ∑ s, p s * V s

/-- At every scalar in the source interval, setting `λ=α−Vmin` rewrites the
exact TV dual objective as nominal value minus the positive-part threshold
certificate. The lower endpoint gives `λ=0`; the upper endpoint gives
`λ=Vmax−Vmin`. The source's nonnegativity, probability normalization,
extremum, and interval assumptions are retained explicitly. -/
theorem sourceTVScalar_eq_nominal_sub_thresholdCertificate
    (p V : State → ℝ) (vmin vmax σ α : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax)
    (hαlo : vmin ≤ α) (hαhi : α ≤ vmax) :
    sourceTVScalarObjective p V σ α =
      nominalValue p V -
        positivePartThresholdCertificate p V vmin σ (α - vmin) := by
  classical
  let lam := α - vmin
  have hlamnonneg : 0 ≤ lam := by dsimp [lam]; linarith
  have hαeq : vmin + lam = α := by dsimp [lam]; ring
  have hclipPoint (s : State) :
      StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α s =
        vmin + min (shiftedCost V vmin s) lam := by
    rw [StatisticalRL.RobustRL.TVProof.Clip.clipAbove_eq_min]
    by_cases h : shiftedCost V vmin s ≤ lam
    · have hVα : V s ≤ α := by dsimp [shiftedCost, lam] at *; linarith
      rw [min_eq_left hVα, min_eq_left h]
      dsimp [shiftedCost]
      ring
    · have hcost : lam ≤ shiftedCost V vmin s := le_of_not_ge h
      have hαV : α ≤ V s := by dsimp [shiftedCost, lam] at *; linarith
      rw [min_eq_right hαV, min_eq_right hcost]
      ring
  have hclipMinimum :
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α) = vmin := by
    obtain ⟨hbound, ⟨s, hs⟩⟩ :=
      StatisticalRL.RobustRL.TVProof.Clip.clipAbove_minimum
        V α vmin hVmin hVminAttained hαlo
    apply le_antisymm
    · calc
        Finset.univ.inf' Finset.univ_nonempty
            (StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α) ≤
          StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α s :=
            Finset.inf'_le (s := Finset.univ)
              (f := StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α)
              (Finset.mem_univ s)
        _ = vmin := hs
    · apply Finset.le_inf'
      intro s hs
      exact hbound s
  have hclipSum :
      (∑ s, p s * StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α s) =
        vmin + ∑ s, p s * min (shiftedCost V vmin s) lam := by
    calc
      (∑ s, p s * StatisticalRL.RobustRL.TVProof.Clip.clipAbove V α s) =
          (∑ s, p s * (vmin + min (shiftedCost V vmin s) lam)) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hclipPoint s]
      _ = vmin * (∑ s, p s) +
          ∑ s, p s * min (shiftedCost V vmin s) lam := by
        calc
          _ = ∑ s, (p s * vmin + p s * min (shiftedCost V vmin s) lam) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = (∑ s, p s * vmin) +
              ∑ s, p s * min (shiftedCost V vmin s) lam := by
            rw [Finset.sum_add_distrib]
          _ = (∑ s, p s) * vmin +
              ∑ s, p s * min (shiftedCost V vmin s) lam := by
            rw [← Finset.sum_mul]
          _ = vmin * (∑ s, p s) +
              ∑ s, p s * min (shiftedCost V vmin s) lam := by ring
      _ = vmin + ∑ s, p s * min (shiftedCost V vmin s) lam := by
        rw [hpSum]
        ring
  have hnominal :
      nominalValue p V = vmin + ∑ s, p s * shiftedCost V vmin s := by
    unfold nominalValue shiftedCost
    calc
      (∑ s, p s * V s) = ∑ s, p s * (vmin + (V s - vmin)) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = vmin * (∑ s, p s) + ∑ s, p s * (V s - vmin) := by
        calc
          _ = ∑ s, (p s * vmin + p s * (V s - vmin)) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = (∑ s, p s * vmin) + ∑ s, p s * (V s - vmin) := by
            rw [Finset.sum_add_distrib]
          _ = (∑ s, p s) * vmin + ∑ s, p s * (V s - vmin) := by
            rw [← Finset.sum_mul]
          _ = vmin * (∑ s, p s) + ∑ s, p s * (V s - vmin) := by ring
      _ = vmin + ∑ s, p s * (V s - vmin) := by
        rw [hpSum]
        ring
  have hcostPoint (s : State) :
      shiftedCost V vmin s =
        min (shiftedCost V vmin s) lam +
          max (shiftedCost V vmin s - lam) 0 := by
    by_cases h : shiftedCost V vmin s ≤ lam
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · have h' : lam ≤ shiftedCost V vmin s := le_of_not_ge h
      rw [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]
      ring
  have hcostSum :
      (∑ s, p s * shiftedCost V vmin s) =
        (∑ s, p s * min (shiftedCost V vmin s) lam) +
          ∑ s, p s * max (shiftedCost V vmin s - lam) 0 := by
    calc
      (∑ s, p s * shiftedCost V vmin s) =
          ∑ s, p s * (min (shiftedCost V vmin s) lam +
            max (shiftedCost V vmin s - lam) 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact congrArg (fun x : ℝ => p s * x) (hcostPoint s)
      _ = (∑ s, p s * min (shiftedCost V vmin s) lam) +
          ∑ s, p s * max (shiftedCost V vmin s - lam) 0 := by
        calc
          _ = ∑ s, (p s * min (shiftedCost V vmin s) lam +
              p s * max (shiftedCost V vmin s - lam) 0) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = (∑ s, p s * min (shiftedCost V vmin s) lam) +
              ∑ s, p s * max (shiftedCost V vmin s - lam) 0 := by
            rw [Finset.sum_add_distrib]
  unfold sourceTVScalarObjective positivePartThresholdCertificate
  dsimp [lam] at hclipSum hcostSum
  rw [hclipMinimum, hclipSum, hnominal, hcostSum]
  ring

end StatisticalRL.RobustRL.TVProof.ClipThreshold
