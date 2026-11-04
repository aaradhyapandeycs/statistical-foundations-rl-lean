import Formalization.Online.Regret.Gap.OnlineJ1ActualVariance

/-! Actual-law variance and gap proof component: OnlineJ1ActualVarianceSum.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
theorem onlineJ1GapSquareSum_eq_actualT6Difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) :
    ∑ n ∈ Finset.range (K * H),
        onlineJ1PaddedRowGapSquare H K hH E fallback
          (Real.log (1 / δ)) c₁ c₂ n (initial, path) =
      onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold onlineActualT6Difference
  let f : Fin H → Fin K → ℝ := fun h k =>
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
  change (∑ n ∈ Finset.range (K * H),
    onlineJ1PaddedRowGapSquare H K hH E fallback
      (Real.log (1 / δ)) c₁ c₂ n (initial, path)) =
    ∑ h : Fin H, ∑ k : Fin K, f h k
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_bij
    (fun n hn =>
      ((⟨n % H, Nat.mod_lt n hH⟩ : Fin H),
       (⟨n / H, (onlineT3NaturalTime_decomposition H hH K n
         (Finset.mem_range.mp hn)).1⟩ : Fin K)))
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn m hm he
    have hdecN := onlineT3NaturalTime_decomposition H hH K n (Finset.mem_range.mp hn)
    have hdecM := onlineT3NaturalTime_decomposition H hH K m (Finset.mem_range.mp hm)
    have hmod : n % H = m % H := congrArg Fin.val (congrArg Prod.fst he)
    have hdiv : n / H = m / H := congrArg Fin.val (congrArg Prod.snd he)
    calc
      n = n / H * H + n % H := hdecN.2.2
      _ = m / H * H + m % H := by rw [hdiv, hmod]
      _ = m := hdecM.2.2.symm
  · intro ⟨h, k⟩ hp
    refine ⟨k.val * H + h.val, Finset.mem_range.mpr ?_, ?_⟩
    · calc
        k.val * H + h.val < (k.val + 1) * H := by
          rw [Nat.succ_mul]
          exact Nat.add_lt_add_left h.isLt _
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
    · apply Prod.ext
      · apply Fin.ext
        have hhmod : (k.val * H + h.val) % H = h.val := by
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
        exact hhmod
      · apply Fin.ext
        have hhdiv : (k.val * H + h.val) / H = k.val := by
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_div_left]
          · simp [Nat.div_eq_of_lt h.isLt]
          · exact hH
        exact hhdiv
  · intro n hn
    have hdec := onlineT3NaturalTime_decomposition H hH K n (Finset.mem_range.mp hn)
    let k' : Fin K := ⟨n / H, hdec.1⟩
    let h' : Fin H := ⟨n % H, hdec.2.1⟩
    have hrow := onlineJ1PaddedRowGapSquare_eq_actualT6DifferenceTerm H K hH E initial fallback path
      k' h' δ c₁ c₂
    calc
      onlineJ1PaddedRowGapSquare H K hH E fallback
          (Real.log (1 / δ)) c₁ c₂ n (initial, path) =
        onlineJ1PaddedRowGapSquare H K hH E fallback
          (Real.log (1 / δ)) c₁ c₂ (k'.val * H + h'.val) (initial, path) := by
            congr 1
            exact hdec.2.2
      _ = f h' k' := by simpa [f] using hrow

end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1ActualSumState : MeasurableSpace State := ⊤
noncomputable local instance j1ActualSumSample (H K : ℕ) : MeasurableSpace
  ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineJ1PredictableSecondMomentSum_le_actualT6Difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (onlineJ1PaddedY H K hH E fallback (Real.log (1 / δ)) c₁ c₂) (K * H) sample ≤
      onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  have hs := onlineJ1PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback
    (Real.log (1 / δ)) c₁ c₂ (K * H)
  filter_upwards [hs] with sample hs
  rw [hs]
  calc
    _ ≤ ∑ n ∈ Finset.range (K * H), onlineJ1PaddedRowGapSquare H K hH E fallback
        (Real.log (1 / δ)) c₁ c₂ n sample :=
      onlineJ1RowVarianceSum_le_gapSquare H K hH E fallback (Real.log (1 / δ)) c₁ c₂ (K * H) sample
    _ = _ := onlineJ1GapSquareSum_eq_actualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
end StatisticalRL.OnlineRL
