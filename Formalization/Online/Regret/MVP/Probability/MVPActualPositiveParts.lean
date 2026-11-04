import Formalization.Online.Regret.MVP.Probability.MVPAllMasksUniform
import Formalization.Online.Regret.MVP.Probability.MVPPositiveMaskProjection

/-! Pointwise projection from all fixed masks to actual positive row errors. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_allMasks_imply_positiveParts {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (hnpos : 0<n)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (peels : ℕ) (ε : ℝ) (hL : 0 ≤ Real.log (2*peels/ε))
    (data : Samples State Action H K)
    (hgood : ∀ mask : Fin H → State → Action → Bool,
      data ∈ mvpFixedMaskBatchEvent E K n hn hnpos mask V peels ε) :
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      max ((FiniteDistribution.empiricalRow n hnpos (fun j => data ((h,s,a),mvpBatchIndex K n hn j))).expectation
              (V h s a (futureData h K data)) -
            ((E h).transition s a).expectation (V h s a (futureData h K data))) 0) ≤
      (Real.sqrt (8 * max
          ((n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (V h s a (futureData h K data)))
          (((n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / n := by
  classical
  let Row := Fin H × State × Action
  let x : Row → ℝ := fun r =>
    (FiniteDistribution.empiricalRow n hnpos (fun j => data ((r.1,r.2.1,r.2.2),mvpBatchIndex K n hn j))).expectation
      (V r.1 r.2.1 r.2.2 (futureData r.1 K data)) -
      ((E r.1).transition r.2.1 r.2.2).expectation (V r.1 r.2.1 r.2.2 (futureData r.1 K data))
  let variance : Row → ℝ := fun r =>
    ((E r.1).transition r.2.1 r.2.2).variance (V r.1 r.2.1 r.2.2 (futureData r.1 K data))
  let floor : ℝ := ((n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels
  let L := Real.log (2*peels/ε)
  let linear : ℝ := (4/3) * H * L
  have hmask : ∀ t : Finset Row, t ⊆ Finset.univ →
      |∑ r ∈ t, x r| ≤ (Real.sqrt (8 * max ((n : ℝ) * ∑ r ∈ t, variance r) floor * L) + linear) / n := by
    intro t ht
    let mask : Fin H → State → Action → Bool := fun h s a => decide ((h,s,a) ∈ t)
    have ht' := hgood mask
    simp only [mvpFixedMaskBatchEvent, Set.mem_setOf_eq] at ht'
    have hxx : (∑ r ∈ t, x r) = ∑ r : Row, if r ∈ t then x r else 0 := by
      rw [← Finset.sum_filter]
      simp
    have hvv : (∑ r ∈ t, variance r) = ∑ r : Row, if r ∈ t then variance r else 0 := by
      rw [← Finset.sum_filter]
      simp
    rw [hxx, hvv]
    dsimp only [Row]
    simp only [Fintype.sum_prod_type]
    simpa only [mask, decide_eq_true_eq, x, variance, floor, L, linear] using ht'
  have hp := mvp_positiveParts_of_fixedMaskBounds (Finset.univ : Finset Row) x variance
    (n : ℝ) floor L linear (by exact_mod_cast hnpos) hL
    (fun r _ => ((E r.1).transition r.2.1 r.2.2).variance_nonneg _) hmask
  dsimp only [Row] at hp
  simp only [Fintype.sum_prod_type] at hp
  simpa only [x, variance, floor, L, linear] using hp
end StatisticalRL.FiniteHorizonGenerative
