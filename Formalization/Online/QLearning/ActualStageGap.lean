import Formalization.Online.QLearning.ActualStagePropagation

/-! Actual optimistic continuation gaps for the Q-learning propagation step. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

noncomputable def qLearningActualStageGap {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (e : ℕ) : ℝ :=
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let next := (hist.map Prod.snd).getD (e*H+h.val) fallback
  qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus initial fallback path (e*H))
    (h.val+1) next - qLearningTrueOptimalNext E (h,rows e) next

theorem qLearning_actualStageGap_nonneg {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path))
    (h : Fin H) (e : ℕ) (he : e<K) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    0 ≤ qLearningActualStageGap hH E bonus initial fallback path h e := by
  classical
  dsimp only [qLearningSourceOptimismGood] at hgood
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let next := (hist.map Prod.snd).getD (e*H+h.val) fallback
  change 0 ≤ qLearningChronologicalValue hH E
    (qLearningActualTableAt hH E bonus initial fallback path (e*H)) (h.val+1) next -
    qLearningTrueOptimalNext E (h,rows e) next
  apply sub_nonneg.mpr
  by_cases hh : h.val+1 < H
  · let hnext : Fin H := ⟨h.val+1,hh⟩
    have hv := hgood.2.2 ⟨e,he⟩ hnext next
    simpa [qLearningTrueOptimalNext, hnext, bonus, L] using hv
  · have hlast : h.val+1=H := by have hlt := h.isLt; omega
    have hz := qLearningTrueOptimalNext_last_zero E (h,rows e) hlast
    simp [qLearningChronologicalValue,hh,hz]

theorem qLearning_actualStageGap_propagation {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path)) (h : Fin H) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    let gap := qLearningActualStageGap hH E bonus initial fallback path h
    (∑ k : Fin K,
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
      let t := visits.length
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) ≤
      (1+1/(H:ℝ))*(∑ e : Fin K, gap e.val) := by
  apply qLearning_actualStagePropagation_budget
  intro e he
  exact qLearning_actualStageGap_nonneg hH E initial fallback δ cb path hgood h e he
end StatisticalRL.OnlineRL
