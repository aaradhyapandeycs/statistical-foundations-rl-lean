import Formalization.Online.QLearning.ActualJointRegretEvent
import Formalization.Online.QLearning.OnlineQStageUnroll
import Formalization.Online.QLearning.OnlineQStageWeights
import Formalization.Online.QLearning.OnlineQResidualReindex

/-! Actual horizon unroll, retaining exact signed stage weights through the
real-law concentration argument. Generic helpers are only algebra inputs. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance horizonRegretStateMeasurable : MeasurableSpace State := ⊤
local instance horizonRegretSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤
attribute [local instance] Classical.propDecidable

private theorem sum_fin_range (K : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin K, f k.val) = ∑ k ∈ Finset.range K, f k := by
  apply Finset.sum_bij (fun k _ => k.val)
  · intro k hk; exact Finset.mem_range.mpr k.isLt
  · intro k hk j hj he; exact Fin.ext he
  · intro k hk; exact ⟨⟨k,Finset.mem_range.mp hk⟩,Finset.mem_univ _,rfl⟩
  · intro k hk; rfl

/-- Actual source regret after unrolling the true state-selector recursion.
Every signed residual keeps its source geometric coefficient. -/
theorem qLearning_actualRegret_horizon_on_good {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ 2 (initial,path)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let B := (Fintype.card (State×Action):ℝ)*(H:ℝ) +
      16*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ)
    let w := fun h : Fin H => (1+1/(H:ℝ))^h.val
    qLearningActualRegret hH E bonus initial fallback path ≤
      Real.exp 1*(H:ℝ)*B +
      ∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n (initial,path) := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let B := (Fintype.card (State×Action):ℝ)*(H:ℝ) +
      16*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ)
  let c : ℝ := 1+1/(H:ℝ)
  let w := fun h : Fin H => c^h.val
  let d := qLearningActualEpisodePolicyError hH E bonus initial fallback path
  let r : ℕ → ℕ → ℝ := fun k h => if hk : k<K then if hh : h<H then
    qLearningActualRegretResidual hH E bonus fallback ⟨k,hk⟩ ⟨h,hh⟩ (initial,path) else 0 else 0
  let R := fun h : ℕ => ∑ k ∈ Finset.range K, r k h
  have hc : 0≤c := by dsimp [c]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hR (h : ℕ) (hh : h<H) : R h =
      ∑ k : Fin K, qLearningActualRegretResidual hH E bonus fallback k ⟨h,hh⟩ (initial,path) := by
    dsimp only [R]
    rw [← sum_fin_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [r,dif_pos k.isLt,dif_pos hh]
  have hstep (h : ℕ) (hh : h<H) : d h ≤ c*d (h+1)+B+R h := by
    have hs := qLearning_actual_episodePolicyError_stage_bound hH hK E initial fallback δ 2
      hδ hδ1 (by norm_num) path hgood ⟨h,hh⟩
    rw [hR h hh]
    dsimp only [d,c,B,bonus,L] at *
    nlinarith
  have hu := StatisticalRL.OnlineQStageAlgebraPrivate.signedStageRecursionUnroll H c hc d (fun _ => B) R hstep
  have hz : d H=0 := qLearning_actualEpisodePolicyError_terminal hH E bonus initial fallback path
  rw [hz,mul_zero,zero_add] at hu
  simp only [mul_add,Finset.sum_add_distrib] at hu
  have hcharge : (∑ h ∈ Finset.range H, c^h*B) ≤ Real.exp 1*(H:ℝ)*B := by
    calc
      _ ≤ ∑ _h ∈ Finset.range H, Real.exp 1*B := by
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_right
          (StatisticalRL.OnlineQStageWeightsPrivate.geometricStageWeight_le_exp H h hH
            (Finset.mem_range.mp hh).le) hB
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have hflat : (∑ h ∈ Finset.range H, c^h*R h) =
      ∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n (initial,path) := by
    rw [StatisticalRL.OnlineQResidualReindexPrivate.stageWeightedResidual_chronological H K hH c r]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have hk : n/H<K := (Nat.div_lt_iff_lt_mul hH).mpr hn'
    have hh : n%H<H := Nat.mod_lt n hH
    simp only [r,dif_pos hk,dif_pos hh,qLearningRegretChronologicalY,dif_pos hn',w]
  have hreg : qLearningActualRegret hH E bonus initial fallback path ≤ d 0 :=
    qLearning_actualRegret_le_episodePolicyError hH E initial fallback δ 2 path hgood
  change qLearningActualRegret hH E bonus initial fallback path ≤
    Real.exp 1*(H:ℝ)*B +
      ∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n (initial,path)
  rw [hflat] at hu
  linarith

/-- Fully unconditional actual-law bound before absorbing the lower-order
initialization term. The algorithm uses exactly cb=2 and log(SAT/δ). -/
theorem qLearning_actualRegret_explicit_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let B := (Fintype.card (State×Action):ℝ)*(H:ℝ) +
      16*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ)
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    1-δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
      qLearningActualRegret hH E bonus sample.1 fallback sample.2 ≤ Real.exp 1*(H:ℝ)*B +
        Real.sqrt (2*((K:ℝ)*(H:ℝ)*(Real.exp 1*(H:ℝ))^2)*Real.log (4/δ))} := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  let w := fun h : Fin H => (1+1/(H:ℝ))^h.val
  let M := (Real.exp 1).toNNReal
  have hM : 0<M := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hMc : (M:ℝ)=Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hw (h : Fin H) : |w h|≤(M:ℝ) := by
    rw [hMc,abs_of_nonneg (by dsimp [w]; positivity)]
    exact StatisticalRL.OnlineQStageWeightsPrivate.geometricStageWeight_le_exp H h.val hH h.isLt.le
  have hj := qLearning_actual_jointRegretEvent_confidence H K hH hK E ρ fallback δ hδ hδ1 w M hM hw
  apply lt_of_lt_of_le hj
  apply measureReal_mono _ (measure_ne_top μ _)
  intro sample hs
  have hr := qLearning_actualRegret_horizon_on_good hH hK E sample.1 fallback δ hδ hδ1 sample.2 hs.1
  have hx := (abs_le.mp hs.2).2
  rw [hMc] at hx
  exact hr.trans (add_le_add_right hx _)

end StatisticalRL.OnlineRL
