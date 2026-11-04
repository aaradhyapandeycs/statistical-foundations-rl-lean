import Formalization.Online.Regret.Joint.OnlineT56SourceConfidence
import Formalization.Online.Regret.Main.OnlineUCBVIActualT0Closure
import Formalization.Online.Regret.Main.OnlineUCBVIActualRegret

/-! Definitions and scalar helpers for the corrected actual-law UCBVI regret bound, with fixed deterministic ties and finite zero-count completion. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mainStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mainSampleMeasurable (H K : ℕ) :
  MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

noncomputable def onlineUCBVIRegretRate (S A H K : ℕ) (δ : ℝ) : ℝ :=
  let I := onlineW1SourceIota S A H K (onlineSourceOptimismDeltaPrime δ S A H K)
  20 * (Real.sqrt ((S : ℝ) * A * H^3 * K) + (S : ℝ)^2 * A * H^3) * (1 + I)

noncomputable def onlineUCBVIRegretRateEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ : ℝ) : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' 4 16) ≤
      onlineUCBVIRegretRate (Fintype.card State) (Fintype.card Action) H K δ}

theorem onlineMain_large_scalar (x b I T0 : ℝ)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (hI : 0 ≤ I)
    (hT0 : T0 ≤ 20 * x * I + 15 * b * I) :
    T0 ≤ 20 * (x + b) * (1 + I) := by
  have hxI := mul_nonneg hx hI
  have hbI := mul_nonneg hb hI
  nlinarith only [hT0, hx, hb, hxI, hbI]

theorem onlineMain_small_scalar (S A H K I : ℝ)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) (hK : 0 ≤ K) (hI : 0 ≤ I)
    (hsmall : K ≤ S * A * H^2 * I) :
    K * H ≤ 20 * (Real.sqrt (S * A * H^3 * K) + S^2 * A * H^3) * (1 + I) := by
  have hH0 : 0 ≤ H := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hb : 0 ≤ S^2 * A * H^3 := by positivity
  have hr : 0 ≤ Real.sqrt (S * A * H^3 * K) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hsmall hH0
  have hs2 : S ≤ S^2 := by nlinarith [sq_nonneg (S - 1)]
  have hm := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ A * H^3 * I by positivity)
  have hbi := mul_nonneg hb hI
  have hri := mul_nonneg hr hI
  nlinarith only [hmul, hm, hb, hr, hbi, hri]

theorem onlineMain_one_scalar (S A H : ℝ)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) :
    H ≤ 20 * (Real.sqrt (S * A * H^3) + S^2 * A * H^3) := by
  have hs2 : 1 ≤ S^2 := by nlinarith [sq_nonneg (S - 1)]
  have hfactor : 1 ≤ S^2 * A * H^2 := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ S^2 * A * H^2 := by gcongr <;> nlinarith
  have hm := mul_le_mul_of_nonneg_right hfactor (show 0 ≤ H by linarith)
  have hr := Real.sqrt_nonneg (S * A * H^3)
  have hb : 0 ≤ S^2 * A * H^3 := by positivity
  nlinarith only [hm, hr, hb]

theorem onlineMain_allocated_failure_le_delta (S A H K : ℕ) (δ : ℝ)
    (hS : 0 < S) (hA : 0 < A) (hH : 0 < H) (hK : 0 < K) (hδ : 0 < δ) :
    39 * (S : ℝ)^2 * A * H^2 * K * onlineSourceOptimismDeltaPrime δ S A H K ≤ δ := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hh : (0 : ℝ) < H := by exact_mod_cast hH
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  unfold onlineSourceOptimismDeltaPrime
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)).2
  have hAK : 1 ≤ (A : ℝ) * K := by nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hK1)]
  have hmul := mul_le_mul_of_nonneg_right hAK (show 0 ≤ (S : ℝ)^2 * A * H^2 * K * δ by positivity)
  have hbase : 0 ≤ (S : ℝ)^2 * A * H^2 * K * δ := by positivity
  nlinarith only [hmul, hbase]

end StatisticalRL.OnlineRL
