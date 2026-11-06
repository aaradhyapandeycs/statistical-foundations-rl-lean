import Formalization.Online.QLearning.ActualHorizonRegret
import Formalization.Online.QLearning.RegretRadiusAlgebra
import Formalization.Online.QLearning.OnlineQRegretAbsorption

/-! Source Theorem 5.16 (onlineRL.tex:1911–1922), with explicit universal
constants and logarithm. Uses the fixed greedy tie/initial-V completion already
disclosed for the actual algorithm. The corrected shifted-beta inequality and
signed stage weights are preserved in its proof, without editing the source. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance regretRateStateMeasurable : MeasurableSpace State := ⊤
local instance regretRateSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

/-- The actual Q-learning regret rate with fixed cb=2, the literal source
bonus logarithm, and strict confidence >1−δ under its actual sequential law.
The rate's universal constant is max(1,19e), and its logarithmic factor is
1+log(4SAT/δ). No confidence, Bellman, counting, or martingale certificates
are theorem premises. -/
theorem qLearning_actualRegret_rate_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let Λ := 1+Real.log (4*((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ))/δ)
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    1-δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
      qLearningActualRegret hH E bonus sample.1 fallback sample.2 ≤
        max 1 (19*Real.exp 1)*Real.sqrt ((H:ℝ)^5*(Fintype.card (State×Action):ℝ)*(K:ℝ)*Λ)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let N : ℝ := Fintype.card (State×Action)
  let x : ℝ := (Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)
  let L := Real.log (x/δ)
  let Λ := 1+Real.log (4*x/δ)
  let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  have hH1 : (1:ℝ)≤H := by exact_mod_cast hH
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card (State×Action))
  have hcard : (1:ℝ)≤Fintype.card (OnlineMDPRow State Action H) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (OnlineMDPRow State Action H))
  have hk1 : (1:ℝ)≤K := by exact_mod_cast hK
  have hx : 1≤x := one_le_mul_of_one_le_of_one_le hcard hk1
  have hx0 : 0<x := by linarith
  have hfour : 1≤4*x/δ := by rw [le_div_iff₀ hδ]; nlinarith
  have hlogfour : 0≤Real.log (4*x/δ) := Real.log_nonneg hfour
  have hΛ : 1≤Λ := by dsimp [Λ]; linarith
  have hlogCompare := Real.log_le_log (div_pos hx0 hδ)
    (div_le_div_of_nonneg_right (show x≤4*x by linarith) hδ.le)
  have hLL : L≤Λ := by dsimp [L,Λ]; linarith
  have htailCompare := Real.log_le_log (div_pos (by norm_num : (0:ℝ)<4) hδ)
    (div_le_div_of_nonneg_right (show (4:ℝ)≤4*x by nlinarith) hδ.le)
  have hℓΛ : Real.log (4/δ)≤Λ := by dsimp [Λ]; linarith
  have hcoarse := qLearning_regret_radius_coarse (H:ℝ) N (K:ℝ) L (Real.log (4/δ)) Λ (Real.exp 1)
    hH1 hN (Nat.cast_nonneg K) hΛ hLL hℓΛ (Real.exp_pos _).le
  have hp := qLearning_actualRegret_explicit_confidence H K hH hK E ρ fallback δ hδ hδ1
  apply lt_of_lt_of_le hp
  apply measureReal_mono _ (measure_ne_top μ _)
  intro sample hs
  have hmain : qLearningActualRegret hH E bonus sample.1 fallback sample.2 ≤
      (18*Real.exp 1)*Real.sqrt ((H:ℝ)^5*N*(K:ℝ)*Λ)+Real.exp 1*(H:ℝ)^2*N :=
    hs.trans hcoarse
  have htrivial : qLearningActualRegret hH E bonus sample.1 fallback sample.2 ≤ (H:ℝ)*(K:ℝ) := by
    calc
      _ ≤ (K:ℝ)*(H:ℝ) := (qLearning_actualRegret_mem_Icc hH E bonus sample.1 fallback sample.2).2
      _ = _ := mul_comm _ _
  have ha := StatisticalRL.OnlineQRegretAlgebraPrivate.regretLowerOrderAbsorption
    (qLearningActualRegret hH E bonus sample.1 fallback sample.2) (H:ℝ) N 1 (K:ℝ) Λ
    (18*Real.exp 1) (Real.exp 1) hH1 hN (by norm_num) (Nat.cast_nonneg K) hΛ
    (by positivity) (Real.exp_pos _).le htrivial (by simpa only [mul_one] using hmain)
  have he : 18*Real.exp 1+Real.exp 1=19*Real.exp 1 := by ring
  simpa only [mul_one,he,mul_assoc] using ha

end StatisticalRL.OnlineRL
