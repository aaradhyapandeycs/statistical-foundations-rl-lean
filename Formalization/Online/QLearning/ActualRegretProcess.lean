import Formalization.Online.QLearning.ActualResidualCentering
import Formalization.Probability.ConditionalHoeffding

/-! A chronological martingale-difference process of the actual policy-gap
residuals, with deterministic stage weights retained through concentration. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance regretProcessStateMeasurable : MeasurableSpace State := ⊤
local instance regretProcessSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤
attribute [local instance] Classical.propDecidable

noncomputable def qLearningRegretChronologicalY {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (fallback : State) (w : Fin H → ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  if hn : n<K*H then
    let k : Fin K := ⟨n/H,(Nat.div_lt_iff_lt_mul hH).mpr hn⟩
    let h : Fin H := ⟨n%H,Nat.mod_lt n hH⟩
    w h * qLearningActualRegretResidual hH E bonus fallback k h sample
  else 0

noncomputable def qLearningRegretFiltration (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ) (fallback : State) :
    Filtration ℕ (⊤ : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H))) where
  seq n := onlineT3CommonPrefixSigma H K (K*H) hH fallback (qLearningActualEpisodePlanner hH E bonus) (n+1)
  mono' := by
    intro n m hnm
    exact onlineT3CommonPrefixSigma_mono H K (K*H) hH fallback
      (qLearningActualEpisodePlanner hH E bonus) (Nat.add_le_add_right hnm 1)
  le' _ := le_top

theorem qLearning_regretChronologicalY_adapted
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ) :
    Adapted (qLearningRegretFiltration H K hH E bonus fallback)
      (qLearningRegretChronologicalY (K:=K) hH E bonus fallback w) := by
  intro n
  by_cases hn : n<K*H
  · let k : Fin K := ⟨n/H,(Nat.div_lt_iff_lt_mul hH).mpr hn⟩
    let h : Fin H := ⟨n%H,Nat.mod_lt n hH⟩
    have hi : k.val*H+h.val=n := by simpa only [k,h,Nat.mul_comm] using Nat.div_add_mod n H
    have hm := qLearning_actualRegretResidual_measurable_next H K hH E bonus fallback k h
    rw [hi] at hm
    have heq : qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n =
        fun sample => w h*qLearningActualRegretResidual hH E bonus fallback k h sample := by
      funext sample
      simp only [qLearningRegretChronologicalY,dif_pos hn,k,h]
    rw [heq]
    exact (measurable_const.mul hm).stronglyMeasurable
  · have heq : qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n = 0 := by
      funext sample
      simp only [qLearningRegretChronologicalY,dif_neg hn,Pi.zero_apply]
    rw [heq]
    exact stronglyMeasurable_const

theorem qLearning_regretChronologicalY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State)
    (w : Fin H → ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    μ[qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n |
      onlineT3CommonPrefixSigma H K (K*H) hH fallback (qLearningActualEpisodePlanner hH E bonus) n] =ᵐ[μ] 0 := by
  dsimp only
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  let pref := onlineT3CommonPrefixSigma H K (K*H) hH fallback (qLearningActualEpisodePlanner hH E bonus) n
  by_cases hn : n<K*H
  · let k : Fin K := ⟨n/H,(Nat.div_lt_iff_lt_mul hH).mpr hn⟩
    let h : Fin H := ⟨n%H,Nat.mod_lt n hH⟩
    have hi : k.val*H+h.val=n := by simpa only [k,h,Nat.mul_comm] using Nat.div_add_mod n H
    have heq : qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n =
        (w h) • qLearningActualRegretResidual hH E bonus fallback k h := by
      funext sample
      simp only [qLearningRegretChronologicalY,dif_pos hn,k,h,Pi.smul_apply,smul_eq_mul]
    rw [heq]
    have hc := qLearning_actualRegretResidual_condExp_zero H K hH E ρ bonus fallback k h
    dsimp only at hc
    rw [hi] at hc
    have hl := condExp_smul (μ:=μ) (w h) (qLearningActualRegretResidual hH E bonus fallback k h) pref
    filter_upwards [hl,hc] with sample hs hz
    rw [hs]
    change w h * μ[qLearningActualRegretResidual hH E bonus fallback k h | pref] sample = 0
    change μ[qLearningActualRegretResidual hH E bonus fallback k h | pref] sample = 0 at hz
    rw [hz,mul_zero]
  · have heq : qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n = 0 := by
      funext sample
      simp only [qLearningRegretChronologicalY,dif_neg hn,Pi.zero_apply]
    rw [heq,condExp_zero]

theorem qLearning_regretChronologicalY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ)
    (M : ℝ≥0) (hweight : ∀ h, |w h| ≤ (M:ℝ)) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    |qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n sample| ≤ (M:ℝ)*(H:ℝ) := by
  dsimp only [qLearningRegretChronologicalY]
  split_ifs with hn
  · rw [abs_mul]
    exact mul_le_mul (hweight _) (qLearning_actualRegretResidual_abs_le hH E bonus fallback _ _ sample)
      (abs_nonneg _) M.coe_nonneg
  · simp only [abs_zero]
    positivity

theorem qLearning_regretChronologicalY_integral_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State)
    (w : Fin H → ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    ∫ sample, qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n sample ∂μ = 0 := by
  dsimp only
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm : onlineT3CommonPrefixSigma H K (K*H) hH fallback (qLearningActualEpisodePlanner hH E bonus) n ≤
      (⊤ : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H))) := le_top
  rw [← integral_condExp hm]
  have hc := qLearning_regretChronologicalY_condExp_zero H K hH E ρ bonus fallback w n
  simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hc

private theorem regretHoeffdingWidth (B : ℝ≥0) :
    ((‖(B:ℝ)-(-(B:ℝ))‖₊/2)^2)=B^2 := by
  apply NNReal.eq
  change (‖(B:ℝ)-(-(B:ℝ))‖/2)^2=(B:ℝ)^2
  rw [Real.norm_eq_abs,abs_of_nonneg (by have := B.coe_nonneg; linarith)]
  ring

private theorem regretHoeffdingWidth_mul (M : ℝ≥0) (H : ℕ) :
    ((‖(M:ℝ)*(H:ℝ)-(-((M:ℝ)*(H:ℝ)))‖₊/2)^2)=(M*(H:ℝ≥0))^2 := by
  simpa only [NNReal.coe_mul,NNReal.coe_natCast] using regretHoeffdingWidth (M*(H:ℝ≥0))

theorem qLearning_regretChronologicalY_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ)
    (M : ℝ≥0) (hweight : ∀ h, |w h| ≤ (M:ℝ)) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    HasSubgaussianMGF (qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n) ((M*(H:ℝ≥0))^2) μ := by
  dsimp only
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let ℱ := qLearningRegretFiltration H K hH E bonus fallback
  have hm := (qLearning_regretChronologicalY_adapted H K hH E bonus fallback w n).measurable.mono (ℱ.le n) le_rfl
  have hb : ∀ sample, qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n sample ∈
      Set.Icc (-((M:ℝ)*(H:ℝ))) ((M:ℝ)*(H:ℝ)) := by
    intro sample
    exact abs_le.mp (qLearning_regretChronologicalY_abs_le H K hH E bonus fallback w M hweight n sample)
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    (Filter.Eventually.of_forall hb) (qLearning_regretChronologicalY_integral_zero H K hH E ρ bonus fallback w n)
  simpa only [regretHoeffdingWidth_mul] using hs

theorem qLearning_regretChronologicalY_hasCondSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ)
    (M : ℝ≥0) (hweight : ∀ h, |w h| ≤ (M:ℝ)) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    let ℱ := qLearningRegretFiltration H K hH E bonus fallback
    HasCondSubgaussianMGF (ℱ n) (ℱ.le n)
      (qLearningRegretChronologicalY (K:=K) hH E bonus fallback w (n+1)) ((M*(H:ℝ≥0))^2) μ := by
  dsimp only
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let ℱ := qLearningRegretFiltration H K hH E bonus fallback
  have hm := (qLearning_regretChronologicalY_adapted H K hH E bonus fallback w (n+1)).measurable.mono (ℱ.le (n+1)) le_rfl
  have hb : ∀ sample, qLearningRegretChronologicalY (K:=K) hH E bonus fallback w (n+1) sample ∈
      Set.Icc (-((M:ℝ)*(H:ℝ))) ((M:ℝ)*(H:ℝ)) := by
    intro sample
    exact abs_le.mp (qLearning_regretChronologicalY_abs_le H K hH E bonus fallback w M hweight (n+1) sample)
  have hc : μ[qLearningRegretChronologicalY (K:=K) hH E bonus fallback w (n+1) | ℱ n] =ᵐ[μ] 0 :=
    qLearning_regretChronologicalY_condExp_zero H K hH E ρ bonus fallback w (n+1)
  have hs := StatisticalRL.hasCondSubgaussianMGF_of_pointwise_Icc_condExp_zero μ (ℱ n) (ℱ.le n)
    _ hm (-((M:ℝ)*(H:ℝ))) ((M:ℝ)*(H:ℝ)) hb hc
  simpa only [regretHoeffdingWidth_mul] using hs

/-- A real-law Azuma MGF for the actual signed weighted residual sum. -/
theorem qLearning_regretChronologicalSum_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ)
    (M : ℝ≥0) (hweight : ∀ h, |w h| ≤ (M:ℝ)) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    HasSubgaussianMGF (fun sample => ∑ n ∈ Finset.range (K*H),
      qLearningRegretChronologicalY (K:=K) hH E bonus fallback w n sample)
      (((K*H:ℕ):ℝ≥0)*(M*(H:ℝ≥0))^2) μ := by
  dsimp only
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hs := HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF (μ:=μ)
    (cY:=fun _ => (M*(H:ℝ≥0))^2)
    (qLearning_regretChronologicalY_adapted H K hH E bonus fallback w)
    (qLearning_regretChronologicalY_hasSubgaussianMGF H K hH E ρ bonus fallback w M hweight 0) (K*H)
    (fun n _hn => qLearning_regretChronologicalY_hasCondSubgaussianMGF H K hH E ρ bonus fallback w M hweight n)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hs

end StatisticalRL.OnlineRL
