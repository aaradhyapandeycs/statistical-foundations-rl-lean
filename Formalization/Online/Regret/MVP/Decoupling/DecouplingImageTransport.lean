import Formalization.Online.SourceOptimism.TranscriptEventTransport

/-! Conditional image transport. The pointwise rank-to-path bridge
and the rank-event probability must be supplied by separately proved results;
this is not a source confidence theorem. No inverse-image decoder is used. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance imageTransportState : MeasurableSpace State := ⊤
noncomputable local instance imageTransportStateDec : DecidableEq State := Classical.decEq State
noncomputable local instance imageTransportActionDec : DecidableEq Action := Classical.decEq Action
local instance imageTransportTranscript (H K : ℕ) : MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance imageTransportAtom (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

theorem onlineStack_rank_event_to_sequential_image_conditional
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n : ℕ) (hn : n≤K*H)
    (R : Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)))
    (A : Set ((Fin K → State) × OnlineOutcomePath State n)) (p : ℝ) (hp : 0<p)
    (hR : 1-p/2 ≤ (onlineMDPInitialStackLaw E ρ K).real R)
    (hpoint : ∀ data sample,
      (data.1,onlineStackHistory (onlineEpisodicChoose H K hH data.1 fallback planner)
        (onlineFiniteStackExtend K fallback data.2) n) =
      (sample.1,onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
        n [] sample.2) → data∈R → sample∈A) :
    1-p < (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure.real A := by
  classical
  let μ := onlineMDPInitialStackLaw E ρ K
  let ν := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure
  let observe := fun data : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (data.1,onlineStackHistory (onlineEpisodicChoose H K hH data.1 fallback planner)
      (onlineFiniteStackExtend K fallback data.2) n)
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State n =>
    (sample.1,onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2)
  let T := encode '' A
  haveI : IsProbabilityMeasure μ := by dsimp [μ,onlineMDPInitialStackLaw,onlineMDPStackLaw]; infer_instance
  have hmap : μ.map observe = ν.map encode :=
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner n hn
  have hrange : MeasurableSet (Set.range encode) := (Set.to_countable _).measurableSet
  have hsupport' : ∀ᵐ z ∂μ.map observe, z∈Set.range encode := by
    rw [hmap]
    exact ae_map_mem_range encode hrange ν
  have hsupport : ∀ᵐ data ∂μ, observe data∈Set.range encode :=
    ae_of_ae_map (measurable_of_countable observe).aemeasurable hsupport'
  have hae : R ≤ᵐ[μ] observe ⁻¹' T := by
    filter_upwards [hsupport] with data hdata hRdata
    obtain ⟨sample, hs⟩ := hdata
    exact ⟨sample, hpoint data sample hs.symm hRdata, hs⟩
  have hmono : μ.real R ≤ μ.real (observe ⁻¹' T) :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)
  have hevent := onlineStack_sequential_transcriptEvent_real_eq H K hH E ρ fallback planner n hn T
  have hinj : Function.Injective encode := onlineRealizedPath_reset_transcript_injective H K hH fallback planner n
  have hpre : encode ⁻¹' T=A := Set.preimage_image_eq A hinj
  change μ.real (observe ⁻¹' T)=ν.real (encode ⁻¹' T) at hevent
  rw [hpre] at hevent
  change 1-p/2 ≤ μ.real R at hR
  change 1-p < ν.real A
  linarith
end StatisticalRL.OnlineRL
