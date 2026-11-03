import Formalization.Online.SourceOptimism.FiniteAtomSigmaTop
import Formalization.Online.SourceOptimism.StackSequentialLawEquality

/-! Transport between the default and top measurable spaces for the finite
reset/path atom, including the stack/sequential law wrapper. The staged counterpart
compiled; this canonical import layout requires verification. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineDefaultTransportStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance onlineDefaultTransportStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineDefaultTransportActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action
local instance onlineDefaultTransportTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤

/-- The atom carrier used by the staged reset/path law comparison. -/
abbrev OnlineResetPathAtom (State : Type*) (K n : ℕ) :=
  (Fin K → State) × OnlineOutcomePath State n

/-- The default measurable instance on the actual finite reset/path atom is
exactly the top sigma algebra. This is a conclusion from the compiled
finite-Pi/product helper, not a local assumption on the atom carrier. -/
theorem onlineResetPathAtom_defaultMeasurableSpace_eq_top (K n : ℕ) :
    (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) = ⊤ := by
  letI : MeasurableSpace State := ⊤
  have hdefault :
      (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) = ⊤ := by
    haveI : MeasurableSingletonClass (OnlineResetPathAtom State K n) := inferInstance
    apply le_antisymm le_top
    intro s _
    exact (Set.to_countable s).measurableSet
  have hexplicit := onlineFiniteResetPathProductSigma_eq_top (State := State) K n
  have hbridge :
      (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) =
        onlineFiniteResetPathProductSigma (State := State)
          (⊤ : MeasurableSpace State) K n :=
    hdefault.trans hexplicit.symm
  exact hbridge.trans hexplicit

/-- Measurability is invariant under an equality of source measurable spaces.
This is the explicit transport step needed when a consumer is elaborated with
the default Pi/product instance but a staged comparison uses `⊤`. -/
theorem measurable_iff_of_sourceMeasurableSpace_eq
    {α β : Type*} (m₁ m₂ : MeasurableSpace α) (mβ : MeasurableSpace β)
    (h : m₁ = m₂) (f : α → β) :
    @Measurable α β m₁ mβ f ↔ @Measurable α β m₂ mβ f := by
  cases h
  rfl

/-- The pushforward measure itself is unchanged when its source sigma algebra
is replaced by an equal one. Equality elimination transports the implicit
measurability condition used by `Measure.map`. -/
theorem measure_map_eq_of_sourceMeasurableSpace_eq
    {α β : Type*} (m₁ m₂ : MeasurableSpace α) (mβ : MeasurableSpace β)
    (h : m₁ = m₂) (μ : @Measure α m₁) (f : α → β) :
    @Measure.map α β m₁ mβ f μ = @Measure.map α β m₂ mβ f (h ▸ μ) := by
  cases h
  rfl

/-- For any pushforward out of the finite reset/path atom, the default-instance
map equals the explicit-top map. This equality is the local transport used
when comparing default-instance pushforwards with the staged law theorem. -/
theorem onlineResetPathAtom_map_default_eq_top
    {K n : ℕ} {β : Type*} [MeasurableSpace β]
    (f : OnlineResetPathAtom State K n → β)
    (μ : @Measure (OnlineResetPathAtom State K n) ⊤) :
    @Measure.map (OnlineResetPathAtom State K n) β
      (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) ‹MeasurableSpace β› f
      ((onlineResetPathAtom_defaultMeasurableSpace_eq_top (State := State) K n).symm ▸ μ) =
    @Measure.map (OnlineResetPathAtom State K n) β ⊤ ‹MeasurableSpace β› f μ := by
  exact (measure_map_eq_of_sourceMeasurableSpace_eq
    ⊤ (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n))
    ‹MeasurableSpace β›
    (onlineResetPathAtom_defaultMeasurableSpace_eq_top (State := State) K n).symm
    μ f).symm

/-- The staged stack/sequential law identity rewritten so its finite atom
pushforward is explicitly taken under `⊤`. The source assumptions and actual
law/map functions are exactly those of `onlineStack_sequential_transcriptLaw_eq`;
the finite helper supplies only the measurable-space equality used to rewrite
the map, not a new theorem premise. -/
theorem onlineStack_sequential_transcriptLaw_eq_topAtomMap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) (hn : n ≤ K * H) :
    (onlineMDPInitialStackLaw E ρ K).map
      (fun sample => (sample.1, onlineStackHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (onlineFiniteStackExtend K fallback sample.2) n)) =
      @Measure.map (OnlineResetPathAtom State K n)
        (OnlineResetTranscript State Action H K)
        (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) ⊤
        (fun sample => (sample.1, onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2))
        ((onlineResetPathAtom_defaultMeasurableSpace_eq_top (State := State) K n).symm ▸
          (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure) := by
  letI : MeasurableSpace State := ⊤
  classical
  have h := onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner n hn
  have htransport := onlineResetPathAtom_map_default_eq_top
    (State := State) (K := K) (n := n)
    (β := OnlineResetTranscript State Action H K)
    (f := fun sample => (sample.1, onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2))
    ((onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure)
  calc
    _ = @Measure.map (OnlineResetPathAtom State K n)
        (OnlineResetTranscript State Action H K) ⊤ ⊤
        (fun sample => (sample.1, onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2))
        ((onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure) := h
    _ = @Measure.map (OnlineResetPathAtom State K n)
        (OnlineResetTranscript State Action H K)
        (inferInstance : MeasurableSpace (OnlineResetPathAtom State K n)) ⊤
        (fun sample => (sample.1, onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2))
        ((onlineResetPathAtom_defaultMeasurableSpace_eq_top (State := State) K n).symm ▸
          (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure) := htransport.symm

end StatisticalRL.OnlineRL
