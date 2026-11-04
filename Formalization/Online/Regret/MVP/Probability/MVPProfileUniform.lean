import Formalization.Online.Regret.MVP.Probability.MVPProfileCoverage

/-! Uniform aggregate bound for all profiles and all admissible family choices. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action Profile Level : Type*} [Fintype State] [Fintype Action]
  [Fintype Profile] [Nonempty Profile] [Fintype Level] [Nonempty Level]
local instance : MeasurableSpace State := ⊤
noncomputable local instance mvpPUStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpPUActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable local instance mvpPUChoiceFintype (H K : ℕ) :
    Fintype (mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K) := by
  unfold mvpProfileChoiceIndex
  infer_instance

noncomputable local instance mvpPUChoiceNonempty (H K : ℕ) :
    Nonempty (mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K) := by
  unfold mvpProfileChoiceIndex
  infer_instance

theorem mvp_profileFamily_uniformExplicit {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (n : Level → ℕ) (hn : ∀ l, 2*n l ≤ K) (hnpos : ∀ l, 0<n l)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hzero : ∀ p h code, (0 : State → ℝ) ∈ family p h code)
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (hbound : ∀ p h code V, V ∈ family p h code → ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let Idx := mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K
    let Mask := Fin H → State → Action → Bool
    let ε := δ / (Fintype.card (Idx × Mask) : ℝ)
    1 - δ ≤ (samplingLaw E K).real {data | ∀ p : Profile, ∀ l : Level,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (n l) (hnpos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (n l) (hn l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      (Real.sqrt (8 * max
          (((n l : ℕ) : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (X h s a))
          ((((n l : ℕ) : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / n l} := by
  classical
  let Idx := mvpProfileChoiceIndex (Profile := Profile) (Level := Level) (State := State) (Action := Action) H K
  let Mask := Fin H → State → Action → Bool
  let n' : Idx → ℕ := fun i => n i.2.2
  let hn' : ∀ i : Idx, 2*n' i ≤ K := fun i => hn i.2.2
  let hp' : ∀ i : Idx, 0<n' i := fun i => hnpos i.2.2
  let V : (i : Idx) → (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ :=
    mvpProfileSelectedTest K family
  have hV : ∀ i h s a code x, 0 ≤ V i h s a code x ∧ V i h s a code x ≤ H := by
    intro i h s a code x
    exact hbound i.1 h code (V i h s a code) (mvpProfileSelectedTest_mem K family hzero i h s a code) x
  have hu := mvp_finiteUniform_positiveParts (ι := Idx) E K n' hn' hp' V hV peels hp δ hδ hδ1
  let ε := δ / (Fintype.card (Idx × Mask) : ℝ)
  let A := {data : Samples State Action H K | ∀ i : Idx,
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      max ((FiniteDistribution.empiricalRow (n' i) (hp' i)
        (fun j => data ((h,s,a),mvpBatchIndex K (n' i) (hn' i) j))).expectation
        (V i h s a (futureData h K data)) - ((E h).transition s a).expectation
        (V i h s a (futureData h K data))) 0) ≤
    (Real.sqrt (8 * max ((n' i : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
      ((E h).transition s a).variance (V i h s a (futureData h K data)))
      (((n' i : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
      Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / n' i}
  have hA : 1 - δ ≤ (samplingLaw E K).real A := hu
  apply hA.trans
  apply measureReal_mono _ (measure_ne_top (samplingLaw E K) _)
  intro data hd p l X hX
  obtain ⟨choice,hchoice⟩ := mvpProfileChoice_covers_actualFamily K family hcard p l data X hX
  have h := hd (p,choice,l)
  simpa only [V, n', hn', hp', hchoice] using h
end StatisticalRL.FiniteHorizonGenerative
