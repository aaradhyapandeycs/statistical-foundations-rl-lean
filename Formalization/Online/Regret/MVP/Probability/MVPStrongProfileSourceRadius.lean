import Formalization.Online.Regret.MVP.Probability.MVPStrongSourceRadius
import Formalization.Online.Regret.MVP.Probability.MVPProfileDyadic
import Formalization.Online.Regret.MVP.Probability.MVPSourceRadius
import Formalization.Online.Regret.MVP.Probability.MVPUniformCardinality

/-! stronger all-profile radius at quarter failure budget; source iota unchanged. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action Profile : Type*} [Fintype State] [Fintype Action] [Fintype Profile] [Nonempty Profile]
local instance mvpStrongProfileStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpStrongProfileStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance mvpStrongProfileActionEq : DecidableEq Action := Classical.decEq Action
noncomputable local instance mvpStrongProfileChoiceFintype (H K : ℕ) :
    Fintype (mvpProfileChoiceIndex (Profile := Profile) (Level := mvpUniformLevel K) (State := State) (Action := Action) H K) := by
  unfold mvpProfileChoiceIndex mvpUniformLevel
  infer_instance

theorem mvp_profileFamily_quarterSourceRadius {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0 < H) (K : ℕ) (hK : 2 ≤ K)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hzero : ∀ p h code, (0 : State → ℝ) ∈ family p h code)
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (hbound : ∀ p h code V, V ∈ family p h code → ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/100)
    (hprofile : (Fintype.card Profile : ℝ) ≤
      (4*(H*Fintype.card State*Fintype.card Action : ℕ)*K : ℝ) ^
        ((H*Fintype.card State*Fintype.card Action : ℕ) * (Real.log K/Real.log 2) + 1)) :
    let d := H*Fintype.card State*Fintype.card Action
    let x := Real.log K/Real.log 2
    let I := 40000*x^3*Real.log (3*d)*Real.log (1/δ)
    1 - δ/4 ≤ (samplingLaw E K).real {data | ∀ p : Profile, ∀ l : mvpUniformLevel K,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l) (mvpUniformBatchSize_fits hK l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      Real.sqrt ((d : ℝ)*I*(∑ h : Fin H, ∑ s : State, ∑ a : Action,
        ((E h).transition s a).variance (X h s a))/(16*(mvpUniformBatchSize l)*x)) +
        (d : ℝ)*(H : ℝ)*I/(16*(mvpUniformBatchSize l)*x)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let d := H*Fintype.card State*Fintype.card Action
  let x := Real.log K/Real.log 2
  let I := 40000*x^3*Real.log (3*d)*Real.log (1/δ)
  let p := mvpUniformPeels d K
  let Idx := mvpProfileChoiceIndex (Profile := Profile) (Level := mvpUniformLevel K) (State := State) (Action := Action) H K
  let Mask := Fin H → State → Action → Bool
  let ε := (δ/4) / (Fintype.card (Idx × Mask) : ℝ)
  have hδq : 0 < δ/4 := by positivity
  have hδq1 : δ/4 < 1 := by linarith only [hδsmall]
  have hd : 1 ≤ d := by
    dsimp [d]
    have hs : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
    have ha : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
    have hp : 0 < H*Fintype.card State*Fintype.card Action := Nat.mul_pos (Nat.mul_pos hH hs) ha
    omega
  have hP : (1 : ℝ) ≤ Fintype.card Profile := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Profile)
  have hIdx : (Fintype.card (Idx × Mask) : ℝ) =
      (Fintype.card Profile : ℝ) * ((K:ℝ)+1)^d * Nat.log2 K * 2^d := by
    dsimp [Idx, Mask, d, mvpProfileChoiceIndex, mvpUniformLevel]
    rw [mvp_profileChoiceMask_card (State := State) (Action := Action) (Profile := Profile) (Level := Fin (Nat.log2 K)) H K]
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hlog2 : 0 < Nat.log2 K := by
    have h : 1 ≤ Nat.log2 K := (Nat.le_log2 (by omega)).2 (by simpa using hK)
    omega
  have hIdxpos : 0 < (Fintype.card (Idx × Mask) : ℝ) := by
    rw [hIdx]
    have hp0 : (0:ℝ) < Fintype.card Profile := by linarith
    have hl0 : (0:ℝ) < Nat.log2 K := by exact_mod_cast hlog2
    positivity
  have hεpos : 0 < ε := div_pos hδq hIdxpos
  have hlog : Real.log (2*p/ε) =
      Real.log (2*p*((Fintype.card Profile : ℝ)*((K:ℝ)+1)^d*(Nat.log2 K)*2^d)/(δ/4)) := by
    congr 1
    dsimp [ε]
    rw [hIdx]
    field_simp
  let A := {data | ∀ prof0 : Profile, ∀ l : mvpUniformLevel K,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family prof0 h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l) (mvpUniformBatchSize_fits hK l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      (Real.sqrt (8 * max
          (((mvpUniformBatchSize l : ℕ) : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (X h s a))
          ((((mvpUniformBatchSize l : ℕ) : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^p) *
          Real.log (2 * p / ε)) + (4/3) * H * Real.log (2 * p / ε)) / mvpUniformBatchSize l}
  have hA : 1-δ/4 ≤ (samplingLaw E K).real A :=
    mvp_profileFamily_dyadicUniform E K hK family hzero hcard hbound p (mvpUniformPeels_pos d K) (δ/4) hδq hδq1
  apply hA.trans
  apply measureReal_mono _ (measure_ne_top (samplingLaw E K) _)
  intro data hdA prof l X hX
  have hb := hdA prof l X hX
  have hV : 0 ≤ ∑ h : Fin H, ∑ s : State, ∑ a : Action,
      ((E h).transition s a).variance (X h s a) := by
    apply Finset.sum_nonneg
    intro h _
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro a _
    exact ((E h).transition s a).variance_nonneg _
  have hnK : mvpUniformBatchSize l ≤ K := by
    have hh := mvpUniformBatchSize_fits hK l
    omega
  have hr := mvp_sourceRadius_quarter_bound (Fintype.card Profile) δ H
    (∑ h : Fin H, ∑ s : State, ∑ a : Action, ((E h).transition s a).variance (X h s a))
    d K (mvpUniformBatchSize l) hP hδ hδsmall hd hK (mvpUniformBatchSize_pos l) hnK
    (by positivity) hV (by simpa [d, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hprofile)
  rw [hlog] at hb
  apply hb.trans
  simpa only [p, d, Nat.cast_mul, mul_assoc] using hr
end StatisticalRL.FiniteHorizonGenerative
