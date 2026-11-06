import Formalization.Online.QLearning.ActualStackRateConfidence

/-! Simultaneous deterministic row/time confidence under the actual stack law. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningRateUnionStateMeasurable : MeasurableSpace State := ⊤

/-- A single simultaneous event over rows and all deterministic positive prefix
lengths up to K. The half-budget leaves a strict confidence margin. -/
theorem qLearning_actualStack_rate_union
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (V : OnlineMDPRow State Action H → State → ℝ)
    (hV : ∀ r s, V r s ∈ Set.Icc 0 (H:ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (onlineMDPInitialStackLaw E ρ K).real {sample |
      ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
      |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample (V r) (j.val+1) i
          (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
        Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by dsimp [μ,onlineMDPInitialStackLaw,onlineMDPStackLaw]; infer_instance
  let d : ℝ := Fintype.card (OnlineMDPRow State Action H)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  let ε : ℝ := δ/(2*d*K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hε1 : ε < 1 := by dsimp [ε]; rw [div_lt_one (by positivity)]; nlinarith
  let Good (r : OnlineMDPRow State Action H) (j : Fin K) : Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) := {sample |
    |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (V r) (j.val+1) i
        (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
    Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*Real.log (2/ε))}
  let I := OnlineMDPRow State Action H × Fin K
  let bad : I → Set _ := fun z => (Good z.1 z.2)ᶜ
  let U : Set _ := ⋃ z,bad z
  have hbad (z : I) : μ.real (bad z) ≤ ε := by
    have h := qLearning_actualStack_rate_confidence H K (z.2.val+1) hH (by omega)
      (Nat.succ_le_of_lt z.2.isLt) E ρ z.1 (V z.1) (hV z.1) ε hε hε1
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (Good z.1 z.2)).measurableSet)
    rw [probReal_univ] at hc
    have hfixed : 1-ε < μ.real (Good z.1 z.2) := by
      simpa only [Good, μ, Nat.cast_add, Nat.cast_one] using h
    dsimp [bad]
    linarith
  have hU : μ.real U ≤ d*K*ε := by
    calc
      _ ≤ ∑ z : I, μ.real (bad z) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _z : I, ε := Finset.sum_le_sum (fun z _ => hbad z)
      _ = d*K*ε := by simp [I,d,Fintype.card_prod]
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable U).measurableSet)
  rw [probReal_univ] at hcomp
  have hgood : Uᶜ = {sample | ∀ r j, sample ∈ Good r j} := by
    ext sample
    simp [U,bad,I]
  have hlog : 2/ε = 4*d*K/δ := by
    dsimp [ε]
    field_simp
    <;> ring_nf
    <;> norm_num
  have hbudget : d*K*ε = δ/2 := by dsimp [ε]; field_simp; <;> ring
  rw [hbudget] at hU
  have hfinal : 1-δ < μ.real Uᶜ := by linarith
  rw [hgood] at hfinal
  simpa [Good, μ, hlog, d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm] using hfinal
end StatisticalRL.OnlineRL
