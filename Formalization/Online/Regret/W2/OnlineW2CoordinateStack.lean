import Formalization.Online.Regret.W1.OnlineW1TrueVariancePrefix

/-! Fixed-coordinate Bernstein union on the actual row-stack law. The event
covers every deterministic row and prefix before any adaptive selection. It
is an intermediate event, not a W₂ cumulative or regret-rate theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row State : Type*} [Fintype Row] [Nonempty Row] [Fintype State]
local instance w2CoordinateStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance w2CoordinateStateDecidable : DecidableEq State := Classical.decEq State

/-- One coordinate of a probability row. -/
noncomputable def onlineW2Indicator (x : State) : State → ℝ :=
  fun y => if y = x then 1 else 0

/-- Coordinate good event uses true-row Bernoulli variance and deterministic
stack prefixes. Counts 0–2 remain a separate bounded branch. -/
noncomputable def onlineW2CoordinateGood
    (d : Row → FiniteDistribution State) (K : ℕ) (δ : ℝ)
    (x : State) (r : Row) (n : ℕ) : Set (Row × Fin K → State) :=
  onlineTrueW1StackPrefixGood d (fun _ => onlineW2Indicator x) K 1 δ r n

/-- One common stack experiment has simultaneous two-sided certificates for
all row, coordinate and deterministic prefix choices. -/
theorem onlineW2Stack_allCoordinatesPrefixes_strict
    (d : Row → FiniteDistribution State) (K : ℕ) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) :
    1 - 4 * (Fintype.card State : ℝ) * (Fintype.card Row : ℝ) * K * δ <
      (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        {data | ∀ x r n, 3 ≤ n → n < K → data ∈ onlineW2CoordinateGood d K δ x r n} := by
  classical
  let μ := onlineStackProductLaw (fun i : Row × Fin K => d i.1)
  let good : State → Set (Row × Fin K → State) := fun x =>
    {data | ∀ r n, 3 ≤ n → n < K → data ∈ onlineW2CoordinateGood d K δ x r n}
  have hgood (x : State) : 1 - 4 * (Fintype.card Row : ℝ) * K * δ < μ.real (good x) := by
    have hV : ∀ (_ : Row) s, onlineW2Indicator x s ∈ Set.Icc 0 (1 : ℝ) := by
      intro r s
      simp only [onlineW2Indicator]
      split_ifs <;> norm_num
    simpa [μ, good, onlineW2CoordinateGood] using
      onlineTrueW1Stack_allPrefixes_strict d (fun _ => onlineW2Indicator x)
        K hK 1 δ (by norm_num) hδ hδsmall hV
  let bad : Set (Row × Fin K → State) := ⋃ x : State, (good x)ᶜ
  have hStateNonempty : Nonempty State := by
    let r : Row := Classical.choice inferInstance
    have hsum : 0 < ∑ x : State, (d r).prob x := by rw [(d r).sum_prob]; norm_num
    obtain ⟨x, _, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => (d r).prob_nonneg x)).mp hsum
    exact ⟨x⟩
  letI : Nonempty State := hStateNonempty
  have hbad : μ.real bad < (Fintype.card State : ℝ) *
      (4 * (Fintype.card Row : ℝ) * K * δ) := by
    calc
      _ ≤ ∑ x : State, μ.real ((good x)ᶜ) := measureReal_iUnion_fintype_le _
      _ < ∑ _x : State, (4 * (Fintype.card Row : ℝ) * K * δ) := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro x hx
        have hc := measureReal_compl (μ := μ) ((Set.to_countable (good x)).measurableSet)
        rw [probReal_univ] at hc
        linarith [hgood x]
      _ = _ := by simp
  have hc := measureReal_compl (μ := μ) ((Set.to_countable bad).measurableSet)
  rw [probReal_univ] at hc
  have hset : badᶜ = {data | ∀ x r n, 3 ≤ n → n < K →
      data ∈ onlineW2CoordinateGood d K δ x r n} := by
    ext data
    simp [bad, good]
  change 1 - 4 * (Fintype.card State : ℝ) * (Fintype.card Row : ℝ) * K * δ < μ.real _
  rw [← hset]
  nlinarith
end StatisticalRL.OnlineRL
