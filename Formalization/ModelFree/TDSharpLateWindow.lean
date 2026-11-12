import Formalization.ModelFree.TDSharpMartingale

/-! The centered-square source window is zero-padded before the late half and after the fixed terminal; its sum reindexes to source updates. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Source active Freedman indices: `n` corresponds to source update `k=n+1`.
The filter gives `floor(t/2)≤n<t`, including an empty set when `t=0`. -/
def tdSquareLateWindowIndices (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun n ↦ t / 2 ≤ n)

/-- Source centered-square term at source update `k`, with fixed terminal `t`.
On the source window, `k` ranges from `floor(t/2)+1` through `t`. -/
noncomputable def tdSquareSourceTerm (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (k : ℕ) : TDSamples State T → ℝ :=
  fun data ↦ tdErrorPropagate M π η k t
    (fun r ↦ tdSquareCentered M π η T V₀ k r data) s

/-- Zero-padded version of the general centered-square sequence. It vanishes
before `floor(t/2)` and from index `t` onward; active `n` represents source
update `n+1`. -/
noncomputable def tdSquareLateWindowIncrement (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (n : ℕ) : TDSamples State T → ℝ :=
  if t / 2 ≤ n ∧ n < t then
    tdSquareTerminalIncrement M π η T t V₀ s n
  else fun _ ↦ 0

/-- The source finite-window sum, indexed by source update `k`. -/
noncomputable def tdSquareSourceLateWindowSum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (data : TDSamples State T) : ℝ :=
  ∑ k ∈ Finset.Icc (t / 2 + 1) t,
    tdSquareSourceTerm M π η T t V₀ s k data

/-- The wrapper's full zero-padded sum over the `t` possible update indices. -/
noncomputable def tdSquareLateWindowSum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (data : TDSamples State T) : ℝ :=
  ∑ n ∈ Finset.range t,
    tdSquareLateWindowIncrement M π η T t V₀ s n data

theorem tdSquareTerminalIncrement_eq_sourceTerm_shift
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State) (n : ℕ)
    (hn : n < t) :
    tdSquareTerminalIncrement M π η T t V₀ s n =
      tdSquareSourceTerm M π η T t V₀ s (n + 1) := by
  funext data
  simp [tdSquareTerminalIncrement, tdSquareSourceTerm, hn]

/-- The padded sum is exactly the source finite sum reindexed by `k=n+1`.
This covers `t=0` without a predecessor underflow: both source window and
active-index set are empty. -/
theorem tdSquareLateWindowSum_eq_source
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ)
    (s : State) (data : TDSamples State T) :
    tdSquareLateWindowSum M π η T t V₀ s data =
      tdSquareSourceLateWindowSum M π η T t V₀ s data := by
  classical
  have hpad :
      (∑ n ∈ Finset.range t,
        tdSquareLateWindowIncrement M π η T t V₀ s n data) =
      ∑ n ∈ tdSquareLateWindowIndices t,
        tdSquareTerminalIncrement M π η T t V₀ s n data := by
    simp only [tdSquareLateWindowIndices, tdSquareLateWindowIncrement,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hnt : n < t := Finset.mem_range.mp hn
    by_cases h : t / 2 ≤ n <;> simp [h, hnt]
  rw [tdSquareLateWindowSum, tdSquareSourceLateWindowSum, hpad]
  apply Finset.sum_bij (fun n _ ↦ n + 1)
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hrange := Finset.mem_range.mp hn'.1
    exact Finset.mem_Icc.mpr (by omega)
  · intro n₁ hn₁ n₂ hn₂ hEq
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨k - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · omega
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hlt := Finset.mem_range.mp hn'.1
    exact congrFun (tdSquareTerminalIncrement_eq_sourceTerm_shift
      M π η T t V₀ s n hlt) data

end StatisticalRL.TemporalDifference
