import Formalization.Online.SourceOptimism.VisitCountFoundation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Card

/-! Finite prefix union. Fixed-count concentration is
an explicit intermediate input; no iid assertion conditional on random counts. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row Data : Type*} [Fintype Row] [Nonempty Row] [Fintype Data]
variable [MeasurableSpace Data] [MeasurableSingletonClass Data]

abbrev OnlineNontrivialPrefix (K : ℕ) := {n : ℕ // n∈Finset.Ico 3 K}

theorem onlineNontrivialPrefix_card (K : ℕ) :
    Fintype.card (OnlineNontrivialPrefix K)=K-3 := by
  simp [OnlineNontrivialPrefix,Nat.card_Ico]

/-- A single union over rows and deterministic prefix lengths3..K−1 has the
strict printed confidence margin; no extra episode union is taken. -/
theorem onlineFixedPrefix_union_strict
    (μ : Measure Data) [IsProbabilityMeasure μ] (K : ℕ) (hK : 0<K)
    (δ : ℝ) (hδ : 0<δ) (Good : Row → ℕ → Set Data)
    (hfixed : ∀ r n,3≤n → n<K → μ.real (Good r n)ᶜ≤2*δ) :
    1-2*(Fintype.card Row : ℝ)*K*δ <
      μ.real {data | ∀ r n,3≤n → n<K → data∈Good r n} := by
  classical
  let I := Row × OnlineNontrivialPrefix K
  let bad : I → Set Data := fun i => (Good i.1 i.2.val)ᶜ
  let badUnion : Set Data := ⋃ i,bad i
  have hi (i : I) : μ.real (bad i)≤2*δ :=
    hfixed i.1 i.2.val (Finset.mem_Ico.mp i.2.property).1
      (Finset.mem_Ico.mp i.2.property).2
  have hbad : μ.real badUnion≤
      2*(Fintype.card Row : ℝ)*(K-3 : ℕ)*δ := by
    calc
      _ ≤ ∑ i : I,μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : I,2*δ := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by
        simp [I,Fintype.card_prod,onlineNontrivialPrefix_card]
        ring
  have hcard : (0 : ℝ)<Fintype.card Row := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcount : (K-3 : ℕ)<K := by omega
  have hslack : 2*(Fintype.card Row : ℝ)*(K-3 : ℕ)*δ <
      2*(Fintype.card Row : ℝ)*K*δ := by
    have hcast : ((K-3 : ℕ) : ℝ)<K := by exact_mod_cast hcount
    nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ)<2) hcard) hδ]
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable badUnion).measurableSet)
  rw [probReal_univ] at hcomp
  have hset : badUnionᶜ={data | ∀ r n,3≤n → n<K → data∈Good r n} := by
    ext data
    simp only [badUnion,bad,Set.mem_compl_iff,Set.mem_iUnion,Set.mem_setOf_eq,
      not_exists,not_not]
    constructor
    · intro h r n hn hnK
      exact h (r,⟨n,Finset.mem_Ico.mpr ⟨hn,hnK⟩⟩)
    · intro h i
      exact h i.1 i.2.val (Finset.mem_Ico.mp i.2.property).1
        (Finset.mem_Ico.mp i.2.property).2
  rw [← hset]
  linarith

/-- The simultaneous deterministic-prefix event covers every realized adaptive
pre-episode count. This inclusion is pathwise and assumes no independence. -/
theorem onlineFixedPrefix_event_covers_adaptive_counts
    (K : ℕ) (rowAt : Data → ℕ → Row) (Good : Row → ℕ → Set Data) :
    {data | ∀ r n,3≤n → n<K → data∈Good r n} ⊆
      {data | ∀ j, j<K → ∀ r,
        3≤onlineVisitCount (rowAt data) j r →
        data∈Good r (onlineVisitCount (rowAt data) j r)} := by
  classical
  intro data hp j hj r hcount
  apply hp r _ hcount
  have hc : onlineVisitCount (rowAt data) j r≤j := by
    unfold onlineVisitCount
    simpa using Finset.card_filter_le (Finset.range j) (fun k => rowAt data k=r)
  exact hc.trans_lt hj

end StatisticalRL.OnlineRL
