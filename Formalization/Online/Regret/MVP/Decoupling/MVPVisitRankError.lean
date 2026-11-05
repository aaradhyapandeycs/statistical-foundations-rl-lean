import Formalization.Online.Regret.MVP.Decoupling.MVPVisitRankKernel
import Formalization.Online.Regret.MVP.Decoupling.MVPStageSlotVariance

/-! error consumption for typed visit ranks. Missing ranks have zero
scalar contribution and do not require any fictitious empirical row. -/
namespace StatisticalRL.OnlineRL
variable {State Row : Type*} [Fintype State]

noncomputable def mvp_rankPositiveError (K : ℕ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State) (u : ℕ) (V : State → ℝ) : ℝ :=
  if hu : u<K then mvp_rowPositiveError p (mvp_visitRankKernel K initial first batch ⟨u,hu⟩) V
  else 0

theorem mvp_rankPositiveError_zero (K : ℕ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State) (u : ℕ) :
    mvp_rankPositiveError K p initial first batch u 0 = 0 := by
  by_cases hu : u<K
  · simp only [mvp_rankPositiveError,dif_pos hu,mvp_rowPositiveError_zero]
  · simp only [mvp_rankPositiveError,dif_neg hu]

theorem mvp_rankPositiveError_lookup_at_slot (rows : ℕ → Row) (K : ℕ) (r : Row)
    (V : Fin K → State → ℝ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State)
    (j : Fin (Nat.log2 K)) (i : ℕ) (hi : i<2*2^j.val) :
    mvp_rankPositiveError K p initial first batch (2*2^j.val+i)
      (mvp_visitValueLookup rows K r (2*2^j.val+i) V) =
    mvp_rowPositiveError p (batch j) (mvp_visitValueLookup rows K r (2*2^j.val+i) V) := by
  by_cases hu : 2*2^j.val+i<K
  · simp only [mvp_rankPositiveError,dif_pos hu]
    rw [mvp_visitRankKernel_at_slot K initial first batch j i hi hu]
  · rw [mvp_rankPositiveError,dif_neg hu,
      mvp_visitValueLookup_zero_of_ge rows K r _ V (by omega),mvp_rowPositiveError_zero]

theorem mvp_rankPositiveError_lookup_le (rows : ℕ → Row) (K : ℕ) (r : Row) (u : ℕ)
    (V : Fin K → State → ℝ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State)
    (H : ℝ) (hH : 0≤H) (hV : ∀ k s,0≤V k s∧V k s≤H) :
    mvp_rankPositiveError K p initial first batch u (mvp_visitValueLookup rows K r u V) ≤ H := by
  by_cases hu : u<K
  · simp only [mvp_rankPositiveError,dif_pos hu]
    exact mvp_rowPositiveError_le _ _ _ H hH
      (mvp_visitValueLookup_bounds rows K r u V H hH hV)
  · simp only [mvp_rankPositiveError,dif_neg hu]
    exact hH

theorem mvp_rowPositiveError_square_eq (p q : FiniteDistribution State)
    (H : ℝ) (hH : 0<H) (V : State → ℝ) :
    mvp_rowPositiveError p q (fun s=>V s^2) =
      H*mvp_rowPositiveError p q (mvp_normalizedSquare H V) :=
  mvp_normalizedSquare_positive_error p q H hH V

end StatisticalRL.OnlineRL
