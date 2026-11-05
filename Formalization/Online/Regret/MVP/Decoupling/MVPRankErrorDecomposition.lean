import Formalization.Online.Regret.MVP.Decoupling.MVPVisitRankError
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! exact initial-rank and positive-slot error decomposition. The
actual retained-row representation is supplied by a separate model proof. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_sum_stageRows_dyadic_commute {Stage Row : Type*}
    [Fintype Stage] [Fintype Row] (J : ℕ) (F : Stage → Row → ℕ → ℕ → ℝ) :
    (∑ h : Stage, ∑ r : Row, ∑ j ∈ Finset.range J,
      ∑ i ∈ Finset.range (2*2^j), F h r j i) =
    ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2*2^j),
      ∑ h : Stage, ∑ r : Row, F h r j i := by
  let slots : Finset (Σ _j : ℕ,ℕ) :=
    (Finset.range J).sigma (fun j=>Finset.range (2*2^j))
  calc
    _ = ∑ h : Stage, ∑ r : Row, ∑ a ∈ slots,F h r a.1 a.2 := by
      simp only [slots,Finset.sum_sigma]
    _ = ∑ h : Stage, ∑ a ∈ slots, ∑ r : Row,F h r a.1 a.2 := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    _ = ∑ a ∈ slots, ∑ h : Stage, ∑ r : Row,F h r a.1 a.2 := Finset.sum_comm
    _ = _ := Finset.sum_sigma _ _ _

variable {State Row : Type*} [Fintype State]

noncomputable def mvp_rankErrorAt (rows : ℕ → Row) (K : ℕ) (r : Row)
    (V : Fin K → State → ℝ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State) (u : ℕ) : ℝ :=
  mvp_rankPositiveError K p initial first batch u (mvp_visitValueLookup rows K r u V)

variable {Stage : Type*} [Fintype Stage] [Fintype Row] [DecidableEq Row]

noncomputable def mvp_rankErrorTotal (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State) : ℝ :=
  ∑ h : Stage, ∑ k : Fin K,
    mvp_rankPositiveError K (p h (rows h k.val)) (initial h (rows h k.val))
      (first h (rows h k.val)) (batch h (rows h k.val))
      (onlineVisitCount (rows h) k.val (rows h k.val)) (V h k)

noncomputable def mvp_rankErrorInitial (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State) : ℝ :=
  ∑ h : Stage, ∑ r : Row,
    (mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 0 +
      mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 1)

noncomputable def mvp_rankErrorSlots (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
    ∑ h : Stage, ∑ r : Row,
      mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
        (2*2^j+i)

theorem mvp_rankErrorTotal_decompose (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State) :
    mvp_rankErrorTotal rows K V p initial first batch =
      mvp_rankErrorInitial rows K V p initial first batch +
        mvp_rankErrorSlots rows K V p initial first batch := by
  classical
  unfold mvp_rankErrorTotal mvp_rankErrorInitial mvp_rankErrorSlots
  calc
    _ = ∑ h : Stage, ∑ r : Row, ∑ k : Fin K,
        if rows h k.val = r then
          mvp_rankPositiveError K (p h r) (initial h r) (first h r) (batch h r)
            (onlineVisitCount (rows h) k.val r) (V h k) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      exact (mvp_allRows_groupVisits (rows h) K (fun r k =>
        mvp_rankPositiveError K (p h r) (initial h r) (first h r) (batch h r)
          (onlineVisitCount (rows h) k.val r) (V h k))).symm
    _ = ∑ h : Stage, ∑ r : Row,
        ((mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 0 +
          mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 1) +
          ∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
            mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
              (2*2^j+i)) := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro r _
      simpa only [mvp_rankErrorAt] using mvp_adaptiveVisit_sum_dyadicSlots (rows h) K r (V h)
        (mvp_rankPositiveError K (p h r) (initial h r) (first h r) (batch h r))
        (mvp_rankPositiveError_zero K (p h r) (initial h r) (first h r) (batch h r))
    _ = (∑ h : Stage, ∑ r : Row,
        (mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 0 +
          mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 1)) +
        (∑ h : Stage, ∑ r : Row, ∑ j ∈ Finset.range (Nat.log2 K),
          ∑ i ∈ Finset.range (2*2^j),
            mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
              (2*2^j+i)) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by rw [mvp_sum_stageRows_dyadic_commute]

end StatisticalRL.OnlineRL
