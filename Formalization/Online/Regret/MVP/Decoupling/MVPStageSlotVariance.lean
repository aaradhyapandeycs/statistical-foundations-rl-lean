import Formalization.Online.Regret.MVP.Decoupling.MVPAdaptiveSlotVariance
import Formalization.Online.Regret.MVP.Decoupling.MVPNormalizedSquare

/-! deterministic horizon/row sum and normalized-square variance
consumption. Actual value-family probability is proved separately. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row State : Type*}

theorem mvp_visitValueLookup_bounds (rows : ℕ → Row) (K : ℕ) (r : Row) (u : ℕ)
    (V : Fin K → State → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hV : ∀ k s, 0 ≤ V k s ∧ V k s ≤ H) :
    ∀ s, 0 ≤ mvp_visitValueLookup rows K r u V s ∧
      mvp_visitValueLookup rows K r u V s ≤ H := by
  classical
  by_cases h : ∃ k : Fin K, rows k.val = r ∧ onlineVisitCount rows k.val r = u
  · obtain ⟨k,hk⟩ := h
    rw [mvp_visitValueLookup_hit rows K r u V k hk]
    exact hV k
  · rw [mvp_visitValueLookup_zero rows K r u V (fun k hk => h ⟨k,hk⟩)]
    exact fun _ => ⟨le_rfl, hH⟩

variable {Stage : Type*} [Fintype State] [Fintype Stage] [Fintype Row] [DecidableEq Row]

theorem mvp_allStages_slotVariance_le (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ) (p : Stage → Row → FiniteDistribution State) :
    (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      ∑ h : Stage, ∑ r : Row,
        (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h))) ≤
      ∑ h : Stage, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (Nat.log2 K), ∑ h : Stage,
        ∑ i ∈ Finset.range (2*2^j), ∑ r : Row,
          (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ h : Stage, ∑ j ∈ Finset.range (Nat.log2 K),
        ∑ i ∈ Finset.range (2*2^j), ∑ r : Row,
          (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)) :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun h _ => mvp_allRows_slotVariance_le (rows h) K (V h) (p h))

theorem mvp_allStages_normalizedSquare_slotVariance_le
    (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ) (p : Stage → Row → FiniteDistribution State)
    (H : ℝ) (hH : 0 < H) (hV : ∀ h k s, 0 ≤ V h k s ∧ V h k s ≤ H) :
    (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      ∑ h : Stage, ∑ r : Row,
        (p h r).variance (mvp_normalizedSquare H
          (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)))) ≤
      4*(∑ h : Stage, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
        ∑ h : Stage, ∑ r : Row,
          4*(p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro r _
      exact mvp_normalizedSquare_variance (p h r) H hH _
        (mvp_visitValueLookup_bounds (rows h) K r _ (V h) H hH.le (hV h))
    _ = 4*(∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
        ∑ h : Stage, ∑ r : Row,
          (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h))) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mvp_allStages_slotVariance_le rows K V p) (by norm_num)

end StatisticalRL.OnlineRL
