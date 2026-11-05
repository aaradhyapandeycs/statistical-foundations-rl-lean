import Formalization.Online.SourceOptimism.VisitCoordinateDistinct
import Formalization.Online.Regret.MVP.MVPActualProfiles

/-! deterministic adaptive-value rank adapter.
No sampling law, independence or source completion is assumed or certified.
-/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row Value : Type*} [AddCommMonoid Value]

/-- The actual value at a row's zero-based visit rank, and zero for an absent
rank. Rank injectivity proves that this finite sum has at most one term. -/
noncomputable def mvp_visitValueLookup (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (V : Fin K → Value) : Value := by
  classical
  exact ∑ k : Fin K,
    if rows k.val = r ∧ onlineVisitCount rows k.val r = u then V k else 0

theorem mvp_visitRank_match_unique (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (k l : Fin K)
    (hk : rows k.val = r ∧ onlineVisitCount rows k.val r = u)
    (hl : rows l.val = r ∧ onlineVisitCount rows l.val r = u) : k = l := by
  classical
  apply onlineVisitCoordinate_injective rows K
  simp only [hk.1, hl.1, hk.2, hl.2]

theorem mvp_visitValueLookup_hit (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (V : Fin K → Value) (k : Fin K)
    (hk : rows k.val = r ∧ onlineVisitCount rows k.val r = u) :
    mvp_visitValueLookup rows K r u V = V k := by
  classical
  unfold mvp_visitValueLookup
  calc
    _ = (if rows k.val = r ∧ onlineVisitCount rows k.val r = u then V k else 0) := by
      apply Finset.sum_eq_single k
      · intro l _ hlk
        by_cases hl : rows l.val = r ∧ onlineVisitCount rows l.val r = u
        · exact (hlk (mvp_visitRank_match_unique rows K r u l k hl hk)).elim
        · exact if_neg hl
      · intro hn
        exact (hn (Finset.mem_univ k)).elim
    _ = V k := if_pos hk

theorem mvp_visitValueLookup_zero (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (V : Fin K → Value)
    (h : ∀ k : Fin K, ¬ (rows k.val = r ∧ onlineVisitCount rows k.val r = u)) :
    mvp_visitValueLookup rows K r u V = 0 := by
  classical
  unfold mvp_visitValueLookup
  apply Finset.sum_eq_zero
  intro k _
  exact if_neg (h k)

theorem mvp_visitValueLookup_mem (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (V : Fin K → Value) (family : Finset Value)
    (hzero : 0 ∈ family) (hV : ∀ k, V k ∈ family) :
    mvp_visitValueLookup rows K r u V ∈ family := by
  classical
  by_cases h : ∃ k : Fin K, rows k.val = r ∧ onlineVisitCount rows k.val r = u
  · obtain ⟨k,hk⟩ := h
    rw [mvp_visitValueLookup_hit rows K r u V k hk]
    exact hV k
  · rw [mvp_visitValueLookup_zero rows K r u V (fun k hk => h ⟨k,hk⟩)]
    exact hzero

theorem mvp_visitValueLookup_map {Other : Type*} [AddCommMonoid Other]
    (rows : ℕ → Row) (K : ℕ) (r : Row) (u : ℕ) (V : Fin K → Value)
    (F : Value → Other) (hF : F 0 = 0) :
    F (mvp_visitValueLookup rows K r u V) =
      mvp_visitValueLookup rows K r u (fun k => F (V k)) := by
  classical
  by_cases h : ∃ k : Fin K, rows k.val = r ∧ onlineVisitCount rows k.val r = u
  · obtain ⟨k,hk⟩ := h
    rw [mvp_visitValueLookup_hit rows K r u V k hk,
      mvp_visitValueLookup_hit rows K r u (fun k => F (V k)) k hk]
  · have hn : ∀ k : Fin K, ¬ (rows k.val = r ∧ onlineVisitCount rows k.val r = u) :=
      fun k hk => h ⟨k,hk⟩
    rw [mvp_visitValueLookup_zero rows K r u V hn,
      mvp_visitValueLookup_zero rows K r u (fun k => F (V k)) hn]
    exact hF

theorem mvp_visitValueLookup_zero_of_ge (rows : ℕ → Row) (K : ℕ) (r : Row)
    (u : ℕ) (V : Fin K → Value) (hu : K ≤ u) :
    mvp_visitValueLookup rows K r u V = 0 := by
  classical
  apply mvp_visitValueLookup_zero
  intro k hk
  have hc := MVPProfile.onlineVisitCount_le_prefix rows k.val r
  have hlt := k.isLt
  omega

/-- Reindex an arbitrary zero-preserving functional of the actual adaptive
value. In particular, variance and positive-part error need no linearity. -/
theorem mvp_visitValueLookup_sum [DecidableEq Row] (rows : ℕ → Row) (K : ℕ) (r : Row)
    (V : Fin K → Value) (G : ℕ → Value → ℝ) (hG : ∀ u, G u 0 = 0) :
    (∑ u ∈ Finset.range K, G u (mvp_visitValueLookup rows K r u V)) =
      ∑ k : Fin K, if rows k.val = r then
        G (onlineVisitCount rows k.val r) (V k) else 0 := by
  classical
  calc
    _ = ∑ u ∈ Finset.range K, ∑ k : Fin K,
        if rows k.val = r ∧ onlineVisitCount rows k.val r = u
          then G u (V k) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simpa only [mvp_visitValueLookup] using
        mvp_visitValueLookup_map rows K r u V (G u) (hG u)
    _ = ∑ k : Fin K, ∑ u ∈ Finset.range K,
        if rows k.val = r ∧ onlineVisitCount rows k.val r = u
          then G u (V k) else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hr : rows k.val = r
      · have hcount : onlineVisitCount rows k.val r < K :=
          lt_of_le_of_lt (MVPProfile.onlineVisitCount_le_prefix rows k.val r) k.isLt
        simp [hr, Finset.mem_range, hcount]
      · simp [hr]

end StatisticalRL.OnlineRL
