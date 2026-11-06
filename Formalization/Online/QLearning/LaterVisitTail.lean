import Formalization.Online.QLearning.FiniteRateTail
import Formalization.Online.SourceOptimism.VisitCoordinateDistinct

/-! A fixed visit's total later same-row influence is bounded by the source tail. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

theorem qLearning_laterVisit_weights_le (H : ℕ) (hH : 0 < H)
    (rowAt : ℕ → Row) (K e : ℕ) :
    (∑ k ∈ (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e),
      onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e))
        (onlineVisitCount rowAt e (rowAt e)+1)) ≤ 1+1/(H:ℝ) := by
  classical
  let i := onlineVisitCount rowAt e (rowAt e)+1
  let s := (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e)
  let f := fun k => onlineVisitCount rowAt k (rowAt e)-i
  have hi : 0 < i := by dsimp [i]; omega
  have hrank (k : ℕ) (hk : k ∈ s) : i ≤ onlineVisitCount rowAt k (rowAt e) := by
    have hm := (Finset.mem_filter.mp hk).2
    have hh := onlineVisitCoordinate_index_strict rowAt e k hm.1 hm.2.symm
    rw [hm.2] at hh
    dsimp [i]
    omega
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hca := hrank a ha
    have hcb := hrank b hb
    have hc : onlineVisitCount rowAt a (rowAt e) = onlineVisitCount rowAt b (rowAt e) := by
      dsimp [f] at hab
      omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · have hra := (Finset.mem_filter.mp (show a ∈ (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e) from ha)).2.2
      have hrb := (Finset.mem_filter.mp (show b ∈ (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e) from hb)).2.2
      have h := onlineVisitCoordinate_index_strict rowAt a b hlt (hra.trans hrb.symm)
      rw [hra,hrb] at h
      omega
    · have hra := (Finset.mem_filter.mp (show a ∈ (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e) from ha)).2.2
      have hrb := (Finset.mem_filter.mp (show b ∈ (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e) from hb)).2.2
      have h := onlineVisitCoordinate_index_strict rowAt b a hgt (hrb.trans hra.symm)
      rw [hra,hrb] at h
      omega
  have heq : (∑ k ∈ s, onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e)) i) =
      ∑ j ∈ s.image f, onlineQRateWeight H (i+j) i := by
    apply Finset.sum_bij (fun k _ => f k)
    · intro k hk; exact Finset.mem_image.mpr ⟨k,hk,rfl⟩
    · intro a ha b hb hab; exact hinj ha hb hab
    · intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact ⟨k,hk,rfl⟩
    · intro k hk
      have hr := hrank k hk
      congr 1
      dsimp [f]
      omega
  change (∑ k ∈ s, onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e)) i) ≤ _
  rw [heq]
  exact qLearning_rate_tail_finite H i hH hi (s.image f)
end StatisticalRL.OnlineRL
