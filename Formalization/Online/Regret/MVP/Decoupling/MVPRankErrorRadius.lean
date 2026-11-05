import Formalization.Online.Regret.MVP.Decoupling.MVPRankErrorDecomposition
import Formalization.Online.Regret.MVP.Decoupling.MVPDyadicRadiusAggregation

/-! analytic consumption of simultaneous slot radii. The family event,
actual empirical-row identity and sampling-law transfer are separate proofs. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Row Stage : Type*} [Fintype State] [Fintype Row] [Fintype Stage]
variable [DecidableEq Row]

theorem mvp_rankErrorInitial_le (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (H : ℝ) (hH : 0≤H) (hV : ∀ h k s,0≤V h k s∧V h k s≤H) :
    mvp_rankErrorInitial rows K V p initial first batch ≤
      2*(Fintype.card Stage:ℝ)*(Fintype.card Row:ℝ)*H := by
  unfold mvp_rankErrorInitial
  calc
    _ ≤ ∑ _h : Stage, ∑ _r : Row, (2*H) := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro r _
      have h0 := mvp_rankPositiveError_lookup_le (rows h) K r 0 (V h)
        (p h r) (initial h r) (first h r) (batch h r) H hH (hV h)
      have h1 := mvp_rankPositiveError_lookup_le (rows h) K r 1 (V h)
        (p h r) (initial h r) (first h r) (batch h r) H hH (hV h)
      change _+_≤2*H
      change mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 0≤H at h0
      change mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r) 1≤H at h1
      linarith only [h0,h1]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

theorem mvp_rankErrorSlots_radius (rows : Stage → ℕ → Row) (K : ℕ) (hK : 2≤K)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (d H I T : ℝ) (hd : 0≤d) (hH : 0≤H) (hI : 0≤I) (hT : 0≤T)
    (hvars : (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      ∑ h : Stage, ∑ r : Row,
        (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h))) ≤ T)
    (he : ∀ j, j<Nat.log2 K → ∀ i, i<2*2^j →
      (∑ h : Stage, ∑ r : Row,
        mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
          (2*2^j+i)) ≤
      Real.sqrt (d*I*((1:ℝ)/(16*(2:ℝ)^j*(Real.log K/Real.log 2)))*
        (∑ h : Stage, ∑ r : Row,
          (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)))) +
      (d*H*I)*((1:ℝ)/(16*(2:ℝ)^j*(Real.log K/Real.log 2)))) :
    mvp_rankErrorSlots rows K V p initial first batch ≤
      Real.sqrt (d*I*(1/8)*T)+d*H*I/8 := by
  have hx : 0<Real.log K/Real.log 2 :=
    div_pos (Real.log_pos (by exact_mod_cast (show 1<K by omega)))
      (Real.log_pos (by norm_num))
  have hj := Real.log2_le_logb K
  simp only [Real.logb] at hj
  exact mvp_dyadicSlot_radius_sum (Nat.log2 K) (Real.log K/Real.log 2) (d*I) (d*H*I) T
    (fun j i=>∑ h : Stage, ∑ r : Row,
      (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)))
    (fun j i=>∑ h : Stage, ∑ r : Row,
      mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
        (2*2^j+i)) hx hj (mul_nonneg hd hI) (by positivity) hT
    (fun j i=>Finset.sum_nonneg (fun h _=>Finset.sum_nonneg (fun r _=>
      (p h r).variance_nonneg _))) hvars he

/-- An internal radius combiner. Its slot bound is supplied by the preceding
uniform-radius consumer; it is not an extra source-theorem hypothesis. -/
theorem mvp_rankErrorTotal_rawRadius (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (H I T : ℝ) (hH : 0≤H) (hV : ∀ h k s,0≤V h k s∧V h k s≤H)
    (hslots : mvp_rankErrorSlots rows K V p initial first batch ≤
      Real.sqrt (((Fintype.card Stage:ℝ)*Fintype.card Row)*I*(1/8)*T) +
        ((Fintype.card Stage:ℝ)*Fintype.card Row)*H*I/8) :
    mvp_rankErrorTotal rows K V p initial first batch ≤
      Real.sqrt (((Fintype.card Stage:ℝ)*Fintype.card Row)*I*(1/8)*T) +
        ((Fintype.card Stage:ℝ)*Fintype.card Row)*H*I/8 +
          2*((Fintype.card Stage:ℝ)*Fintype.card Row)*H := by
  rw [mvp_rankErrorTotal_decompose]
  have hinit := mvp_rankErrorInitial_le rows K V p initial first batch H hH hV
  linarith only [hinit,hslots]

end StatisticalRL.OnlineRL
