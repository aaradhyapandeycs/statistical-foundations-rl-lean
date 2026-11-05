import Formalization.Online.Regret.MVP.Decoupling.MVPRankErrorRadius

/-! analytic endpoint for rank-indexed errors. The radius predicate
is discharged from the actual simultaneous family event in a separate file. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Row Stage : Type*} [Fintype State] [Fintype Row] [Fintype Stage]
variable [DecidableEq Row]

def mvp_rankSlotRadiusCondition (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (d H I : ℝ) : Prop :=
  ∀ j, j<Nat.log2 K → ∀ i, i<2*2^j →
    (∑ h : Stage, ∑ r : Row,
      mvp_rankErrorAt (rows h) K r (V h) (p h r) (initial h r) (first h r) (batch h r)
        (2*2^j+i)) ≤
    Real.sqrt (d*I*((1:ℝ)/(16*(2:ℝ)^j*(Real.log K/Real.log 2)))*
      (∑ h : Stage, ∑ r : Row,
        (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i) (V h)))) +
    (d*H*I)*((1:ℝ)/(16*(2:ℝ)^j*(Real.log K/Real.log 2)))

theorem mvp_rankErrorTotal_linear_bound (rows : Stage → ℕ → Row) (K : ℕ) (hK : 2≤K)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (H I : ℝ) (hH : 0≤H) (hI : 4≤I) (hV : ∀ h k s,0≤V h k s∧V h k s≤H)
    (he : mvp_rankSlotRadiusCondition rows K V p initial first batch
      ((Fintype.card Stage:ℝ)*Fintype.card Row) H I) :
    let d := (Fintype.card Stage:ℝ)*Fintype.card Row
    let T := ∑ h : Stage, ∑ k : Fin K,(p h (rows h k.val)).variance (V h k)
    mvp_rankErrorTotal rows K V p initial first batch ≤ Real.sqrt (d*I*T)+d*H*I := by
  let d := (Fintype.card Stage:ℝ)*Fintype.card Row
  let T := ∑ h : Stage, ∑ k : Fin K,(p h (rows h k.val)).variance (V h k)
  change mvp_rankErrorTotal rows K V p initial first batch ≤ Real.sqrt (d*I*T)+d*H*I
  have hd : 0≤d := by dsimp [d]; positivity
  have hI0 : 0≤I := by linarith only [hI]
  have hT : 0≤T := Finset.sum_nonneg (fun h _=>Finset.sum_nonneg (fun k _=>
    (p h (rows h k.val)).variance_nonneg _))
  have hvars := mvp_allStages_slotVariance_le rows K V p
  have hs := mvp_rankErrorSlots_radius rows K hK V p initial first batch d H I T hd hH hI0 hT hvars he
  have hr := mvp_rankErrorTotal_rawRadius rows K V p initial first batch H I T hH hV hs
  exact mvp_linearSlot_final_absorb d H I T _ hd hH hI hT hr

/-- Exact scalar scaling for the squared-value error. The finite empirical
kernel is unchanged when replacing V by its normalized square. -/
theorem mvp_rankPositiveError_square_eq (K : ℕ) (p initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State) (u : ℕ)
    (H : ℝ) (hH : 0<H) (V : State → ℝ) :
    mvp_rankPositiveError K p initial first batch u (fun s=>V s^2) =
      H*mvp_rankPositiveError K p initial first batch u (mvp_normalizedSquare H V) := by
  by_cases hu : u<K
  · simp only [mvp_rankPositiveError,dif_pos hu]
    exact mvp_rowPositiveError_square_eq _ _ H hH V
  · simp only [mvp_rankPositiveError,dif_neg hu,mul_zero]

theorem mvp_rankErrorTotal_square_eq (rows : Stage → ℕ → Row) (K : ℕ)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (H : ℝ) (hH : 0<H) :
    mvp_rankErrorTotal rows K (fun h k s=>V h k s^2) p initial first batch =
      H*mvp_rankErrorTotal rows K (fun h k=>mvp_normalizedSquare H (V h k)) p initial first batch := by
  simp only [mvp_rankErrorTotal,mvp_rankPositiveError_square_eq K _ _ _ _ _ H hH,Finset.mul_sum]

/-- Lookup commutes with normalization because each rank selects at most one
actual value; the zero value fills exactly the absent ranks. -/
theorem mvp_lookupNormalizedSquare_slotVariance_le
    (rows : Stage → ℕ → Row) (K : ℕ) (V : Stage → Fin K → State → ℝ)
    (p : Stage → Row → FiniteDistribution State) (H : ℝ) (hH : 0<H)
    (hV : ∀ h k s,0≤V h k s∧V h k s≤H) :
    (∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
      ∑ h : Stage, ∑ r : Row,
        (p h r).variance (mvp_visitValueLookup (rows h) K r (2*2^j+i)
          (fun k=>mvp_normalizedSquare H (V h k)))) ≤
    4*(∑ h : Stage, ∑ k : Fin K,(p h (rows h k.val)).variance (V h k)) := by
  have hm (h : Stage) (r : Row) (u : ℕ) :
      mvp_visitValueLookup (rows h) K r u (fun k=>mvp_normalizedSquare H (V h k)) =
        mvp_normalizedSquare H (mvp_visitValueLookup (rows h) K r u (V h)) :=
    (mvp_visitValueLookup_map (rows h) K r u (V h) (mvp_normalizedSquare H)
      (mvp_normalizedSquare_zero H)).symm
  simp_rw [hm]
  exact mvp_allStages_normalizedSquare_slotVariance_le rows K V p H hH hV

/-- The square test keeps the same rows and empirical kernels as the original
learner. Normalization affects only the tested vectors. -/
theorem mvp_rankErrorTotal_square_bound (rows : Stage → ℕ → Row) (K : ℕ) (hK : 2≤K)
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Row → FiniteDistribution State)
    (batch : Stage → Row → Fin (Nat.log2 K) → FiniteDistribution State)
    (H I : ℝ) (hH : 0<H) (hI : 4≤I) (hV : ∀ h k s,0≤V h k s∧V h k s≤H)
    (he : mvp_rankSlotRadiusCondition rows K (fun h k=>mvp_normalizedSquare H (V h k))
      p initial first batch ((Fintype.card Stage:ℝ)*Fintype.card Row) H I) :
    let d := (Fintype.card Stage:ℝ)*Fintype.card Row
    let T := ∑ h : Stage, ∑ k : Fin K,(p h (rows h k.val)).variance (V h k)
    mvp_rankErrorTotal rows K (fun h k s=>V h k s^2) p initial first batch ≤
      Real.sqrt (d*H^2*I*T)+d*H^2*I := by
  let d := (Fintype.card Stage:ℝ)*Fintype.card Row
  let T := ∑ h : Stage, ∑ k : Fin K,(p h (rows h k.val)).variance (V h k)
  let VN := fun h k=>mvp_normalizedSquare H (V h k)
  change mvp_rankErrorTotal rows K (fun h k s=>V h k s^2) p initial first batch ≤
    Real.sqrt (d*H^2*I*T)+d*H^2*I
  have hd : 0≤d := by dsimp [d]; positivity
  have hI0 : 0≤I := by linarith only [hI]
  have hT : 0≤T := Finset.sum_nonneg (fun h _=>Finset.sum_nonneg (fun k _=>
    (p h (rows h k.val)).variance_nonneg _))
  have hVN : ∀ h k s,0≤VN h k s∧VN h k s≤H := fun h k=>
    mvp_normalizedSquare_bounds H hH (V h k) (hV h k)
  have hvars := mvp_lookupNormalizedSquare_slotVariance_le rows K V p H hH hV
  have hs := mvp_rankErrorSlots_radius rows K hK VN p initial first batch d H I (4*T)
    hd hH.le hI0 (by positivity) hvars he
  have hr := mvp_rankErrorTotal_rawRadius rows K VN p initial first batch H I (4*T) hH.le hVN hs
  have hb : mvp_rankErrorTotal rows K (fun h k s=>V h k s^2) p initial first batch ≤
      H*Real.sqrt (d*I*(1/8)*(4*T))+d*H^2*I/8+2*d*H^2 := by
    calc
      _ = H*mvp_rankErrorTotal rows K VN p initial first batch :=
        mvp_rankErrorTotal_square_eq rows K V p initial first batch H hH
      _ ≤ H*(Real.sqrt (d*I*(1/8)*(4*T))+d*H*I/8+2*d*H) :=
        mul_le_mul_of_nonneg_left hr hH.le
      _ = _ := by ring
  exact mvp_squareSlot_final_absorb d H I T _ hd hH.le hI hT hb

end StatisticalRL.OnlineRL
