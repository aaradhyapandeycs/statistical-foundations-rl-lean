import Formalization.Online.Regret.T3.OnlineRegretT3Freedman
import Formalization.Online.Regret.W1.OnlineW1PolicyVarianceBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Formalization.Online.Regret.T3.T3Definitions

/-! T₃ variance comparison, integer peeling, and first-radius probability helpers. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SourceStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SourceSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SourceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SourceActionDecidable : DecidableEq Action := Classical.decEq Action

/-- General variance comparison requiring no pointwise ordering: write
`U=P+(U-P)`, apply the two-term variance inequality, and bound the second
variance by its second moment. -/
theorem onlineVariance_le_two_variances_plus_square
    (d : FiniteDistribution State) (U P : State → ℝ) :
    d.variance U ≤ 2 * d.variance P + 2 * d.expectation (fun s => (U s - P s)^2) := by
  let D := fun s => U s - P s
  have hadd := d.sqrt_variance_add_le P D
  have heq : (fun s => P s + D s) = U := by
    funext s
    dsimp [D]
    ring
  rw [heq] at hadd
  have hsq := d.variance_le_expectation_sq D
  have hv := d.variance_nonneg P
  have hd := d.variance_nonneg D
  have hroot := sq_nonneg (Real.sqrt (d.variance P) - Real.sqrt (d.variance D))
  have hsqrtU : 0 ≤ Real.sqrt (d.variance U) := Real.sqrt_nonneg _
  have hsqrtP : 0 ≤ Real.sqrt (d.variance P) := Real.sqrt_nonneg _
  have hsqrtD : 0 ≤ Real.sqrt (d.variance D) := Real.sqrt_nonneg _
  have hU := Real.sq_sqrt (d.variance_nonneg U)
  have hP := Real.sq_sqrt hv
  have hD := Real.sq_sqrt hd
  nlinarith

/-- Deterministically compare the optimistic-continuation variance sum with
the actual selected-policy variance and squared-gap sums. No optimism event or
ordering hypothesis is needed. -/
theorem onlineActualT6UCB_le_policy_difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) :
    onlineActualT6UCB H K hH E initial fallback path δ c₁ c₂ ≤
      2 * onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ +
      2 * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let row := onlineActualStageRowSequence H K hH initial fallback planner path
  let d (h : Fin H) (k : Fin K) := (E h).transition (row h k.val).1 (row h k.val).2
  let U (h : Fin H) (k : Fin K) :=
    onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let P (h : Fin H) (k : Fin K) :=
    onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  change (∑ h : Fin H, ∑ k : Fin K, (d h k).variance (U h k)) ≤
    2 * (∑ h : Fin H, ∑ k : Fin K, (d h k).variance (P h k)) +
    2 * (∑ h : Fin H, ∑ k : Fin K,
      (d h k).expectation (fun s => (U h k s - P h k s)^2))
  have hpoint (h : Fin H) (k : Fin K) :
      (d h k).variance (U h k) ≤
        2 * (d h k).variance (P h k) +
        2 * (d h k).expectation (fun s => (U h k s - P h k s)^2) :=
    onlineVariance_le_two_variances_plus_square (d h k) (U h k) (P h k)
  calc
    _ ≤ ∑ h : Fin H, ∑ k : Fin K,
          (2 * (d h k).variance (P h k) +
            2 * (d h k).expectation (fun s => (U h k s - P h k s)^2)) := by
          apply Finset.sum_le_sum
          intro h hh
          apply Finset.sum_le_sum
          intro k hk
          exact hpoint h k
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- Integer-parameter Freedman peeling: choosing `δF=2*j*δ'` turns the
logarithm in the fixed-time theorem into exactly `log(1/δ')`. The condition
`2*j*δ'<1` is the nontrivial confidence branch. -/
theorem onlineT3Freedman_peeled_integer
    (H K j : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ δ' : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hj : 0 < j) (hδ' : 0 < δ') (hbranch : 2 * j * δ' < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - 2 * j * δ' ≤ μ.real {sample |
      |incrementSum (onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂)
          (K * H) sample| ≤
        Real.sqrt (8 * max
          (predictableSecondMomentSum μ ℱ
            (onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂) (K * H) sample)
          (((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^j) * Real.log (1 / δ')) +
        (4 / 3) * (H : ℝ) * Real.log (1 / δ')} := by
  classical
  dsimp
  let δF : ℝ := 2 * j * δ'
  have hδF : 0 < δF := by dsimp [δF]; positivity
  have hδF1 : δF < 1 := by simpa [δF] using hbranch
  have hfixed := onlineT3Freedman_fixed_time H K j hH E ρ fallback planner
    L c₁ c₂ δF hL hc₁ hc₂ hj hδF hδF1
  have hlog : Real.log (2 * (j : ℝ) / δF) = Real.log (1 / δ') := by
    congr 1
    dsimp [δF]
    field_simp
  rw [hlog] at hfixed
  exact hfixed

/-- Scalar conversion from the integer dyadic floor to the source T₃ RHS.
The log condition `L ≥ 2` is the source allocation's small-δ consequence. -/
theorem onlineT3_dyadic_freedman_radius_le_source
    (v H q L : ℝ) (hv : 0 ≤ v) (hH : 0 ≤ H)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hL : 2 ≤ L) :
    Real.sqrt (8 * max v (q * H^2) * L) + (4 / 3) * H * L ≤
      Real.sqrt (8 * v * L) + 5 * H * L := by
  have hL0 : 0 ≤ L := by linarith
  have harg : 0 ≤ 8 * max v (q * H^2) * L := by positivity
  have ha : 0 ≤ 8 * v * L := by positivity
  have hb : 0 ≤ 8 * q * H^2 * L := by positivity
  have hsplit : 8 * max v (q * H^2) * L ≤ 8 * v * L + 8 * q * H^2 * L := by
    have hm : max v (q * H^2) ≤ v + q * H^2 :=
      max_le (by nlinarith [mul_nonneg hq0 (sq_nonneg H)]) (by linarith)
    nlinarith
  have hrootadd : Real.sqrt (8 * v * L + 8 * q * H^2 * L) ≤
      Real.sqrt (8 * v * L) + Real.sqrt (8 * q * H^2 * L) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg (8 * v * L))
          (Real.sqrt_nonneg (8 * q * H^2 * L)),
        sq_nonneg (Real.sqrt (8 * v * L) - Real.sqrt (8 * q * H^2 * L))]
  have hsecond : Real.sqrt (8 * q * H^2 * L) ≤ 4 * H * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hsL := Real.sq_sqrt hL0
      have hprod : 0 ≤ (2 - q) * H^2 * L :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hq2) (sq_nonneg H)) hL0
      nlinarith
  have hsmall : 4 * Real.sqrt L + (4 / 3 : ℝ) * L ≤ 5 * L := by
    have hsL := Real.sq_sqrt hL0
    have hsq : (12 * Real.sqrt L)^2 ≤ (11 * L)^2 := by nlinarith
    have hn : 0 ≤ 12 * Real.sqrt L := by positivity
    have hm : 0 ≤ 11 * L := by positivity
    nlinarith
  calc
    Real.sqrt (8 * max v (q * H^2) * L) + (4 / 3) * H * L ≤
        Real.sqrt (8 * v * L) + Real.sqrt (8 * q * H^2 * L) +
          (4 / 3) * H * L := by
            have h := add_le_add_left
              ((Real.sqrt_le_sqrt hsplit).trans hrootadd) ((4 / 3) * H * L)
            nlinarith
    _ ≤ Real.sqrt (8 * v * L) + (4 * H * Real.sqrt L + (4 / 3) * H * L) := by
          have h := add_le_add_left hsecond (Real.sqrt (8 * v * L))
          nlinarith
    _ ≤ Real.sqrt (8 * v * L) + 5 * H * L := by
          have hmul := mul_le_mul_of_nonneg_left hsmall hH
          nlinarith

/-- The integer floor `Nat.log2 N` leaves a quotient in `[1,2)` for every
`N≥2`, with no real-log rounding premise. -/
theorem onlineT3_natLog2_ratio_bounds (N : ℕ) (hN : 2 ≤ N) :
    let j := Nat.log2 N
    0 < j ∧ 1 ≤ (N : ℝ) / (2 : ℝ)^j ∧ (N : ℝ) / (2 : ℝ)^j < 2 := by
  let j := Nat.log2 N
  have hNnz : N ≠ 0 := by omega
  have hpowlo := Nat.pow_log_le_self 2 hNnz
  have hpowhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hj : j = Nat.log 2 N := Nat.log2_eq_log_two
  have hjpos : 0 < j := by
    rw [hj]
    exact Nat.log_pos (by norm_num) (by omega)
  have hpowlo' : 2^j ≤ N := by simpa [j, Nat.log2_eq_log_two] using hpowlo
  have hpowhi' : N < 2^(j + 1) := by
    simpa [j, Nat.log2_eq_log_two] using hpowhi
  have hden : 0 < (2 : ℝ)^j := by positivity
  constructor
  · exact hjpos
  constructor
  · rw [le_div_iff₀ hden]
    have hcast : (2 : ℝ)^j ≤ (N : ℝ) := by exact_mod_cast hpowlo'
    simpa using hcast
  · rw [div_lt_iff₀ hden]
    have hpowhi'' : N < 2^j * 2 := by simpa [pow_succ] using hpowhi'
    exact_mod_cast (by simpa [Nat.mul_comm] using hpowhi'')

/-- The source confidence allocation has `δ'≤1/100` from positive S,A,H,K
and `0<δ≤1`; consequently its logarithmic factor is at least 2. -/
theorem onlineT3_sourceLog_ge_two
    (δ' : ℝ) (hδ' : 0 < δ') (hδsmall : δ' ≤ 1 / 100) :
    2 ≤ Real.log (1 / δ') := by
  have hinv : (100 : ℝ) ≤ 1 / δ' := by
    rw [le_div_iff₀ hδ']
    norm_num
    nlinarith
  have hlog100 : Real.log 100 ≤ Real.log (1 / δ') :=
    Real.log_le_log (by norm_num) hinv
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2' : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog16 : 2 ≤ Real.log 16 := by
    have hpow : (16 : ℝ) = 2^4 := by norm_num
    rw [hpow, Real.log_pow]
    exact le_trans (by norm_num) (le_of_lt
      (mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)))
  have h16 : (16 : ℝ) ≤ 100 := by norm_num
  have hlog : Real.log 16 ≤ Real.log 100 := Real.log_le_log (by norm_num) h16
  linarith

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- The fixed-time Freedman radius event with its integer dyadic variance floor. -/
def onlineFreedmanPeeledRadiusSet
    (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (n : ℕ) (B σ₂ : ℝ) (j : ℕ) (L : ℝ) : Set Ω :=
  {ω | |incrementSum X n ω| ≤
    Real.sqrt (8 * max (predictableSecondMomentSum μ ℱ X n ω)
      (σ₂ / (2 : ℝ)^j) * L) + (4 / 3) * B * L}

/-- The printed source radius event, before substituting a source variance
proxy into the random predictable-variance slot. -/
def onlineFreedmanSourceRadiusSet
    (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (n : ℕ) (B : ℝ) (L : ℝ) : Set Ω :=
  {ω | |incrementSum X n ω| ≤
    Real.sqrt (8 * predictableSecondMomentSum μ ℱ X n ω * L) + 5 * B * L}

/-- Convert the dyadic floor to any selected scalar bound `q ≤ 2`; the only
pointwise variance premise used here is the actual nonnegativity of its
conditional-expectation version. -/
theorem onlineFreedman_peeledRadiusSet_ae_subset_source
    (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (n : ℕ) (B σ₂ q L : ℝ) (j : ℕ)
    (hvar : ∀ᵐ ω ∂μ, 0 ≤ predictableSecondMomentSum μ ℱ X n ω)
    (hB : 0 ≤ B) (hσq : σ₂ / (2 : ℝ)^j = q * B^2)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hL : 2 ≤ L) :
    onlineFreedmanPeeledRadiusSet μ ℱ X n B σ₂ j L ≤ᵐ[μ]
      onlineFreedmanSourceRadiusSet μ ℱ X n B L := by
  filter_upwards [hvar] with ω hv
  intro h
  have hs := onlineT3_dyadic_freedman_radius_le_source
    (predictableSecondMomentSum μ ℱ X n ω) B q L hv hB hq0 hq2 hL
  dsimp [onlineFreedmanPeeledRadiusSet, onlineFreedmanSourceRadiusSet] at h ⊢
  rw [hσq] at h
  exact h.trans hs

/-- Probability transfers across the radius event inclusion under the same
measure; the source-specific caller supplies the fixed-time Freedman bound. -/
theorem onlineFreedman_peeledProbability_le_source
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (n : ℕ) (B σ₂ q L δ : ℝ) (j : ℕ)
    (hvar : ∀ᵐ ω ∂μ, 0 ≤ predictableSecondMomentSum μ ℱ X n ω)
    (hB : 0 ≤ B) (hσq : σ₂ / (2 : ℝ)^j = q * B^2)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hL : 2 ≤ L)
    (hfixed : 1 - δ ≤ μ.real
      (onlineFreedmanPeeledRadiusSet μ ℱ X n B σ₂ j L)) :
    1 - δ ≤ μ.real (onlineFreedmanSourceRadiusSet μ ℱ X n B L) := by
  have hsub := onlineFreedman_peeledRadiusSet_ae_subset_source
    μ ℱ X n B σ₂ q L j hvar hB hσq hq0 hq2 hL
  have hmono := ENNReal.toReal_mono
    (measure_ne_top μ (onlineFreedmanSourceRadiusSet μ ℱ X n B L))
    (measure_mono_ae hsub)
  exact hfixed.trans hmono

/-- Source T₃ first-radius event after integer peeling. The integer ratio and
small-confidence logarithm are derived from `j=Nat.log2(KH)` and δ'≤1/100. -/
theorem onlineT3_source_first_radius_probability
    (H K j : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (c₁ c₂ δ' : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hδ' : 0 < δ') (hδsmall : δ' ≤ 1 / 100)
    (hj : j = Nat.log2 (K * H)) (hbranch : 2 * j * δ' < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - 2 * j * δ' ≤ μ.real
      (onlineFreedmanSourceRadiusSet μ ℱ
        (onlineT3PaddedY H K hH E ρ fallback planner
          (Real.log (1 / δ')) c₁ c₂) (K * H) (H : ℝ) (Real.log (1 / δ'))) := by
  classical
  dsimp
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT3PaddedY H K hH E ρ fallback planner (Real.log (1 / δ')) c₁ c₂
  have hjpos : 0 < j := by
    rw [hj]
    exact (onlineT3_natLog2_ratio_bounds (K * H) hN).1
  let δF : ℝ := 2 * j * δ'
  have hδF : 0 < δF := by dsimp [δF]; positivity
  have hδF1 : δF < 1 := by simpa [δF] using hbranch
  have hL : 2 ≤ Real.log (1 / δ') :=
    onlineT3_sourceLog_ge_two δ' hδ' hδsmall
  have hL0 : 0 ≤ Real.log (1 / δ') := le_trans (by norm_num) hL
  have hfixedRaw := onlineT3Freedman_peeled_integer H K j hH E ρ fallback planner
    (Real.log (1 / δ')) c₁ c₂ δ' hL0 hc₁ hc₂ hjpos hδ' hbranch
  have hfixed : 1 - δF ≤ μ.real
      (onlineFreedmanPeeledRadiusSet μ ℱ X (K * H) (H : ℝ)
        ((K : ℝ) * (H : ℝ)^3) j (Real.log (1 / δ'))) := by
    change 1 - 2 * j * δ' ≤ μ.real {sample | _} at hfixedRaw
    simpa [δF, onlineFreedmanPeeledRadiusSet, μ, ℱ, X] using hfixedRaw
  have hvar := predictableSecondMomentSum_nonneg μ ℱ X (K * H)
  let N := K * H
  let q : ℝ := (N : ℝ) / (2 : ℝ)^j
  have hq := onlineT3_natLog2_ratio_bounds N hN
  dsimp [N] at hq
  rw [← hj] at hq
  rcases hq with ⟨_, hqone, hqtwo⟩
  have hq0 : 0 ≤ q := le_trans (by norm_num) hqone
  have hpow : 0 < (2 : ℝ)^j := by positivity
  have hσq : ((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^j = q * (H : ℝ)^2 := by
    dsimp [q, N]
    push_cast
    field_simp
  have hprob := onlineFreedman_peeledProbability_le_source μ ℱ X (K * H)
    (H : ℝ) ((K : ℝ) * (H : ℝ)^3) q (Real.log (1 / δ')) δF j
    hvar (by positivity) hσq hq0 (le_of_lt hqtwo) hL hfixed
  change 1 - 2 * j * δ' ≤ μ.real
    (onlineFreedmanSourceRadiusSet μ ℱ X (K * H) (H : ℝ) (Real.log (1 / δ')))
  exact hprob

end StatisticalRL.OnlineRL
