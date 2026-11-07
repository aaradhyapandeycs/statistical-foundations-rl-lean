import Formalization.OfflineRL.LCBQPessimism

/-!
# LCB-Q: the Q-error recursions of Lemma 6.9 on the martingale event

`lemma:Q-recursion-pessimistic-Q`, `offlineRL.tex:1866–1893`; proof `:4415–4528`.

Deterministic part. `martSum data (s,a) n` is the martingale term
`γ Σ_{i=1}^{n} η_i^n (P_{k_i} − P_{s,a}) V_{k_i−1}` of `eq:qstar-recursion-all-actions-lcbq`
(with the opposite sign), written as a sum over sample indices whose weights depend only on the
labels. On the event `martingaleEvent` (all `|martSum| ≤ 2√(H log(2SAT/δ')/(n(1-γ)²))`) and for
`c_b ≥ 4`, both recursions (`eq:qstar-recursion-lcbq` and
`eq:uniform-policy-pessimism-recursion`) hold for all `1 ≤ t ≤ T`, `(s,a)` and deterministic `π`.
The proof follows `:4436–4522`: the unrolled iterate `eq:unroll-q-lcbq`, the Bellman equations,
the penalty sum `eq:weighted-penalty-lcb`, and `4 log(2SAT/δ) ≤ c_b² log(SAT/δ)` when `T ≥ 2`; for
`T = 1` the martingale term is `0` because `V_0 = 0`.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The weight `γ η^n_{c+1}` of sample `u` (its `c+1`-st visit to `sa`, `c < n`) in the
martingale for `(sa, n)`; zero for other samples. It depends on the labels only. -/
noncomputable def martWeight (M : DiscountedMDP S A) (δ : ℝ) {T : ℕ}
    (data : Fin T → (S × A) × S) (sa : S × A) (n : ℕ) (u : Fin T) : ℝ :=
  if (data u).1 = sa ∧ Nat.count (visitPred data sa) u.val < n then
    M.discount * onlineQRateWeight (horizon M.discount (iota S A T δ)) n
      (Nat.count (visitPred data sa) u.val + 1)
  else 0

/-- `Σ_u γ η^n_{c_u+1} 1{u is one of the first n visits to sa} (V_u(s'_u) − P_{s_u,a_u} V_u)`,
i.e. `γ Σ_{i=1}^{n} η_i^n (P_{k_i} − P_{s,a}) V_{k_i − 1}`. -/
noncomputable def martSum (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (sa : S × A) (n : ℕ) : ℝ :=
  ∑ u : Fin T, martWeight M δ data sa n u *
    ((run M cb δ sel π₀ data u.val).V (data u).2 -
      (M.transition (data u).1.1 (data u).1.2).expectation (run M cb δ sel π₀ data u.val).V)

/-- The Azuma event of the proof of Lemma 6.9 (`offlineRL.tex:4478–4491`), at confidence `δ'`
per union over `(s, a, n)`. -/
def martingaleEvent (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) (δ' : ℝ) : Prop :=
  ∀ (s : S) (a : A) (n : ℕ), 1 ≤ n → n ≤ T →
    |martSum M cb δ sel π₀ data (s, a) n| ≤
      2 * Real.sqrt (horizon M.discount (iota S A T δ) *
        Real.log (2 * Fintype.card S * Fintype.card A * T / δ') / (n * (1 - M.discount) ^ 2))

/-- The upper recursion `eq:qstar-recursion-lcbq` (Lemma 6.9(a)) on one data sequence. -/
def upperRecursion (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ (s : S) (a : A), 0 < (run M cb δ sel π₀ data t).count s a →
    M.optimalityFixedPoint s a - (run M cb δ sel π₀ data t).Q s a ≤
      M.discount * ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
          onlineQRateWeight (horizon M.discount (iota S A T δ))
            ((run M cb δ sel π₀ data t).count s a) (i + 1) *
            (M.transition s a).expectation (fun s' =>
              M.trajectoryExpectedValue M.optimalGreedyPolicy s' -
                (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s') +
        3 * cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
          ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2))

section Reindex

variable {T : ℕ} (data : Fin T → (S × A) × S)

/-- Regrouping a sum over sample indices by visit rank: the first `n` visits to `sa`
(`n ≤ n_T(sa)`) are exactly `visitTime data sa i`, `i < n`. -/
theorem sum_fin_visits_eq (sa : S × A) (n : ℕ) (hn : n ≤ Nat.count (visitPred data sa) T)
    (G : ℕ → Fin T → ℝ) :
    ∑ u : Fin T, (if (data u).1 = sa ∧ Nat.count (visitPred data sa) u.val < n then
        G (Nat.count (visitPred data sa) u.val) u else 0) =
      ∑ i ∈ Finset.range n, (if h : visitTime data sa i < T then
        G i ⟨visitTime data sa i, h⟩ else 0) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun u _ => Nat.count (visitPred data sa) u.val)
    (fun i hi => ⟨visitTime data sa i, visitTime_lt data
      (lt_of_lt_of_le (Finset.mem_range.1 hi) hn)⟩) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact Finset.mem_range.2 hu.2.2
  · intro i hi
    have hi' := lt_of_lt_of_le (Finset.mem_range.1 hi) hn
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · obtain ⟨h, he⟩ := visitPred_visitTime data hi'
      exact he
    · rw [count_visitTime data hi']
      exact Finset.mem_range.1 hi
  · intro u hu
    rw [Finset.mem_filter] at hu
    have hp : visitPred data sa u.val := ⟨u.isLt, hu.2.1⟩
    exact Fin.ext (Nat.nth_count (p := visitPred data sa) hp)
  · intro i hi
    have hi' := lt_of_lt_of_le (Finset.mem_range.1 hi) hn
    exact count_visitTime data hi'
  · intro u hu
    rw [Finset.mem_filter] at hu
    have hp : visitPred data sa u.val := ⟨u.isLt, hu.2.1⟩
    have hv : visitTime data sa (Nat.count (visitPred data sa) u.val) = u.val :=
      Nat.nth_count (p := visitPred data sa) hp
    have hlt : visitTime data sa (Nat.count (visitPred data sa) u.val) < T := by
      rw [hv]; exact u.isLt
    rw [dif_pos hlt]
    congr 1
    exact Fin.ext hv.symm

end Reindex

section Algebra

theorem sqrt_ratio_eq {γ : ℝ} (hγ : γ < 1) (x : ℝ) (hx : 0 ≤ x) (j : ℝ) (hj : 0 ≤ j) :
    Real.sqrt (x / (j * (1 - γ) ^ 2)) = Real.sqrt x / (1 - γ) / Real.sqrt j := by
  rw [Real.sqrt_div hx, Real.sqrt_mul hj, Real.sqrt_sq (by linarith), div_div,
    mul_comm (1 - γ)]

/-- `eq:weighted-penalty-lcb`: `c_b√(Hι/(n(1-γ)²)) ≤ Σ_i η_i^n b_i ≤ 2c_b√(Hι/(n(1-γ)²))`. -/
theorem penalty_sum_bounds {cb γ ι : ℝ} (hcb : 0 ≤ cb) (hγ : γ < 1) (hι : 0 ≤ ι) {H n : ℕ}
    (hH : 0 < H) (hn : 0 < n) :
    cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2)) ≤
        ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) * penalty cb γ ι H (i + 1) ∧
      ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) * penalty cb γ ι H (i + 1) ≤
        2 * (cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2))) := by
  have hHι : 0 ≤ (H : ℝ) * ι := mul_nonneg (Nat.cast_nonneg _) hι
  set K := cb * Real.sqrt ((H : ℝ) * ι) / (1 - γ) with hK
  have hK0 : 0 ≤ K := by
    apply div_nonneg (mul_nonneg hcb (Real.sqrt_nonneg _)); linarith
  have hpen : ∀ j : ℕ, penalty cb γ ι H j = K * (1 / Real.sqrt j) := by
    intro j
    unfold penalty
    rw [sqrt_ratio_eq hγ _ hHι _ (Nat.cast_nonneg j), hK]
    ring
  have hx : cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2)) = K * (1 / Real.sqrt n) := by
    rw [sqrt_ratio_eq hγ _ hHι _ (Nat.cast_nonneg n), hK]
    ring
  have hsum : ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) * penalty cb γ ι H (i + 1) =
      K * ∑ j ∈ Finset.Icc 1 n, onlineQRateWeight H n j / Real.sqrt j := by
    rw [sum_Icc_one_eq_sum_range (fun j => onlineQRateWeight H n j / Real.sqrt j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpen]
    push_cast
    ring
  obtain ⟨h1, h2⟩ := onlineQRateWeight_sqrt_sum_bounds H n hH hn
  rw [hsum, hx]
  constructor
  · exact mul_le_mul_of_nonneg_left h1 hK0
  · calc K * ∑ j ∈ Finset.Icc 1 n, onlineQRateWeight H n j / Real.sqrt j ≤ K * (2 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ = 2 * (K * (1 / Real.sqrt n)) := by ring

/-- `2√(H L/(n(1-γ)²)) ≤ c_b √(H ι/(n(1-γ)²))` when `4L ≤ c_b² ι`. -/
theorem radius_le_of_log_le {cb ι L D : ℝ} (hcb : 0 ≤ cb) (H : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hL : 4 * L ≤ cb ^ 2 * ι) :
    2 * Real.sqrt (H * L / D) ≤ cb * Real.sqrt (H * ι / D) := by
  have h2 : (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have hc : cb = Real.sqrt (cb ^ 2) := (Real.sqrt_sq hcb).symm
  rw [h2, hc, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [mul_div_assoc', mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hD
  nlinarith

end Algebra

section Recursion

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

/-- The error identity behind `eq:qstar-recursion-all-actions-lcbq` and
`eq:policy-pessimism-decomposition`: for every `V'`, with `n = n_t(s,a) ≥ 1`,
`r(s,a) + γP_{s,a}V' − Q_t(s,a) = γΣ_i η_i^n P_{s,a}(V' − V_{k_i−1}) − martSum + Σ_i η_i^n b_i`. -/
theorem error_identity (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℕ} (ht : t ≤ T) (s : S) (a : A)
    (hn : 0 < (run M cb δ sel π₀ data t).count s a) (V' : S → ℝ) :
    M.reward s a + M.discount * (M.transition s a).expectation V' -
        (run M cb δ sel π₀ data t).Q s a =
      M.discount * ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
          onlineQRateWeight (horizon M.discount (iota S A T δ))
            ((run M cb δ sel π₀ data t).count s a) (i + 1) *
            (M.transition s a).expectation (fun s' =>
              V' s' - (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s') -
        martSum M cb δ sel π₀ data (s, a) ((run M cb δ sel π₀ data t).count s a) +
        ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
          onlineQRateWeight (horizon M.discount (iota S A T δ))
            ((run M cb δ sel π₀ data t).count s a) (i + 1) *
            penalty cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ)) (i + 1) := by
  set n := (run M cb δ sel π₀ data t).count s a with hndef
  set H := horizon M.discount (iota S A T δ) with hHdef
  have hT : 1 ≤ T := by
    by_contra h
    have hT0 : T = 0 := by omega
    have hc := run_count M cb δ sel π₀ data ht s a
    rw [← hndef] at hc
    have : Nat.count (visitPred data (s, a)) t = 0 := by
      rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨hx, -⟩
      omega
    omega
  have hcnt : n = Nat.count (visitPred data (s, a)) t := run_count M cb δ sel π₀ data ht s a
  have hnT : n ≤ Nat.count (visitPred data (s, a)) T := by
    rw [hcnt]; exact Nat.count_monotone _ ht
  -- unrolled iterate
  have hQ := run_Q_unroll M cb δ sel π₀ data ht s a
  rw [← hndef] at hQ
  -- martingale term as a sum over visit ranks
  have hmart : martSum M cb δ sel π₀ data (s, a) n =
      ∑ i ∈ Finset.range n, M.discount * onlineQRateWeight H n (i + 1) *
        (if h : visitTime data (s, a) i < T then
          (run M cb δ sel π₀ data (visitTime data (s, a) i)).V
              (data ⟨visitTime data (s, a) i, h⟩).2 -
            (M.transition s a).expectation (run M cb δ sel π₀ data (visitTime data (s, a) i)).V
        else 0) := by
    unfold martSum martWeight
    have := sum_fin_visits_eq data (s, a) n hnT
      (fun c u => M.discount * onlineQRateWeight H n (c + 1) *
        ((run M cb δ sel π₀ data u.val).V (data u).2 -
          (M.transition s a).expectation (run M cb δ sel π₀ data u.val).V))
    rw [← hHdef]
    convert this using 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs with hu
      · rw [hu.1]
      · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [mul_assoc]
  have hw1 : ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) = 1 :=
    sum_rateWeight_range_eq_one (horizon_pos M hT hδ hδ1) hn
  have hcoef : M.reward s a + M.discount * (M.transition s a).expectation V' =
      ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) *
        (M.reward s a + M.discount * (M.transition s a).expectation V') := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have hterm : ∑ i ∈ Finset.range n, (onlineQRateWeight H n (i + 1) *
        (M.reward s a + M.discount * (M.transition s a).expectation V') -
        onlineQRateWeight H n (i + 1) * visitTarget M cb δ sel π₀ data (s, a) i) =
      ∑ i ∈ Finset.range n, (M.discount * (onlineQRateWeight H n (i + 1) *
          (M.transition s a).expectation (fun s' =>
            V' s' - (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s')) -
        M.discount * onlineQRateWeight H n (i + 1) *
          (if h : visitTime data (s, a) i < T then
            (run M cb δ sel π₀ data (visitTime data (s, a) i)).V
                (data ⟨visitTime data (s, a) i, h⟩).2 -
              (M.transition s a).expectation (run M cb δ sel π₀ data (visitTime data (s, a) i)).V
          else 0) +
        onlineQRateWeight H n (i + 1) * penalty cb M.discount (iota S A T δ) H (i + 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < Nat.count (visitPred data (s, a)) T :=
      lt_of_lt_of_le (Finset.mem_range.1 hi) hnT
    have hlt := visitTime_lt data hi'
    rw [dif_pos hlt, visitTarget, dif_pos hlt, FiniteDistribution.expectation_sub]
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hterm
  rw [hQ, hmart, hcoef]
  linarith

/-- `Q^π(s,a) = r(s,a) + γ P_{s,a} V^π` for the actual trajectory Q and V. -/
theorem trajectoryQ_eq_reward_add (π : StationaryPolicy S A) (s : S) (a : A) :
    M.trajectoryExpectedQ π s a =
      M.reward s a + M.discount * (M.transition s a).expectation (M.trajectoryExpectedValue π) := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, M.policyFixedPoint_eq_reward_add_value,
    M.trajectoryExpectedValue_eq_valueFixedPoint]

/-- `Q⋆(s,a) = r(s,a) + γ P_{s,a} V⋆`. -/
theorem optQ_eq_reward_add (s : S) (a : A) :
    M.optimalityFixedPoint s a =
      M.reward s a + M.discount *
        (M.transition s a).expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) := by
  letI : Nonempty A := M.action_nonempty
  rw [← M.optimalGreedy_trajectoryQ s a]
  exact trajectoryQ_eq_reward_add M _ s a

theorem martSum_eq_zero_of_T_eq_one (hT : T = 1) (sa : S × A) (n : ℕ) :
    martSum M cb δ sel π₀ data sa n = 0 := by
  unfold martSum
  apply Finset.sum_eq_zero
  intro u _
  have hu : u.val = 0 := by have := u.isLt; omega
  rw [hu, run_zero]
  simp [init]

/-- On the martingale event, `|martSum| ≤ c_b √(Hι/(n(1-γ)²))` for every realised count
`n = n_t(s,a) ≥ 1`, provided `c_b ≥ 4` (`offlineRL.tex:4478–4491`, with the union over
`(s,a,n)`). -/
theorem martSum_le_of_martingaleEvent (hcb : 4 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hE : martingaleEvent M cb δ sel π₀ data δ) {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ T)
    (s : S) (a : A) (hn : 0 < (run M cb δ sel π₀ data t).count s a) :
    |martSum M cb δ sel π₀ data (s, a) ((run M cb δ sel π₀ data t).count s a)| ≤
      cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) := by
  have hT : 1 ≤ T := le_trans ht1 htT
  have hι := iota_pos M hT hδ hδ1
  have hcb0 : 0 ≤ cb := by linarith
  rcases Nat.lt_or_ge T 2 with hT1 | hT2
  · rw [martSum_eq_zero_of_T_eq_one M cb δ sel π₀ data (by omega), abs_zero]
    exact mul_nonneg hcb0 (Real.sqrt_nonneg _)
  · have hnT : (run M cb δ sel π₀ data t).count s a ≤ T := by
      rw [run_count M cb δ sel π₀ data htT]
      exact (Nat.count_le _).trans htT
    have h := hE s a _ hn hnT
    refine h.trans (radius_le_of_log_le hcb0 _ (Nat.cast_nonneg _) (by positivity) ?_)
    haveI := M.state_nonempty
    haveI := M.action_nonempty
    have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hT2' : (2 : ℝ) ≤ T := by exact_mod_cast hT2
    set X : ℝ := (Fintype.card S : ℝ) * Fintype.card A * T with hX
    have hX2 : 2 ≤ X := by
      have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := by nlinarith
      nlinarith
    have hXδ : 2 ≤ X / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    have hlog2 : Real.log 2 ≤ iota S A T δ := by
      unfold iota
      rw [← hX]
      exact Real.log_le_log (by norm_num) hXδ
    have hL : Real.log (2 * Fintype.card S * Fintype.card A * T / δ) =
        Real.log 2 + iota S A T δ := by
      unfold iota
      rw [← hX, show 2 * (Fintype.card S : ℝ) * Fintype.card A * T / δ = 2 * (X / δ) by
        rw [hX]; ring]
      exact Real.log_mul (by norm_num) (by positivity)
    rw [hL]
    have hcb2 : 16 ≤ cb ^ 2 := by nlinarith
    nlinarith

/-- **Lemma 6.9, deterministic part**: on the martingale event (at confidence `δ`) and for
`c_b ≥ 4`, both recursions of `lemma:Q-recursion-pessimistic-Q` hold. -/
theorem recursion_of_martingaleEvent (hcb : 4 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hE : martingaleEvent M cb δ sel π₀ data δ) :
    upperRecursion M cb δ sel π₀ data ∧ lowerRecursion M cb δ sel π₀ data := by
  have hcb0 : 0 ≤ cb := by linarith
  constructor
  · intro t ht1 htT s a hn
    have hT : 1 ≤ T := le_trans ht1 htT
    have hι := iota_pos M hT hδ hδ1
    have hH := horizon_pos M hT hδ hδ1
    have hid := error_identity M cb δ sel π₀ data hδ hδ1 htT s a hn
      (M.trajectoryExpectedValue M.optimalGreedyPolicy)
    rw [← optQ_eq_reward_add] at hid
    have hm := martSum_le_of_martingaleEvent M cb δ sel π₀ data hcb hδ hδ1 hE ht1 htT s a hn
    have hp := (penalty_sum_bounds hcb0 M.discount_lt_one hι.le hH hn).2
    have h3 : 3 * cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) =
        cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
          ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) +
        2 * (cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
          ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2))) := by ring
    have hm' := (abs_le.mp hm).1
    rw [hid, h3]
    linarith
  · intro t ht1 htT s a π
    have hT : 1 ≤ T := le_trans ht1 htT
    have hι := iota_pos M hT hδ hδ1
    have hH := horizon_pos M hT hδ hδ1
    rcases Nat.eq_zero_or_pos ((run M cb δ sel π₀ data t).count s a) with hn0 | hn
    · have hQ := run_Q_unroll M cb δ sel π₀ data htT s a
      rw [hn0, Finset.range_zero, Finset.sum_empty] at hQ
      rw [hn0, Finset.range_zero, Finset.sum_empty, mul_zero, hQ, sub_zero,
        M.trajectoryExpectedQ_eq_policyFixedPoint]
      exact (M.policyFixedPoint_bounds _ s a).1
    · have hid := error_identity M cb δ sel π₀ data hδ hδ1 htT s a hn
        (M.trajectoryExpectedValue (detPolicy π))
      rw [← trajectoryQ_eq_reward_add] at hid
      have hm := martSum_le_of_martingaleEvent M cb δ sel π₀ data hcb hδ hδ1 hE ht1 htT s a hn
      have hp := (penalty_sum_bounds hcb0 M.discount_lt_one hι.le hH hn).1
      have hm' := (abs_le.mp hm).2
      rw [hid]
      linarith

end Recursion

end StatisticalRL.OfflineRL.LCBQ
