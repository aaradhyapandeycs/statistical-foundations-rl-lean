import Formalization.OfflineRL.FiniteVILCB.Deterministic
import Formalization.OfflineRL.VILCBBonusSumScalar

/-!
# Step 4: bounding `B = Σ_h ⟨d⋆_h, b⋆_h⟩` and the final arithmetic

Plan §3.2. Small states (`K d^b_h(s,π⋆) < 288ι`) use `b⋆ ≤ H` and `d⋆ ≤ C⋆ d^b`; large states use
the count lower bound `N ≥ K d^b/54`, the variance part of the row event, Cauchy–Schwarz over the
`H·S` pairs and (D3). Self-bounding gives `B ≤ 2√(216 c_b H Y) + 2(324 c_b + 288) Y` with
`Y = H² S C⋆ ι / K`; then `c_k = 69120 c_b` closes the gap bound.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

/-- Per-state scalar bound (both cases). -/
theorem per_state_bound {d db C K N cb ι v vh b H : ℝ} (hd0 : 0 ≤ d) (hdC : d ≤ C * db)
    (hC : 0 ≤ C) (hK : 0 < K) (hι : 0 < ι) (hcb : 2 ≤ cb) (hb0 : 0 ≤ b) (hbH : b ≤ H)
    (hv : 0 ≤ v)
    (hlarge : 288 * ι ≤ K * db → 0 < N ∧ K * db ≤ 54 * N ∧
      b ≤ max (Real.sqrt (cb * ι * vh / N)) (cb * H * ι / N) ∧ vh ≤ 2 * v + 2 * H ^ 2 * ι / N) :
    d * b ≤ Real.sqrt (108 * cb * C * ι / K * (d * v)) + (108 * cb + 288) * C * H * ι / K := by
  have hsq0 : 0 ≤ Real.sqrt (108 * cb * C * ι / K * (d * v)) := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := hb0.trans hbH
  by_cases hL : 288 * ι ≤ K * db
  · obtain ⟨hN, hdbN, hb, hvh⟩ := hlarge hL
    -- d / N ≤ 54 C / K
    have hdN : d / N ≤ 54 * C / K := by
      rw [div_le_div_iff₀ hN hK]
      nlinarith
    set p := Real.sqrt (2 * cb * ι * v / N) with hp
    have hp0 : 0 ≤ p := Real.sqrt_nonneg _
    have hx : Real.sqrt (cb * ι * vh / N) ≤ p + cb * H * ι / N := by
      rw [Real.sqrt_le_iff]
      have hq0 : 0 ≤ cb * H * ι / N := by positivity
      refine ⟨by positivity, ?_⟩
      have hp2 : p ^ 2 = 2 * cb * ι * v / N := Real.sq_sqrt (by positivity)
      have h1 : cb * ι * vh / N ≤ cb * ι * (2 * v + 2 * H ^ 2 * ι / N) / N := by
        apply div_le_div_of_nonneg_right _ hN.le
        exact mul_le_mul_of_nonneg_left hvh (by positivity)
      have h2 : cb * ι * (2 * v + 2 * H ^ 2 * ι / N) / N =
          2 * cb * ι * v / N + 2 * cb * (H * ι / N) ^ 2 := by field_simp
      have h3 : 2 * cb * (H * ι / N) ^ 2 ≤ (cb * H * ι / N) ^ 2 := by
        have : (cb * H * ι / N) ^ 2 = cb ^ 2 * (H * ι / N) ^ 2 := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        nlinarith
      nlinarith
    have hbxy : b ≤ p + 2 * (cb * H * ι / N) := by
      have hy0 : 0 ≤ cb * H * ι / N := by positivity
      rcases le_total (Real.sqrt (cb * ι * vh / N)) (cb * H * ι / N) with h | h
      · rw [max_eq_right h] at hb; linarith
      · rw [max_eq_left h] at hb; linarith
    have hdp : d * p ≤ Real.sqrt (108 * cb * C * ι / K * (d * v)) := by
      rw [hp, show d * Real.sqrt (2 * cb * ι * v / N) = Real.sqrt (d ^ 2 * (2 * cb * ι * v / N)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd0]]
      apply Real.sqrt_le_sqrt
      have : d ^ 2 * (2 * cb * ι * v / N) = (d / N) * (2 * cb * ι * (d * v)) := by
        field_simp
      rw [this]
      have hdv : 0 ≤ 2 * cb * ι * (d * v) := by positivity
      calc d / N * (2 * cb * ι * (d * v)) ≤ 54 * C / K * (2 * cb * ι * (d * v)) :=
            mul_le_mul_of_nonneg_right hdN hdv
        _ = 108 * cb * C * ι / K * (d * v) := by ring
    have hdy : d * (2 * (cb * H * ι / N)) ≤ 108 * cb * C * H * ι / K := by
      have : d * (2 * (cb * H * ι / N)) = (d / N) * (2 * cb * H * ι) := by field_simp
      rw [this]
      calc d / N * (2 * cb * H * ι) ≤ 54 * C / K * (2 * cb * H * ι) :=
            mul_le_mul_of_nonneg_right hdN (by positivity)
        _ = 108 * cb * C * H * ι / K := by ring
    have h288 : 0 ≤ 288 * C * H * ι / K := by positivity
    calc d * b ≤ d * (p + 2 * (cb * H * ι / N)) := mul_le_mul_of_nonneg_left hbxy hd0
      _ = d * p + d * (2 * (cb * H * ι / N)) := by ring
      _ ≤ Real.sqrt (108 * cb * C * ι / K * (d * v)) + 108 * cb * C * H * ι / K := add_le_add hdp hdy
      _ ≤ _ := by
          have : (108 * cb + 288) * C * H * ι / K = 108 * cb * C * H * ι / K + 288 * C * H * ι / K := by
            ring
          linarith
  · push_neg at hL
    have hdb : d ≤ C * (288 * ι / K) := by
      refine hdC.trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [le_div_iff₀ hK]
      linarith
    have h1 : d * b ≤ C * (288 * ι / K) * H :=
      (mul_le_mul_of_nonneg_left hbH hd0).trans (mul_le_mul_of_nonneg_right hdb hH0)
    have h2 : 0 ≤ 108 * cb * C * H * ι / K := by positivity
    have : (108 * cb + 288) * C * H * ι / K = 108 * cb * C * H * ι / K + C * (288 * ι / K) * H := by
      ring
    linarith

/-- Self-bounding: `B ≤ √(a + b B) + c` implies `B ≤ 2√a + b + 2c`. -/
theorem self_bounding {B a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (h : B ≤ Real.sqrt (a + b * B) + c) : B ≤ 2 * Real.sqrt a + b + 2 * c := by
  have h1 : Real.sqrt (a + b * B) ≤ Real.sqrt a + Real.sqrt (b * B) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt (mul_nonneg hb hB)
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (b * B)]
  have h3 : Real.sqrt (b * B) ≤ (b + B) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (b - B)]
  linarith

/-- Final arithmetic with `c_k = 69120 c_b`. -/
theorem final_arith {cb H Y ε : ℝ} (hcb : 16 ≤ cb) (hH : 1 ≤ H) (hε : 0 < ε) (hεH : ε ≤ H)
    (hY : 0 ≤ Y) (hHY : H * Y ≤ 5 * ε ^ 2 / (69120 * cb)) :
    4 * Real.sqrt (216 * cb * H * Y) + 4 * (324 * cb + 288) * Y ≤ ε := by
  have hcb0 : 0 < cb := by linarith
  have hs : Real.sqrt (216 * cb * H * Y) ≤ ε / 8 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : 216 * cb * (H * Y) ≤ 216 * cb * (5 * ε ^ 2 / (69120 * cb)) :=
      mul_le_mul_of_nonneg_left hHY (by positivity)
    have e : 216 * cb * (5 * ε ^ 2 / (69120 * cb)) = (ε / 8) ^ 2 := by field_simp; ring
    nlinarith
  have hY2 : Y ≤ 5 * ε / (69120 * cb) := by
    have h1 : Y ≤ H * Y := by nlinarith
    have h2 : 5 * ε ^ 2 / (69120 * cb) ≤ 5 * ε / (69120 * cb) * H := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have h3 : H * Y ≤ 5 * ε / (69120 * cb) * H := hHY.trans h2
    have h4 : Y * H ≤ 5 * ε / (69120 * cb) * H := by linarith
    exact le_of_mul_le_mul_right h4 (by linarith)
  have hlin : 4 * (324 * cb + 288) * Y ≤ ε / 2 := by
    have : 4 * (324 * cb + 288) * Y ≤ 4 * (324 * cb + 288) * (5 * ε / (69120 * cb)) :=
      mul_le_mul_of_nonneg_left hY2 (by positivity)
    refine this.trans ?_
    rw [show 4 * (324 * cb + 288) * (5 * ε / (69120 * cb)) = ε * ((6480 * cb + 5760) / (69120 * cb))
      by field_simp; ring]
    have : (6480 * cb + 5760) / (69120 * cb) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

section Bsum

variable {H : ℕ} {E : Fin H → EnvironmentStage S A} {cb ι L : ℝ}
  {cnt : Fin H → S → A → ℕ} {row : Fin H → S → A → FiniteDistribution S}

theorem sum_stageB (πs : Fin H → S → A) (d : ℕ → S → ℝ) :
    ∑ h ∈ Finset.range H, stageB E cb ι cnt row πs d h =
      ∑ p : Fin H × S, d p.1.val p.2 * pen E cb ι cnt row p.1 p.2 (πs p.1 p.2) := by
  rw [Finset.sum_range, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp [stageB, h.isLt]

/-- **Step 4.** `B ≤ 2√(216 c_b H Y) + 2(324 c_b + 288) Y`, `Y = H² S C ι / K`. -/
theorem Good.B_le (hG : Good E cb ι L cnt row) {πs : Fin H → S → A}
    {ρ : FiniteDistribution S} {d : ℕ → S → ℝ} (hd : Flow E πs ρ d)
    (db : Fin H → S → ℝ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hι : 0 < ι)
    (hdC : ∀ h : Fin H, ∀ s, d h.val s ≤ C * db h s)
    (hcnt : ∀ h s, 288 * ι ≤ K * db h s → K * db h s ≤ 54 * cnt h s (πs h s)) :
    ∑ h ∈ Finset.range H, stageB E cb ι cnt row πs d h ≤
      2 * Real.sqrt (216 * cb * H * ((H : ℝ) ^ 2 * Fintype.card S * C * ι / K)) +
        2 * (324 * cb + 288) * ((H : ℝ) ^ 2 * Fintype.card S * C * ι / K) := by
  set B := ∑ h ∈ Finset.range H, stageB E cb ι cnt row πs d h with hBdef
  set Y := (H : ℝ) ^ 2 * Fintype.card S * C * ι / K with hYdef
  have hcb := hG.cb16
  have hY0 : 0 ≤ Y := by positivity
  have hB0 : 0 ≤ B := by
    rw [hBdef, sum_stageB]
    exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hd.nonneg _ _) (pen_nonneg hG _ _ _)
  set c := 108 * cb * C * ι / K with hc
  have hc0 : 0 ≤ c := by positivity
  let v : Fin H × S → ℝ := fun p ↦
    ((E p.1).transition p.2 (πs p.1 p.2)).variance
      (vh E cb ι cnt row (p.1.val + 1))
  have hper : ∀ p : Fin H × S, d p.1.val p.2 * pen E cb ι cnt row p.1 p.2 (πs p.1 p.2) ≤
      Real.sqrt (c * (d p.1.val p.2 * v p)) + (108 * cb + 288) * C * H * ι / K := by
    rintro ⟨h, s⟩
    refine per_state_bound (hd.nonneg _ _) (hdC h s) hC hK hι (by linarith) (pen_nonneg hG _ _ _)
      (pen_le_H hG _ _ _) (FiniteDistribution.variance_nonneg _ _)
      (vh := (row h s (πs h s)).variance (vh E cb ι cnt row (h.val + 1)))
      (N := (cnt h s (πs h s) : ℝ)) ?_
    intro hlarge
    have hNle := hcnt h s hlarge
    have hpos : 0 < cnt h s (πs h s) := by
      have : (0 : ℝ) < cnt h s (πs h s) := by nlinarith [hG.L0]
      exact_mod_cast this
    have hNpos : (0 : ℝ) < cnt h s (πs h s) := by exact_mod_cast hpos
    refine ⟨hNpos, hNle, ?_, ?_⟩
    · unfold pen bonus
      rw [if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      exact min_le_left _ _
    · obtain ⟨-, hvar⟩ := hG.rows h s (πs h s) hpos
      have : 5 * (H : ℝ) ^ 2 * L / (3 * cnt h s (πs h s)) ≤
          2 * (H : ℝ) ^ 2 * ι / cnt h s (πs h s) := by
        rw [div_le_div_iff₀ (by positivity) hNpos]
        have := hG.Lι
        have := hG.L0
        have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
        have := mul_le_mul_of_nonneg_left (show 5 * L ≤ 6 * ι by linarith)
          (mul_nonneg hH2 hNpos.le)
        nlinarith
      exact hvar.trans (by linarith)
  -- sum over the H·S pairs
  have hsum : B ≤ Real.sqrt (c * Fintype.card (Fin H × S) *
      ∑ p : Fin H × S, d p.1.val p.2 * v p) +
        Fintype.card (Fin H × S) * ((108 * cb + 288) * C * H * ι / K) := by
    rw [hBdef, sum_stageB]
    refine (Finset.sum_le_sum fun p _ ↦ hper p).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact add_le_add (OfflineVILCB.Theorem63.sum_sqrt_le c hc0
      (fun p : Fin H × S ↦ d p.1.val p.2 * v p)
      fun p ↦ mul_nonneg (hd.nonneg _ _) (FiniteDistribution.variance_nonneg _ _)) le_rfl
  have hD3 := hG.variance_sum hd
  have hvsum : ∑ p : Fin H × S, d p.1.val p.2 * v p ≤ 2 * (H : ℝ) ^ 2 + 4 * H * B := by
    rw [Fintype.sum_prod_type]
    exact hD3
  have hcard : (Fintype.card (Fin H × S) : ℝ) = H * Fintype.card S := by
    simp [Fintype.card_prod]
  rw [hcard] at hsum
  have hmono : Real.sqrt (c * (H * Fintype.card S) * ∑ p : Fin H × S, d p.1.val p.2 * v p) ≤
      Real.sqrt (216 * cb * H * Y + 432 * cb * Y * B) := by
    apply Real.sqrt_le_sqrt
    have hcHS : 0 ≤ c * (H * Fintype.card S) := by positivity
    calc c * (H * Fintype.card S) * ∑ p : Fin H × S, d p.1.val p.2 * v p
        ≤ c * (H * Fintype.card S) * (2 * (H : ℝ) ^ 2 + 4 * H * B) :=
          mul_le_mul_of_nonneg_left hvsum hcHS
      _ = 216 * cb * H * Y + 432 * cb * Y * B := by
          rw [hc, hYdef]; field_simp; try ring
  have hlin : (H : ℝ) * Fintype.card S * ((108 * cb + 288) * C * H * ι / K) =
      (108 * cb + 288) * Y := by rw [hYdef]; field_simp; try ring
  rw [hlin] at hsum
  have hfin := self_bounding (a := 216 * cb * H * Y) (b := 432 * cb * Y) (c := (108 * cb + 288) * Y)
    (by positivity) (by positivity) hB0 (hsum.trans (by linarith [hmono]))
  linarith

end Bsum

end StatisticalRL.FiniteVILCB
