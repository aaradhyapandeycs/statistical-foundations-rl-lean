import Formalization.MultiAgent.LowerBound.HardTesting

/-!
# Corrected Theorem 7.8: product prior, Bayes risk and counting

* `prior ref θ = ∏_c w(θ_c)` with `w(ref) = 1/2`, `w(j) = 1/(2(n−1))`; `prior_resample` re-draws one
  coordinate from `w` without changing a prior average.
* `hard_bayes`: for every deterministic learner (adaptive randomized query rule, output a function of
  the history), the prior average of `P_θ(gap > ε)` is at least `1/4`, under the KL budget
  `64 κ N ≤ (n − 1)(S − 1)⌊H/2⌋`, `κ = 4λ²/H³`, and `ε < λ/512`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL OnlineLowerBound AdaptiveKL GenerativeLowerBound

section Prior

variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}

/-- Product prior on `C → Fin n`. -/
noncomputable def prior (ref : Fin n) (θ : C → Fin n) : ℝ := ∏ c, wt ref (θ c)

omit [DecidableEq C] in
theorem prior_nonneg (hn : 2 ≤ n) (ref : Fin n) (θ : C → Fin n) : 0 ≤ prior ref θ :=
  Finset.prod_nonneg fun c _ => wt_nonneg hn ref (θ c)

theorem sum_prior (hn : 2 ≤ n) (ref : Fin n) : ∑ θ : C → Fin n, prior ref θ = 1 := by
  unfold prior
  have h := Finset.prod_univ_sum (fun _ : C => (Finset.univ : Finset (Fin n)))
    (fun _ b => wt ref b)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp [sum_wt hn ref]

/-- Re-drawing coordinate `c` from `w` leaves prior averages unchanged. -/
theorem prior_resample (ref : Fin n) (hn : 2 ≤ n) (G : (C → Fin n) → ℝ) (c : C) :
    ∑ θ, prior ref θ * G θ = ∑ θ, prior ref θ * ∑ b, wt ref b * G (Function.update θ c b) := by
  set e := Equiv.funSplitAt c (Fin n) with he
  have hval : ∀ a r, e.symm (a, r) c = a := by
    intro a r; simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
  have hoff : ∀ a r (i : {i // i ≠ c}), e.symm (a, r) i.1 = r i := by
    intro a r i; simp [he, Equiv.funSplitAt, Equiv.piSplitAt, i.2]
  have hρ : ∀ a r, prior ref (e.symm (a, r)) = wt ref a * ∏ i : {i // i ≠ c}, wt ref (r i) := by
    intro a r
    unfold prior
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ c, hval]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hoff]
  have hup : ∀ a r b, Function.update (e.symm (a, r)) c b = e.symm (b, r) := by
    intro a r b
    funext i
    by_cases hi : i = c
    · subst hi; rw [Function.update_self, hval]
    · rw [Function.update_of_ne hi]
      exact (hoff a r ⟨i, hi⟩).trans (hoff b r ⟨i, hi⟩).symm
  set Q : ({i // i ≠ c} → Fin n) → ℝ := fun r => ∏ i : {i // i ≠ c}, wt ref (r i)
  set X : ({i // i ≠ c} → Fin n) → ℝ := fun r => ∑ b, wt ref b * G (e.symm (b, r))
  have hL : ∑ θ, prior ref θ * G θ = ∑ r, Q r * X r := by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hρ, X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hR : ∑ θ, prior ref θ * ∑ b, wt ref b * G (Function.update θ c b) = ∑ r, Q r * X r := by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hρ, hup]
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_wt hn ref, one_mul]
  rw [hL, hR]

end Prior

theorem sum_fin_filter_lt (H k : ℕ) (hk : k ≤ H) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.univ.filter (fun t : Fin H => (t : ℕ) < k), f t = ∑ j ∈ Finset.range k, f j := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0) H,
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem margProb_le_one {m : ℕ} {A : Fin m → ℕ} (d : FiniteDistribution ((i : Fin m) → Fin (A i)))
    (i : Fin m) (b : Fin (A i)) : margProb d i b ≤ 1 := by
  rw [← sum_margProb d i]
  exact Finset.single_le_sum (fun b _ => margProb_nonneg d i b) (Finset.mem_univ _)

section Bayes

variable {m S H : ℕ} {A : Fin m → ℕ} {istar : Fin m} {z : Fin S} {hH : 2 ≤ H} {lam : ℝ}
  {hl : 0 < lam} {hlH : lam ≤ (H : ℝ) / 2}

/-- The miss indicator `1[σ̂_c(θ_c) ≤ 1/2]`. -/
noncomputable def missI {N : ℕ} (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A)
    (θ : Fin S × Fin H → Fin (A istar)) (c : Fin S × Fin H)
    (hist : Fin N → Query m S H A × Fin S) : ℝ :=
  if hitEv out c (θ c) hist then 0 else 1

/-- Pointwise: many misses on one chain force a large gap. -/
theorem gap_of_misses (cst : ℝ) (hcst : 0 ≤ cst)
    (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ) {N : ℕ}
    (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A)
    (θ : Fin S × Fin H → Fin (A istar)) (hist : Fin N → Query m S H A × Fin S) (x : Fin S)
    (hx : x ≠ z) :
    lam / (32 * (H : ℝ)) * ∑ t ∈ Finset.univ.filter (fun t : Fin H => (t : ℕ) < H / 2),
        missI (istar := istar) out θ (x, t) hist ≤
      gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) := by
  have hg := hard_chain_gap (hH := hH) (hl := hl) (hlH := hlH) cst hcst rest θ (out hist) x hx
  refine le_trans ?_ hg
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  rw [Finset.mul_sum]
  have hfun : ∀ t : Fin H, lam / (32 * (H : ℝ)) * missI (istar := istar) out θ (x, t) hist =
      (fun j : ℕ => lam / (32 * (H : ℝ)) * (if 1 / 2 < margProb (out hist (1 + j) x) istar
        (θ (x, stepIdx hH (1 + j))) then 0 else 1)) t := by
    intro t
    simp only [missI, hitEv, stepIdx_one_add hH t t.isLt]
  rw [Finset.sum_congr rfl fun t _ => hfun t]
  refine le_trans (le_of_eq (sum_fin_filter_lt H (H / 2) (Nat.div_le_self H 2)
    (fun j : ℕ => lam / (32 * (H : ℝ)) * (if 1 / 2 < margProb (out hist (1 + j) x) istar
        (θ (x, stepIdx hH (1 + j))) then 0 else 1)))) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hm := margProb_le_one (out hist (1 + j) x) istar (θ (x, stepIdx hH (1 + j)))
  have hy : lam / (32 * (H : ℝ)) = (H : ℝ) / 8 * ((1 / 2) * (lam / (2 * (H : ℝ) ^ 2))) := by
    field_simp; ring
  have hy0 : 0 ≤ lam / (2 * (H : ℝ) ^ 2) := by positivity
  have hH8 : 0 ≤ (H : ℝ) / 8 := by positivity
  rw [hy]
  split_ifs with hh
  · rw [mul_zero]; exact mul_nonneg hH8 (mul_nonneg (by linarith) hy0)
  · rw [mul_one]
    push_neg at hh
    apply mul_le_mul_of_nonneg_left _ hH8
    exact mul_le_mul_of_nonneg_right (by linarith) hy0

/-- **Bayes bound for one deterministic learner.** -/
theorem hard_bayes (cst : ℝ) (hcst : 0 ≤ cst)
    (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (hS : 2 ≤ S) (hn : 2 ≤ A istar) (ref : Fin (A istar)) (href : (ref : ℕ) = 0)
    (ε : ℝ) (hε : ε < lam / 512) (N : ℕ)
    (hN : 64 * (4 * lam ^ 2 / (H : ℝ) ^ 3) * N ≤
      ((A istar : ℝ) - 1) * ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ))
    (rule : (t : ℕ) → (Fin t → Query m S H A × Fin S) → FiniteDistribution (Query m S H A))
    (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A) :
    (1 : ℝ) / 4 ≤ ∑ θ : Fin S × Fin H → Fin (A istar), prior ref θ *
      evProb (interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest θ)) N)
        (fun hist => ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist)) := by
  classical
  set P : (Fin S × Fin H → Fin (A istar)) → FiniteDistribution (Fin N → Query m S H A × Fin S) :=
    fun θ => interactionLaw rule (genEnv (hardGame istar z hH lam hl hlH cst rest θ)) N with hP
  set κ : ℝ := 4 * lam ^ 2 / (H : ℝ) ^ 3 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hn' : (2 : ℝ) ≤ A istar := by exact_mod_cast hn
  have hM : (0 : ℝ) < (A istar : ℝ) - 1 := by linarith
  have hS' : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  set T : Finset (Fin H) := Finset.univ.filter (fun t : Fin H => (t : ℕ) < H / 2) with hT
  set Cp : Finset (Fin S × Fin H) := (Finset.univ.erase z) ×ˢ T with hCp
  have hTcard : (T.card : ℝ) = ((H / 2 : ℕ) : ℝ) := by
    have := sum_fin_filter_lt H (H / 2) (Nat.div_le_self H 2) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at this
    rw [← hT] at this
    exact this
  have hEcard : ((Finset.univ.erase z).card : ℝ) = (S : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  set K : ℝ := ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ) with hK
  have hCcard : (Cp.card : ℝ) = K := by
    rw [hCp, Finset.card_product]; push_cast; rw [hEcard, hTcard]
  have hH2 : (H : ℝ) / 4 ≤ ((H / 2 : ℕ) : ℝ) := by
    have h1 : H ≤ 4 * (H / 2) := by omega
    have h2 : (H : ℝ) ≤ 4 * ((H / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hKpos : 0 < K := by
    rw [hK]; exact mul_pos (by linarith) (by linarith)
  have hρ1 := sum_prior (C := Fin S × Fin H) hn ref
  have hρ0 := prior_nonneg (C := Fin S × Fin H) hn ref
  -- (a) per-coordinate prior bound on the hit probability
  have hcoord : ∀ c : Fin S × Fin H,
      ∑ θ, prior ref θ * evProb (P θ) (hitEv out c (θ c)) ≤
        17 / 32 + 2 * κ / ((A istar : ℝ) - 1) * ∑ θ, prior ref θ * expCount (P θ) c := by
    intro c
    rw [prior_resample ref hn (fun θ => evProb (P θ) (hitEv out c (θ c))) c]
    simp only [Function.update_self]
    have h1 : ∀ θ, ∑ b, wt ref b * evProb (P (Function.update θ c b)) (hitEv out c b) ≤
        17 / 32 + κ * expCount (P (Function.update θ c ref)) c / ((A istar : ℝ) - 1) :=
      fun θ => hard_coord_bayes cst rest hn ref href rule out θ c
    have h2 : ∑ θ, prior ref θ * expCount (P (Function.update θ c ref)) c ≤
        2 * ∑ θ, prior ref θ * expCount (P θ) c := by
      rw [prior_resample ref hn (fun θ => expCount (P θ) c) c, Finset.mul_sum]
      refine Finset.sum_le_sum fun θ _ => ?_
      have hsingle : wt ref ref * expCount (P (Function.update θ c ref)) c ≤
          ∑ b, wt ref b * expCount (P (Function.update θ c b)) c :=
        Finset.single_le_sum (f := fun b => wt ref b * expCount (P (Function.update θ c b)) c)
          (fun b _ => mul_nonneg (wt_nonneg hn ref b) (expCount_nonneg _ _)) (Finset.mem_univ ref)
      have hw : wt ref ref = 1 / 2 := by simp [wt]
      rw [hw] at hsingle
      have := mul_le_mul_of_nonneg_left hsingle (hρ0 θ)
      linarith
    calc ∑ θ, prior ref θ * ∑ b, wt ref b * evProb (P (Function.update θ c b)) (hitEv out c b)
        ≤ ∑ θ, prior ref θ * (17 / 32 + κ * expCount (P (Function.update θ c ref)) c /
            ((A istar : ℝ) - 1)) :=
          Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (h1 θ) (hρ0 θ)
      _ = 17 / 32 + κ / ((A istar : ℝ) - 1) *
            ∑ θ, prior ref θ * expCount (P (Function.update θ c ref)) c := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hρ1, one_mul,
            Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun θ _ => ?_
          ring
      _ ≤ 17 / 32 + κ / ((A istar : ℝ) - 1) * (2 * ∑ θ, prior ref θ * expCount (P θ) c) := by
          have : 0 ≤ κ / ((A istar : ℝ) - 1) := div_nonneg hκ0 hM.le
          linarith [mul_le_mul_of_nonneg_left h2 this]
      _ = _ := by ring
  -- (b) expected number of misses
  set W : (Fin S × Fin H → Fin (A istar)) → (Fin N → Query m S H A × Fin S) → ℝ :=
    fun θ hist => ∑ c ∈ Cp, missI (istar := istar) out θ c hist with hW
  have hmiss : ∀ θ c, ∑ hist, (P θ).prob hist * missI (istar := istar) out θ c hist =
      1 - evProb (P θ) (hitEv out c (θ c)) := by
    intro θ c
    have : ∀ hist, (P θ).prob hist * missI (istar := istar) out θ c hist =
        (P θ).prob hist - (P θ).prob hist * (if hitEv out c (θ c) hist then 1 else 0) := by
      intro hist; unfold missI; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, (P θ).sum_prob]
    rfl
  have hEW : 7 / 16 * K ≤ ∑ θ, prior ref θ * ∑ hist, (P θ).prob hist * W θ hist := by
    have e1 : ∑ θ, prior ref θ * ∑ hist, (P θ).prob hist * W θ hist =
        ∑ c ∈ Cp, (1 - ∑ θ, prior ref θ * evProb (P θ) (hitEv out c (θ c))) := by
      have hθ : ∀ θ, prior ref θ * ∑ hist, (P θ).prob hist * W θ hist =
          ∑ c ∈ Cp, prior ref θ * (1 - evProb (P θ) (hitEv out c (θ c))) := by
        intro θ
        rw [← Finset.mul_sum]
        congr 1
        simp only [hW, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => hmiss θ c
      rw [Finset.sum_congr rfl fun θ _ => hθ θ, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hρ1]
    rw [e1]
    have hcount : ∑ c ∈ Cp, ∑ θ, prior ref θ * expCount (P θ) c ≤ N := by
      calc ∑ c ∈ Cp, ∑ θ, prior ref θ * expCount (P θ) c
          ≤ ∑ c, ∑ θ, prior ref θ * expCount (P θ) c :=
            Finset.sum_le_univ_sum_of_nonneg fun c => Finset.sum_nonneg fun θ _ =>
              mul_nonneg (hρ0 θ) (expCount_nonneg _ _)
        _ = ∑ θ, prior ref θ * N := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun θ _ => ?_
            rw [← Finset.mul_sum, sum_expCount]
        _ = N := by rw [← Finset.sum_mul, hρ1, one_mul]
    calc 7 / 16 * K ≤ 15 / 32 * K - 2 * κ / ((A istar : ℝ) - 1) * N := by
          have : 2 * κ / ((A istar : ℝ) - 1) * N ≤ K / 32 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ hM (by norm_num)]
            nlinarith
          linarith
      _ = ∑ c ∈ Cp, (15 / 32 : ℝ) - 2 * κ / ((A istar : ℝ) - 1) * N := by
          rw [Finset.sum_const, nsmul_eq_mul, hCcard]; ring
      _ ≤ ∑ c ∈ Cp, (15 / 32 : ℝ) - 2 * κ / ((A istar : ℝ) - 1) *
            ∑ c ∈ Cp, ∑ θ, prior ref θ * expCount (P θ) c := by
          have : 0 ≤ 2 * κ / ((A istar : ℝ) - 1) := div_nonneg (by linarith) hM.le
          linarith [mul_le_mul_of_nonneg_left hcount this]
      _ ≤ ∑ c ∈ Cp, (1 - ∑ θ, prior ref θ * evProb (P θ) (hitEv out c (θ c))) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun c _ => ?_
          linarith [hcoord c]
  -- (c) pointwise: `W ≤ K/4 + (3K/4) · 1[gap > ε]`
  have hpt : ∀ θ hist, W θ hist ≤ K / 4 + 3 * K / 4 *
      (if ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) then 1 else 0) := by
    intro θ hist
    have hWle : W θ hist ≤ K := by
      rw [← hCcard, hW]
      calc ∑ c ∈ Cp, missI (istar := istar) out θ c hist ≤ ∑ c ∈ Cp, (1 : ℝ) :=
            Finset.sum_le_sum fun c _ => by unfold missI; split_ifs <;> norm_num
        _ = Cp.card := by simp
    by_cases hbig : K / 4 ≤ W θ hist
    · -- some chain has at least `|T|/4` misses
      have hex : ∃ x ∈ Finset.univ.erase z, (T.card : ℝ) / 4 ≤
          ∑ t ∈ T, missI (istar := istar) out θ (x, t) hist := by
        by_contra hcon
        push_neg at hcon
        have hne : (Finset.univ.erase z).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]; omega
        have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
        rw [Finset.sum_const, nsmul_eq_mul, hEcard, hTcard] at hlt
        have hWsum : W θ hist = ∑ x ∈ Finset.univ.erase z, ∑ t ∈ T,
            missI (istar := istar) out θ (x, t) hist := by
          simp only [hW, hCp]
          exact Finset.sum_product _ _ _
        rw [hK] at hbig
        linarith
      obtain ⟨x, hxmem, hx⟩ := hex
      have hxz : x ≠ z := Finset.ne_of_mem_erase hxmem
      have hgap := gap_of_misses (hl := hl) (hlH := hlH) (hH := hH) cst hcst rest out θ hist x hxz
      have hlpos : 0 < lam / (32 * (H : ℝ)) := by positivity
      have hge : lam / 512 ≤ lam / (32 * (H : ℝ)) * ∑ t ∈ T, missI (istar := istar) out θ (x, t) hist := by
        calc lam / 512 = lam / (32 * (H : ℝ)) * ((H : ℝ) / 4 / 4) := by field_simp; ring
          _ ≤ lam / (32 * (H : ℝ)) * ((T.card : ℝ) / 4) := by
              rw [hTcard]; exact mul_le_mul_of_nonneg_left (by linarith) hlpos.le
          _ ≤ _ := mul_le_mul_of_nonneg_left hx hlpos.le
      have : ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) := by linarith
      rw [if_pos this]
      linarith
    · push_neg at hbig
      have : 0 ≤ 3 * K / 4 *
          (if ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) then (1 : ℝ) else 0) :=
        mul_nonneg (by linarith) (by split_ifs <;> norm_num)
      linarith
  -- (d) conclude
  set F := ∑ θ, prior ref θ * evProb (P θ)
    (fun hist => ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist)) with hF
  have hEW2 : ∑ θ, prior ref θ * ∑ hist, (P θ).prob hist * W θ hist ≤ K / 4 + 3 * K / 4 * F := by
    calc ∑ θ, prior ref θ * ∑ hist, (P θ).prob hist * W θ hist
        ≤ ∑ θ, prior ref θ * ∑ hist, (P θ).prob hist * (K / 4 + 3 * K / 4 *
            (if ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) then 1 else 0)) :=
          Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun hist _ => mul_le_mul_of_nonneg_left (hpt θ hist)
              ((P θ).prob_nonneg hist)) (hρ0 θ)
      _ = K / 4 + 3 * K / 4 * F := by
          have : ∀ θ, ∑ hist, (P θ).prob hist * (K / 4 + 3 * K / 4 *
              (if ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist) then (1 : ℝ) else 0)) =
              K / 4 + 3 * K / 4 * evProb (P θ)
                (fun hist => ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out hist)) := by
            intro θ
            unfold evProb
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (P θ).sum_prob, one_mul,
              Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun hist _ => ?_
            ring
          simp_rw [this, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hρ1, one_mul, hF,
            Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun θ _ => ?_
          ring
  have hfin : 7 / 16 * K ≤ K / 4 + 3 * K / 4 * F := hEW.trans hEW2
  by_contra hlt
  push_neg at hlt
  have : 3 * K / 4 * F < 3 * K / 4 * (1 / 4) := mul_lt_mul_of_pos_left hlt (by linarith)
  linarith

end Bayes

end StatisticalRL.Ch7Rest.Marl
