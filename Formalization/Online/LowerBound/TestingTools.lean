import Formalization.Online.LowerBound.BanditDefinitions
import Formalization.Probability.AdaptiveKL
import Formalization.Probability.Fano.ReverseTest
import Formalization.Generative.GenerativeLowerBoundBernoulli

/-!
# Testing tools for the online lower bound

Reusable finite-law facts for `lem:online-lb-testing` (`chapters/onlineRL.tex:2709–2721`) and
`thm:minimax-lower-online` (`:2443–2456`).

* `compLaw_finiteKLExpression`: appending a common kernel does not change the KL expression.
* `interactionLaw_finiteKLExpression`: the real-valued adaptive chain rule (from
  `AdaptiveKL.seqLaw_finiteKLExpression`).
* `finite_reverseFano`: `lem:reverse-Fano-bound` (`PrelimFano.reverseFano_test_error_lower`) for
  finite laws, with KL divergences and error probabilities written as finite sums.
* `fano_third`: `1 − 1/A − √((A−1)B/(2A²)) ≥ 1/3` when `A ≥ 3` and `B ≤ 2A/9`
  (`:5090–5095`).
* `onlineLBq_bernoulliKL_le`: every pair of exit probabilities of `eqn:prob-astar-a-1` at a common
  arm has Bernoulli KL at most `4ε²/H³` (`:5030–5048`, via `lem:KL-quadratic-lower-bound`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL AdaptiveKL GenerativeLowerBound

section KL

theorem compLaw_ac {W Z : Type*} [Fintype W] [Fintype Z] (P Q : FiniteDistribution W)
    (κ : W → FiniteDistribution Z) (hac : ∀ w, Q.prob w = 0 → P.prob w = 0) (x : W × Z) :
    (compLaw Q κ).prob x = 0 → (compLaw P κ).prob x = 0 := by
  intro hx
  change Q.prob x.1 * (κ x.1).prob x.2 = 0 at hx
  change P.prob x.1 * (κ x.1).prob x.2 = 0
  rcases mul_eq_zero.mp hx with h | h
  · rw [hac _ h, zero_mul]
  · rw [h, mul_zero]

/-- Appending a common kernel leaves the KL expression unchanged. -/
theorem compLaw_finiteKLExpression {W Z : Type*} [Fintype W] [Fintype Z]
    (P Q : FiniteDistribution W) (κ : W → FiniteDistribution Z)
    (hac : ∀ w, Q.prob w = 0 → P.prob w = 0) :
    finiteKLExpression (compLaw P κ).prob (compLaw Q κ).prob =
      finiteKLExpression P.prob Q.prob := by
  have h := finiteKLExpression_comp P.prob Q.prob (fun w z => (κ w).prob z)
    (fun w z => (κ w).prob z) (fun w _ => (κ w).sum_prob) hac (fun _ _ _ hz => hz)
  simp_rw [finiteKLExpression_self, mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [← h]
  exact Fintype.sum_prod_type _

variable {A O : Type*} [Fintype A] [Fintype O]

theorem interactionLaw_ac' (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ) :
    ∀ h, (interactionLaw π e' T).prob h = 0 → (interactionLaw π e T).prob h = 0 :=
  seqLaw_ac _ _ (fun t h _ z => interactionKernel_ac π e e' hac t h z) T

/-- Real-valued adaptive chain rule: `KL(P_T ‖ Q_T) = ∑_{t<T} E_{P_t}[∑_a π_t(a) KL(e_t(a) ‖ e'_t(a))]`
for the finite KL expressions. -/
theorem interactionLaw_finiteKLExpression (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ) :
    finiteKLExpression (interactionLaw π e T).prob (interactionLaw π e' T).prob =
      ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
        ∑ a, (π t h).prob a * finiteKLExpression (e t h a).prob (e' t h a).prob := by
  unfold interactionLaw
  rw [seqLaw_finiteKLExpression _ _ (fun t h _ z => interactionKernel_ac π e e' hac t h z) T]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun h _ => ?_
  rw [interactionKernel_finiteKLExpression π e e' hac t h]

/-- Bounding a family of chain-rule sums: if for every `(t, h, a)` the alternatives' per-step KL
expressions sum to at most `δ`, then the alternatives' history KL expressions sum to at most `T δ`. -/
theorem interactionLaw_sum_finiteKLExpression_le {J : Type*} [Fintype J]
    (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (e' : J → (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ j t h a o, (e' j t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ) (δ : ℝ)
    (hδ : ∀ t h a, ∑ j, finiteKLExpression (e t h a).prob (e' j t h a).prob ≤ δ) :
    ∑ j, finiteKLExpression (interactionLaw π e T).prob (interactionLaw π (e' j) T).prob ≤
      T * δ := by
  have hrw := fun j => interactionLaw_finiteKLExpression π e (e' j) (hac j) T
  simp_rw [hrw]
  rw [Finset.sum_comm]
  calc ∑ t ∈ Finset.range T, ∑ j, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a * finiteKLExpression (e t h a).prob (e' j t h a).prob
      = ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a * ∑ j, finiteKLExpression (e t h a).prob (e' j t h a).prob := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a * δ := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun h _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ ((interactionLaw π e t).prob_nonneg h)
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hδ t h a) ((π t h).prob_nonneg a)
    _ = T * δ := by
        have h1 : ∀ t (h : Fin t → A × O), ∑ a, (π t h).prob a * δ = δ := fun t h => by
          rw [← Finset.sum_mul, (π t h).sum_prob, one_mul]
        have h2 : ∀ t, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h * δ = δ := fun t => by
          rw [← Finset.sum_mul, (interactionLaw π e t).sum_prob, one_mul]
        simp_rw [h1, h2]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end KL

section Fano

/-- **Reverse Fano for finite laws** (`lem:reverse-Fano-bound`, `chapters/prelim.tex:1209–1229`, via
`PrelimFano.reverseFano_test_error_lower`): for laws `d 0, …, d M` on a finite set with
atomwise absolute continuity `d 0 ≪ d (j+1)` and KL budget
`∑_{j} KL(d 0 ‖ d (j+1)) ≤ B`, every test `ψ` has average error at least
`1 − 1/(M+1) − √(M B / (2 (M+1)²))`. -/
theorem finite_reverseFano {Ω : Type*} [Fintype Ω] (M : ℕ) (d : Fin (M + 1) → FiniteDistribution Ω)
    (ψ : Ω → Fin (M + 1)) (hac : ∀ (j : Fin M) x, (d j.succ).prob x = 0 → (d 0).prob x = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hKL : ∑ j : Fin M, finiteKLExpression (d 0).prob (d j.succ).prob ≤ B) :
    1 - 1 / ((M : ℝ) + 1) - Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) ≤
      (1 / ((M : ℝ) + 1)) *
        ∑ j : Fin (M + 1), ∑ x, (d j).prob x * (if ψ x ≠ j then 1 else 0) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  haveI : MeasurableSingletonClass Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmeas : Measurable ψ := measurable_from_top
  have hKL' : (∑ j : Fin M, InformationTheory.klDiv (d 0).toPMF.toMeasure
      (d j.succ).toPMF.toMeasure) ≤ ENNReal.ofReal B := by
    have hterm : ∀ j : Fin M, InformationTheory.klDiv (d 0).toPMF.toMeasure
        (d j.succ).toPMF.toMeasure = ENNReal.ofReal (finiteKLExpression (d 0).prob (d j.succ).prob) := by
      intro j
      obtain ⟨hne, heq⟩ := toMeasure_klDiv (d 0) (d j.succ) (hac j)
      rw [← heq, ENNReal.ofReal_toReal hne]
    have hnn : ∀ j : Fin M, 0 ≤ finiteKLExpression (d 0).prob (d j.succ).prob := by
      intro j
      rw [← (toMeasure_klDiv (d 0) (d j.succ) (hac j)).2]
      exact ENNReal.toReal_nonneg
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j)]
    exact ENNReal.ofReal_le_ofReal hKL
  have h := PrelimFano.reverseFano_test_error_lower M (fun j => (d j).toPMF.toMeasure) ψ hmeas
    B hB hKL'
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hset : {ω | ψ ω ≠ j} = ((Finset.univ.filter fun ω => ψ ω ≠ j : Finset Ω) : Set Ω) := by
    ext ω; simp
  rw [hset, ← sum_measureReal_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [toMeasure_real_singleton]
  split_ifs <;> simp

/-- The scalar step of `chapters/onlineRL.tex:5090–5095`: for `A = M + 1 ≥ 3` and `0 ≤ B ≤ 2A/9`,
`1 − 1/A − √((A − 1) B / (2A²)) ≥ 1/3`. -/
theorem fano_third (M : ℕ) (hM : 2 ≤ M) (B : ℝ)
    (hBle : B ≤ 2 * ((M : ℝ) + 1) / 9) :
    (1 : ℝ) / 3 ≤ 1 - 1 / ((M : ℝ) + 1) - Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hfrac : (M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2) ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (M : ℝ) * B ≤ (M : ℝ) * (2 * ((M : ℝ) + 1) / 9) :=
      mul_le_mul_of_nonneg_left hBle (by linarith)
    nlinarith
  have hsqrt : Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) ≤ 1 / 3 := by
    calc Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) ≤ Real.sqrt (1 / 9) :=
          Real.sqrt_le_sqrt hfrac
      _ = 1 / 3 := by
          rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hinv : 1 / ((M : ℝ) + 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]; linarith
  linarith

end Fano

section Bernoulli

/-- Every exit probability of `eqn:prob-astar-a-1` is at least `1/H − ε/H²`. -/
theorem onlineLBq_ge {H : ℕ} {ε : ℝ} (hH : 1 ≤ H) (hε : 0 ≤ ε) {A : ℕ} (astar a : Fin A) :
    1 / (H : ℝ) - ε / (H : ℝ) ^ 2 ≤ onlineLBq H ε astar a := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have h3 : ε / (2 * (H : ℝ) ^ 2) ≤ ε / (H : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hε (by positivity) (by nlinarith)
  have h4 : 0 ≤ ε / (2 * (H : ℝ) ^ 2) := by positivity
  unfold onlineLBq
  split_ifs <;> linarith

/-- `KL(Bern(q_s(a)) ‖ Bern(q_{s'}(a))) ≤ 4ε²/H³` for any two instances `s, s'` and any arm `a`
(`chapters/onlineRL.tex:5030–5048`, using `lem:KL-quadratic-lower-bound`). -/
theorem onlineLBq_bernoulliKL_le {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (s s' a : Fin A) :
    bernoulliKLExpression (onlineLBq H ε s a) (onlineLBq H ε s' a) ≤ 4 * ε ^ 2 / (H : ℝ) ^ 3 := by
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  obtain ⟨hq1, hq2⟩ := onlineLBq_bounds hH hε hεH s a
  obtain ⟨hp1, hp2⟩ := onlineLBq_bounds hH hε hεH s' a
  have hq3 := onlineLBq_ge (H := H) (by omega) hε.le s a
  have hp3 := onlineLBq_ge (H := H) (by omega) hε.le s' a
  set q := onlineLBq H ε s a
  set p := onlineLBq H ε s' a
  have hhalf : 1 / (H : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hHpos (by norm_num)]; linarith
  have h2H : 0 < 1 / (2 * (H : ℝ)) := by positivity
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hq1' : q < 1 := by linarith
  have hp1' : p < 1 := by linarith
  refine (bernoulliKLExpression_le_quadratic q p hp0 hp1' hq0 hq1').trans ?_
  have hnum : (q - p) ^ 2 ≤ (ε / (H : ℝ) ^ 2) ^ 2 := by
    apply sq_le_sq' <;> linarith
  have hden : 1 / (4 * (H : ℝ)) ≤ p * (1 - p) := by
    have h1 : 1 / (4 * (H : ℝ)) = 1 / (2 * (H : ℝ)) * (1 / 2) := by field_simp; ring
    rw [h1]
    exact mul_le_mul hp1 (by linarith) (by norm_num) hp0.le
  calc (q - p) ^ 2 / (p * (1 - p)) ≤ (ε / (H : ℝ) ^ 2) ^ 2 / (1 / (4 * (H : ℝ))) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * ε ^ 2 / (H : ℝ) ^ 3 := by field_simp

/-- The bandit reward rows' KL expression is the Bernoulli KL of the exit probabilities. -/
theorem banditRewardRow_finiteKLExpression {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (s s' a : Fin A) :
    finiteKLExpression (banditRewardRow H ε hH hε hεH s a).prob
        (banditRewardRow H ε hH hε hεH s' a).prob =
      bernoulliKLExpression (onlineLBq H ε s a) (onlineLBq H ε s' a) := by
  unfold finiteKLExpression bernoulliKLExpression
  rw [Fintype.sum_bool]
  simp only [banditRewardRow, if_true, Bool.false_eq_true, if_false]
  ring

theorem banditRewardRow_pos {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (s a : Fin A) (r : Bool) :
    0 < (banditRewardRow H ε hH hε hεH s a).prob r := by
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  obtain ⟨h1, h2⟩ := onlineLBq_bounds hH hε hεH s a
  have hhalf : 1 / (H : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hHpos (by norm_num)]; linarith
  have h2H : 0 < 1 / (2 * (H : ℝ)) := by positivity
  cases r <;> simp only [banditRewardRow, if_true, Bool.false_eq_true, if_false] <;> linarith

/-- The exit probabilities of the instances `1` (index `0`) and `j + 1` agree at every arm other
than `j + 1` (`eqn:prob-astar-a-1`). -/
theorem onlineLBq_zero_eq_succ (H : ℕ) (ε : ℝ) {M : ℕ} (j : Fin M) (a : Fin (M + 1))
    (hj : j.succ ≠ a) : onlineLBq H ε (0 : Fin (M + 1)) a = onlineLBq H ε j.succ a := by
  unfold onlineLBq
  have h1 : ((j.succ : Fin (M + 1)) : ℕ) ≠ 0 := by simp
  have h2 : a ≠ j.succ := Ne.symm hj
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, if_false, h1, not_false_eq_true,
    if_true, h2]
  by_cases ha : a = 0
  · subst ha; simp
  · have : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
    simp [ha, this]

/-- A sum over the alternatives `j + 1` whose terms vanish unless `j + 1 = a` is at most `δ`. -/
theorem sum_succ_le_of_single {M : ℕ} (a : Fin (M + 1)) (f : Fin M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hzero : ∀ j, j.succ ≠ a → f j = 0) (hle : ∀ j, j.succ = a → f j ≤ δ) : ∑ j, f j ≤ δ := by
  by_cases ha : a = 0
  · rw [Finset.sum_eq_zero fun j _ => hzero j (by rw [ha]; exact Fin.succ_ne_zero j)]
    exact hδ
  · obtain ⟨j₀, hj₀⟩ := Fin.exists_succ_eq_of_ne_zero ha
    rw [Finset.sum_eq_single j₀ (fun j _ hj => hzero j (fun h => hj (Fin.succ_injective _
      (h.trans hj₀.symm)))) (by simp)]
    exact hle j₀ hj₀

/-- The KL expression of two exit rows with the same pair of states is the Bernoulli KL of the exit
probabilities. -/
theorem exitRow_finiteKLExpression {State : Type*} [Fintype State] [DecidableEq State]
    (g b : State) (hgb : g ≠ b) (q q' : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (h0' : 0 ≤ q')
    (h1' : q' ≤ 1) :
    finiteKLExpression (exitRow g b hgb q h0 h1).prob (exitRow g b hgb q' h0' h1').prob =
      bernoulliKLExpression q q' := by
  unfold finiteKLExpression bernoulliKLExpression
  rw [← Finset.sum_subset (Finset.subset_univ ({b, g} : Finset State)) (fun z _ hz => ?_),
    Finset.sum_pair (Ne.symm hgb)]
  · simp [exitRow, hgb]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp [exitRow, hz.1, hz.2]

end Bernoulli

end StatisticalRL.OnlineLowerBound
