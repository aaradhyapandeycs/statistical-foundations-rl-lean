import Formalization.Probability.FiniteMarkov.Mixing

/-! # Finite Markov chains: path sums and the Markov property

The Markov split (M4) of the plan for Theorem 4.12, in explicit finite-sum form on paths
`x : Fin (n+1) → X` with mass `pathMass ν K n x = ν(x₀) ∏ K(xᵢ,xᵢ₊₁)`:

* `pathExp_dep_snoc` (marginalisation of the last coordinate),
* `pathExp_markov_step` (one-step Markov property: given `x₀..x_k`, `x_{k+1} ∼ K(x_k,·)`),
* `pathExp_markov_iter` (`t`-step version with `K^t`),
* `pathExp_prod_block` (expectation of a product of single-site factors over a block, by
  backward recursion), and `pathExp_window_prod_le` (peeling consecutive blocks). -/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.FiniteMarkov

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Append a last coordinate to a path. -/
def snocPath {n : ℕ} (x : Fin (n + 1) → X) (y : X) : Fin (n + 2) → X :=
  Fin.snoc (α := fun _ ↦ X) x y

theorem sum_snocPath {n : ℕ} (F : (Fin (n + 2) → X) → ℝ) :
    ∑ x', F x' = ∑ x : Fin (n + 1) → X, ∑ y, F (snocPath x y) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ X)).sum_comp, Fintype.sum_prod_type, sum_comm]
  rfl

theorem pathAt_snocPath_of_le {n : ℕ} (x : Fin (n + 1) → X) (y : X) {i : ℕ} (hi : i ≤ n) :
    pathAt (snocPath x y) i = pathAt x i := by
  unfold pathAt snocPath
  have : (⟨min i (n + 1), by omega⟩ : Fin (n + 2)) = Fin.castSucc ⟨min i n, by omega⟩ := by
    ext; simp; omega
  rw [this, Fin.snoc_castSucc]

theorem pathAt_snocPath_of_gt {n : ℕ} (x : Fin (n + 1) → X) (y : X) {i : ℕ} (hi : n < i) :
    pathAt (snocPath x y) i = y := by
  unfold pathAt snocPath
  have : (⟨min i (n + 1), by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
    ext; simp; omega
  rw [this, Fin.snoc_last]

theorem pathAt_last {n : ℕ} (x : Fin (n + 1) → X) : pathAt x n = x (Fin.last n) := by
  unfold pathAt; congr 1; ext; simp

theorem pathMass_snocPath (ν : X → ℝ) (K : X → X → ℝ) {n : ℕ} (x : Fin (n + 1) → X) (y : X) :
    pathMass ν K (n + 1) (snocPath x y) = pathMass ν K n x * K (pathAt x n) y := by
  unfold pathMass
  rw [Fin.prod_univ_castSucc, pathAt_last]
  have h0 : snocPath x y 0 = x 0 := by
    unfold snocPath
    exact Fin.snoc_castSucc (α := fun _ ↦ X) (p := x) (x := y) (i := 0)
  have hl : snocPath x y (Fin.last n).succ = y := by
    unfold snocPath; rw [Fin.succ_last]; exact Fin.snoc_last (α := fun _ ↦ X) _ _
  have hc : ∀ i : Fin (n + 1), snocPath x y i.castSucc = x i := fun i ↦ by
    unfold snocPath; exact Fin.snoc_castSucc (α := fun _ ↦ X) _ _ _
  rw [h0, hl, hc]
  simp only [Fin.succ_castSucc, hc]
  ring

/-- Path expectation `∑_x pathMass(x) F(x)`. -/
noncomputable def pathExp (ν : X → ℝ) (K : X → X → ℝ) (n : ℕ) (F : (Fin (n + 1) → X) → ℝ) : ℝ :=
  ∑ x, pathMass ν K n x * F x

/-- `F` only depends on the coordinates `x₀,…,x_k`. -/
def DependsUpTo {n : ℕ} (k : ℕ) (F : (Fin (n + 1) → X) → ℝ) : Prop :=
  ∀ x x', (∀ i ≤ k, pathAt x i = pathAt x' i) → F x = F x'

theorem DependsUpTo.mono {n k k' : ℕ} {F : (Fin (n + 1) → X) → ℝ} (h : DependsUpTo k F)
    (hk : k ≤ k') : DependsUpTo k' F :=
  fun x x' hx ↦ h x x' fun i hi ↦ hx i (hi.trans hk)

theorem DependsUpTo.mul {n k : ℕ} {F G : (Fin (n + 1) → X) → ℝ} (hF : DependsUpTo k F)
    (hG : DependsUpTo k G) : DependsUpTo k (fun x ↦ F x * G x) :=
  fun x x' hx ↦ by show F x * G x = F x' * G x'; rw [hF x x' hx, hG x x' hx]

theorem dependsUpTo_const {n k : ℕ} (c : ℝ) : DependsUpTo (n := n) (X := X) k (fun _ ↦ c) :=
  fun _ _ _ ↦ rfl

theorem dependsUpTo_coord {n k : ℕ} (f : X → ℝ) {i : ℕ} (hi : i ≤ k) :
    DependsUpTo (n := n) k (fun x ↦ f (pathAt x i)) :=
  fun x x' hx ↦ by show f (pathAt x i) = f (pathAt x' i); rw [hx i hi]

theorem dependsUpTo_prod {n k : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin (n + 1) → X) → ℝ)
    (hF : ∀ j ∈ s, DependsUpTo k (F j)) : DependsUpTo k (fun x ↦ ∏ j ∈ s, F j x) :=
  fun x x' hx ↦ prod_congr rfl fun j hj ↦ hF j hj x x' hx

theorem DependsUpTo.snoc {n k : ℕ} {F : (Fin (n + 2) → X) → ℝ} (hF : DependsUpTo k F)
    (hk : k ≤ n) (y : (Fin (n + 1) → X) → X) :
    DependsUpTo k (fun x : Fin (n + 1) → X ↦ F (snocPath x (y x))) :=
  fun x x' hx ↦ hF _ _ fun i hi ↦ by
    rw [pathAt_snocPath_of_le _ _ (hi.trans hk), pathAt_snocPath_of_le _ _ (hi.trans hk), hx i hi]

theorem DependsUpTo.snoc_eq {n k : ℕ} {F : (Fin (n + 2) → X) → ℝ} (hF : DependsUpTo k F)
    (hk : k ≤ n) (x : Fin (n + 1) → X) (y y' : X) : F (snocPath x y) = F (snocPath x y') :=
  hF _ _ fun i hi ↦ by
    rw [pathAt_snocPath_of_le _ _ (hi.trans hk), pathAt_snocPath_of_le _ _ (hi.trans hk)]

variable {K : X → X → ℝ} {ν : X → ℝ}

/-- Marginalising the last coordinate. -/
theorem pathExp_dep_snoc (hK : IsStochastic K) {n : ℕ} (F : (Fin (n + 2) → X) → ℝ)
    (hF : ∀ x y y', F (snocPath x y) = F (snocPath x y')) :
    pathExp ν K (n + 1) F = pathExp ν K n (fun x ↦ F (snocPath x (x 0))) := by
  unfold pathExp
  rw [sum_snocPath]
  refine sum_congr rfl fun x _ ↦ ?_
  simp_rw [pathMass_snocPath, hF x _ (x 0), mul_assoc, ← mul_sum, ← sum_mul, hK.row_sum, one_mul]

theorem pathExp_add {n : ℕ} (F G : (Fin (n + 1) → X) → ℝ) :
    pathExp ν K n (fun x ↦ F x + G x) = pathExp ν K n F + pathExp ν K n G := by
  unfold pathExp; simp_rw [mul_add, sum_add_distrib]

theorem pathExp_smul {n : ℕ} (c : ℝ) (F : (Fin (n + 1) → X) → ℝ) :
    pathExp ν K n (fun x ↦ c * F x) = c * pathExp ν K n F := by
  unfold pathExp; rw [mul_sum]; exact sum_congr rfl fun x _ ↦ by ring

theorem pathExp_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin (n + 1) → X) → ℝ) :
    pathExp ν K n (fun x ↦ ∑ j ∈ s, F j x) = ∑ j ∈ s, pathExp ν K n (F j) := by
  unfold pathExp; simp_rw [mul_sum]; rw [sum_comm]

theorem pathMass_nonneg (hK : IsStochastic K) (hν : ∀ x, 0 ≤ ν x) {n : ℕ}
    (x : Fin (n + 1) → X) : 0 ≤ pathMass ν K n x :=
  mul_nonneg (hν _) (prod_nonneg fun i _ ↦ hK.nonneg _ _)

theorem pathExp_mono (hK : IsStochastic K) (hν : ∀ x, 0 ≤ ν x) {n : ℕ}
    {F G : (Fin (n + 1) → X) → ℝ} (h : ∀ x, F x ≤ G x) : pathExp ν K n F ≤ pathExp ν K n G :=
  sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (pathMass_nonneg hK hν x)

theorem pathExp_nonneg (hK : IsStochastic K) (hν : ∀ x, 0 ≤ ν x) {n : ℕ}
    {F : (Fin (n + 1) → X) → ℝ} (h : ∀ x, 0 ≤ F x) : 0 ≤ pathExp ν K n F :=
  sum_nonneg fun x _ ↦ mul_nonneg (pathMass_nonneg hK hν x) (h x)

/-- Expectation of a function of the initial coordinate. -/
theorem pathExp_initial (hK : IsStochastic K) (n : ℕ) (f : X → ℝ) :
    pathExp ν K n (fun x ↦ f (pathAt x 0)) = ∑ x, ν x * f x := by
  induction n with
  | zero =>
    unfold pathExp pathMass
    rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
    refine sum_congr rfl fun x _ ↦ ?_
    simp [pathAt]
  | succ n ih =>
    rw [pathExp_dep_snoc hK]
    · simp_rw [pathAt_snocPath_of_le _ _ (Nat.zero_le n)]; exact ih
    · intro x y y'
      simp_rw [pathAt_snocPath_of_le _ _ (Nat.zero_le n)]

theorem pathExp_one (hK : IsStochastic K) (hν : IsProb ν) (n : ℕ) :
    pathExp ν K n (fun _ ↦ 1) = 1 := by
  have := pathExp_initial (ν := ν) hK n (fun _ ↦ 1)
  simpa [hν.sum_eq] using this

/-- One-step Markov property. -/
theorem pathExp_markov_step (hK : IsStochastic K) {n : ℕ} {k : ℕ} (hk : k < n)
    (G : (Fin (n + 1) → X) → ℝ) (hG : DependsUpTo k G) (h : X → X → ℝ) :
    pathExp ν K n (fun x ↦ G x * h (pathAt x k) (pathAt x (k + 1))) =
      pathExp ν K n (fun x ↦ G x * ∑ y, K (pathAt x k) y * h (pathAt x k) y) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · have hdep : ∀ F : (Fin (n + 2) → X) → ℝ, DependsUpTo n F →
          ∀ x y y', F (snocPath x y) = F (snocPath x y') := fun F hF x y y' ↦ hF.snoc_eq le_rfl x y y'
      rw [pathExp_dep_snoc hK _ (hdep _ ((hG.mono (by omega)).mul
          (fun x x' hx ↦ by rw [hx k (by omega), hx (k + 1) (by omega)]))),
        pathExp_dep_snoc hK _ (hdep _ ((hG.mono (by omega)).mul
          (fun x x' hx ↦ by rw [hx k (by omega)])))]
      simp_rw [pathAt_snocPath_of_le _ _ (show k ≤ n by omega),
        pathAt_snocPath_of_le _ _ (show k + 1 ≤ n by omega)]
      exact ih (by omega) _ (hG.snoc (by omega) (fun x ↦ x 0))
    · have hkn : k = n := by omega
      subst hkn
      unfold pathExp
      rw [sum_snocPath, sum_snocPath]
      refine sum_congr rfl fun x _ ↦ ?_
      have e1 : ∀ y, pathMass ν K (k + 1) (snocPath x y) * (G (snocPath x y) *
          h (pathAt (snocPath x y) k) (pathAt (snocPath x y) (k + 1))) =
          (pathMass ν K k x * G (snocPath x (x 0))) * (K (pathAt x k) y * h (pathAt x k) y) := by
        intro y
        rw [pathMass_snocPath, pathAt_snocPath_of_le _ _ le_rfl,
          pathAt_snocPath_of_gt _ _ (Nat.lt_succ_self k), hG.snoc_eq le_rfl x y (x 0)]
        ring
      have e2 : ∀ y, pathMass ν K (k + 1) (snocPath x y) * (G (snocPath x y) *
          ∑ w, K (pathAt (snocPath x y) k) w * h (pathAt (snocPath x y) k) w) =
          (pathMass ν K k x * G (snocPath x (x 0)) *
            ∑ w, K (pathAt x k) w * h (pathAt x k) w) * K (pathAt x k) y := by
        intro y
        rw [pathMass_snocPath, pathAt_snocPath_of_le _ _ le_rfl, hG.snoc_eq le_rfl x y (x 0)]
        ring
      simp_rw [e1, e2, ← mul_sum, hK.row_sum, mul_one]

theorem sum_kpow_succ_mul (t : ℕ) (u : X) (f : X → ℝ) :
    ∑ y, kpow K (t + 1) u y * f y = ∑ w, K u w * ∑ y, kpow K t w y * f y := by
  simp_rw [kpow_succ_apply, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-- `t`-step Markov property. -/
theorem pathExp_markov_iter (hK : IsStochastic K) {n : ℕ} (t : ℕ) :
    ∀ (k : ℕ), k + t ≤ n → ∀ (G : (Fin (n + 1) → X) → ℝ), DependsUpTo k G → ∀ (f : X → ℝ),
    pathExp ν K n (fun x ↦ G x * f (pathAt x (k + t))) =
      pathExp ν K n (fun x ↦ G x * ∑ y, kpow K t (pathAt x k) y * f y) := by
  induction t with
  | zero =>
    intro k _ G _ f
    simp [kpow_zero_apply]
  | succ t ih =>
    intro k hkt G hG f
    rw [show k + (t + 1) = (k + 1) + t by omega, ih (k + 1) (by omega) G (hG.mono (by omega)) f]
    rw [pathExp_markov_step hK (by omega) G hG (fun _ v ↦ ∑ y, kpow K t v y * f y)]
    simp_rw [sum_kpow_succ_mul]

/-- Law of a single coordinate: `E f(X_j) = ∑_x ν(x) (K^j f)(x)`. -/
theorem pathExp_coord (hK : IsStochastic K) {n j : ℕ} (hj : j ≤ n) (f : X → ℝ) :
    pathExp ν K n (fun x ↦ f (pathAt x j)) = ∑ x, ν x * ∑ y, kpow K j x y * f y := by
  have h := pathExp_markov_iter (ν := ν) (n := n) hK j 0 (by omega) (fun _ ↦ 1) (dependsUpTo_const 1) f
  simp only [one_mul, zero_add] at h
  rw [h]
  exact pathExp_initial hK n (fun v ↦ ∑ y, kpow K j v y * f y)

/-! ## Products of single-site factors over blocks -/

/-- Backward recursion `v₀ = 1`, `v_{r+1}(y) = φ(y) ∑_w K(y,w) v_r(w)`, i.e.
`v_r(y) = E_y ∏_{i<r} φ(Y_i)`. -/
noncomputable def blockValue (K : X → X → ℝ) (φ : X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ ↦ 1
  | r + 1 => fun y ↦ φ y * ∑ w, K y w * blockValue K φ r w

theorem pathExp_prod_block (hK : IsStochastic K) {n : ℕ} (φ : X → ℝ) (r : ℕ) :
    ∀ (s : ℕ), s + r ≤ n + 1 → ∀ (G : (Fin (n + 1) → X) → ℝ), DependsUpTo s G →
    pathExp ν K n (fun x ↦ G x * ∏ i ∈ range r, φ (pathAt x (s + i))) =
      pathExp ν K n (fun x ↦ G x * blockValue K φ r (pathAt x s)) := by
  induction r with
  | zero => intro s _ G _; simp [blockValue]
  | succ r ih =>
    intro s hsr G hG
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [blockValue, hK.row_sum]
    have hstep : ∀ x : Fin (n + 1) → X, G x * ∏ i ∈ range (r + 1), φ (pathAt x (s + i)) =
        (G x * φ (pathAt x s)) * ∏ i ∈ range r, φ (pathAt x (s + 1 + i)) := fun x ↦ by
      rw [prod_range_succ', mul_comm (∏ i ∈ range r, _), ← mul_assoc]
      simp only [add_zero]
      congr 1
      refine prod_congr rfl fun i _ ↦ by rw [show s + (i + 1) = s + 1 + i by omega]
    simp_rw [hstep]
    rw [ih (s + 1) (by omega) _ ((hG.mono (Nat.le_succ s)).mul (dependsUpTo_coord φ (by omega)))]
    have := pathExp_markov_step (ν := ν) hK (k := s) (by omega) (fun x ↦ G x * φ (pathAt x s))
      (hG.mul (dependsUpTo_coord φ le_rfl)) (fun _ v ↦ blockValue K φ r v)
    simp only at this
    rw [this]
    unfold pathExp
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [blockValue]
    ring

/-- The block value integrated against an initial law is a path expectation of length `b`. -/
theorem blockValue_eq_pathExp (hK : IsStochastic K) (φ : X → ℝ) (b : ℕ) :
    ∑ x, ν x * blockValue K φ (b + 1) x =
      pathExp ν K b (fun x ↦ ∏ i ∈ range (b + 1), φ (pathAt x i)) := by
  have h := pathExp_prod_block (ν := ν) hK (n := b) φ (b + 1) 0 (by omega) (fun _ ↦ 1)
    (dependsUpTo_const 1)
  simp only [one_mul, zero_add] at h
  rw [h, pathExp_initial hK]

/-- Peeling consecutive blocks of length `b` starting at time `τ`: if every block, started from
any of the laws `ν` or `K(y,·)`, has expected product at most `ρ`, then the product over `J`
blocks has expectation at most `ρ^J`. -/
theorem pathExp_window_prod_le (hK : IsStochastic K) (hν : IsProb ν) {n : ℕ} {φ : X → ℝ}
    (hφ : ∀ y, 0 ≤ φ y) {b : ℕ} (hb : 1 ≤ b) (τ : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hblockK : ∀ y, ∑ w, K y w * blockValue K φ b w ≤ ρ)
    (hblockν : ∑ x, ν x * blockValue K φ b x ≤ ρ) (J : ℕ) (hJ : τ + J * b ≤ n + 1) :
    pathExp ν K n (fun x ↦ ∏ i ∈ range (J * b), φ (pathAt x (τ + i))) ≤ ρ ^ J := by
  induction J with
  | zero => simp [pathExp_one hK hν]
  | succ J ih =>
    have hJ' : τ + J * b ≤ n + 1 := le_trans (by nlinarith) hJ
    set s := τ + J * b with hs
    have hsplit : ∀ x : Fin (n + 1) → X, ∏ i ∈ range ((J + 1) * b), φ (pathAt x (τ + i)) =
        (∏ i ∈ range (J * b), φ (pathAt x (τ + i))) * ∏ i ∈ range b, φ (pathAt x (s + i)) :=
      fun x ↦ by
        rw [Nat.succ_mul, prod_range_add]
        congr 1
        exact prod_congr rfl fun i _ ↦ by rw [hs, add_assoc]
    simp_rw [hsplit]
    have hGnn : ∀ x : Fin (n + 1) → X, 0 ≤ ∏ i ∈ range (J * b), φ (pathAt x (τ + i)) :=
      fun x ↦ prod_nonneg fun i _ ↦ hφ _
    have hbs : s + b ≤ n + 1 := by rw [hs]; nlinarith
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · have hJ0 : J * b = 0 := by omega
      have hτ0 : τ = 0 := by omega
      simp_rw [hJ0, prod_range_zero, one_mul]
      have := pathExp_prod_block (ν := ν) hK (n := n) φ b s hbs (fun _ ↦ 1) (dependsUpTo_const 1)
      simp only [one_mul] at this
      rw [this, hs0, pathExp_initial hK]
      have hJz : J = 0 := by
        rcases Nat.eq_zero_or_pos J with h | h
        · exact h
        · nlinarith
      simp [hJz, hblockν]
    · have hdep : DependsUpTo (s - 1) (fun x : Fin (n + 1) → X ↦
          ∏ i ∈ range (J * b), φ (pathAt x (τ + i))) :=
        dependsUpTo_prod _ _ fun i hi ↦ dependsUpTo_coord φ (by
          have := mem_range.mp hi; omega)
      rw [pathExp_prod_block (ν := ν) hK φ b s hbs _ (hdep.mono (Nat.sub_le s 1))]
      have hstep := pathExp_markov_step (ν := ν) hK (k := s - 1) (by omega) _ hdep
        (fun _ v ↦ blockValue K φ b v)
      simp only [show s - 1 + 1 = s by omega] at hstep
      rw [hstep]
      calc pathExp ν K n (fun x ↦ (∏ i ∈ range (J * b), φ (pathAt x (τ + i))) *
            ∑ y, K (pathAt x (s - 1)) y * blockValue K φ b y)
          ≤ pathExp ν K n (fun x ↦ ρ * ∏ i ∈ range (J * b), φ (pathAt x (τ + i))) :=
            pathExp_mono hK hν.nonneg fun x ↦ by
              rw [mul_comm ρ]; exact mul_le_mul_of_nonneg_left (hblockK _) (hGnn x)
        _ ≤ ρ * ρ ^ J := by rw [pathExp_smul]; exact mul_le_mul_of_nonneg_left (ih hJ') hρ
        _ = ρ ^ (J + 1) := by ring

end StatisticalRL.FiniteMarkov
