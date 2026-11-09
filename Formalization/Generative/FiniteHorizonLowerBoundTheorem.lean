import Formalization.Generative.FiniteHorizonLowerBoundBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-horizon generative minimax lower bound

The matching lower bound behind the prose claim `generative_model_model_based.tex:2585` that the
sample size `SAH⁴/ε²` of Theorem 3.9 is minimax optimal, in the book's per-tuple protocol
(`:23–30`, `:2533–2540`), for randomized estimators with a seed independent of the data.

Proof: weighted Assouad (averaged over the hidden bits) on the hard family `hardStages`, with
Le Cam's inequality and the Bhattacharyya coefficient for each bit flip, a reverse-Markov step for
each seed value, and integration over the seed.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace StatisticalRL.FiniteHorizonLowerBound

open StatisticalRL OnlineLowerBound FiniteHorizonGenerative Assouad

section Measurability

/-- Preimages under a map into a finite function space with measurable coordinate level sets are
measurable. -/
theorem measurableSet_preimage_coords {Seed ι κ : Type*} [MeasurableSpace Seed] [Finite ι]
    [Finite κ] (R : Seed → ι → κ) (hR : ∀ i k, MeasurableSet {ω | R ω i = k})
    (T : Set (ι → κ)) : MeasurableSet (R ⁻¹' T) := by
  have : R ⁻¹' T = ⋃ g : T, ⋂ i, {ω | R ω i = (g : ι → κ) i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq,
      Subtype.exists, exists_prop]
    constructor
    · intro h; exact ⟨R ω, h, fun _ ↦ rfl⟩
    · rintro ⟨g, hg, hRg⟩
      rwa [show R ω = g from funext hRg]
  rw [this]
  exact MeasurableSet.iUnion fun g ↦ MeasurableSet.iInter fun i ↦ hR i _

/-- An event about a deterministic `H`-step policy that only reads its first `H` steps is
measurable in the seed when every output action is. -/
theorem measurableSet_policy_event {S A H : ℕ} (a0 : Fin A) {Seed : Type*} [MeasurableSpace Seed]
    (F : Seed → ℕ → Fin S → Fin A) (hF : ∀ h s a, MeasurableSet {ω | F ω h s = a})
    (G : (ℕ → Fin S → Fin A) → Prop)
    (hG : ∀ f f' : ℕ → Fin S → Fin A, (∀ n < H, f n = f' n) → (G f ↔ G f')) :
    MeasurableSet {ω | G (F ω)} := by
  let ext : (Fin H × Fin S → Fin A) → ℕ → Fin S → Fin A :=
    fun g n s ↦ if hn : n < H then g (⟨n, hn⟩, s) else a0
  let R : Seed → Fin H × Fin S → Fin A := fun ω hs ↦ F ω hs.1 hs.2
  have hset : {ω | G (F ω)} = R ⁻¹' {g | G (ext g)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine hG _ _ fun n hn ↦ ?_
    funext s
    simp [ext, R, hn]
  rw [hset]
  exact measurableSet_preimage_coords R (fun i k ↦ hF i.1 i.2 k) _

end Measurability

section Arithmetic

/-- The probability constant: `(θ/2 − t)/(1 − t) ≥ 1/8` with `θ = (1 − K)²/2`, `K ≤ 1/64`,
`t = 1/10`. Stated in the cleared form used below. -/
theorem constant_check (K : ℝ) (hK0 : 0 ≤ K) (hK : K ≤ 1 / 64) :
    (1 / 10 : ℝ) + (1 - 1 / 10) * (1 / 8) ≤ (1 - K) ^ 2 / 2 / 2 := by
  nlinarith

end Arithmetic

/-- **Finite-horizon generative minimax lower bound** (library form). For `S, A, H ≥ 2`,
`0 < ε ≤ H/4096` and per-tuple sample count `N ≤ 2⁻²⁸ H³/ε²`, every randomized estimator (a seed
of law `ν` independent of the data and a map `piHat` of the seed, the reward tables and the data
whose output actions have measurable level sets in the seed) fails, on some instance of the hard
family, to be `ε`-optimal at stage `1` with joint probability at least `1/8`. -/
theorem minimaxLowerBound (S A H N : ℕ) (ε : ℝ) (hS : 2 ≤ S) (hA : 2 ≤ A) (hH : 2 ≤ H)
    (hε : 0 < ε) (hεH : ε ≤ 1 / 4096 * H) (hN : (N : ℝ) ≤ 1 / 2 ^ 28 * (H : ℝ) ^ 3 / ε ^ 2)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (piHat : Seed → (Fin H → Fin S → Fin A → ℝ) → Samples (Fin S) (Fin A) H N →
      ℕ → Fin S → Fin A)
    (hmeas : ∀ r data h s a, MeasurableSet {ω | piHat ω r data h s = a}) :
    ∃ E : Fin H → EnvironmentStage (Fin S) (Fin A),
      (1 : ℝ) / 8 ≤ ((samplingLaw E N).prod ν).real
        {p | ∃ s, ε < EnvironmentStage.optimalValue (List.ofFn E) s -
          policyTrajectorySuffix (List.ofFn E) (piHat p.2 (fun h s a ↦ (E h).reward s a) p.1) 0 s} := by
  classical
  -- Parameters.
  set ε₀ : ℝ := 2048 * ε with hε₀def
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀H : ε₀ ≤ (H : ℝ) / 2 := by rw [hε₀def]; linarith
  let E : (Fin H → Bool) → Fin H → EnvironmentStage (Fin S) (Fin A) :=
    hardStages hS hA hH ε₀ hε₀ hε₀H
  let r₀ : Fin H → Fin S → Fin A → ℝ := fun h s a ↦ (E (fun _ ↦ false) h).reward s a
  have hr : ∀ σ, (fun h s a ↦ (E σ h).reward s a) = r₀ := fun σ ↦ rfl
  let g0 : Fin S := ⟨0, by omega⟩
  -- Information constant.
  set K : ℝ := (N : ℝ) * ε₀ ^ 2 / (H : ℝ) ^ 3 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : K ≤ 1 / 64 := by
    have hNε : (N : ℝ) * ε ^ 2 ≤ 1 / 2 ^ 28 * (H : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hN (sq_nonneg ε)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    rw [hKdef, div_le_iff₀ (by positivity), hε₀def]
    nlinarith
  set θ : ℝ := (1 - K) ^ 2 / 2 with hθdef
  set W : ℝ := ∑ h, weight H ε₀ h with hWdef
  have hW : ε₀ / 64 ≤ W := sum_weight_ge hH hε₀
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hW
  set t : ℝ := 1 / 10 with htdef
  -- Atoms.
  let p : (Fin H → Bool) → Samples (Fin S) (Fin A) H N → ℝ := fun σ x ↦ samplingAtom (E σ) N x
  have hp0 : ∀ σ x, 0 ≤ p σ x := fun σ x ↦ samplingAtom_nonneg _ _ _
  have hp1 : ∀ σ, ∑ x, p σ x = 1 := fun σ ↦ sum_samplingAtom _ _
  -- Per-seed bound on the hypercube sum of the probabilities of the large-loss events.
  let d : Seed → Samples (Fin S) (Fin A) H N → Fin H → Bool :=
    fun ω x h ↦ decodeBit hA (piHat ω r₀ x) (by omega) h
  let Z : Seed → (Fin H → Bool) → Samples (Fin S) (Fin A) H N → ℝ :=
    fun ω σ x ↦ ∑ h, weight H ε₀ h * (if d ω x h ≠ σ h then 1 else 0)
  let Q : Seed → (Fin H → Bool) → ℝ :=
    fun ω σ ↦ ∑ x, p σ x * (if t * W ≤ Z ω σ x then 1 else 0)
  have hQ : ∀ ω, (2 : ℝ) ^ H / 8 ≤ ∑ σ, Q ω σ := by
    intro ω
    have htest : ∀ j σ, σ j = false →
        θ ≤ (∑ x, p σ x * (if d ω x j = true then 1 else 0)) +
          ∑ x, p (flipAt j σ) x * (if d ω x j = false then 1 else 0) := by
      intro j σ _
      have hle := bhattacharyya_sq_le_test_error (p σ) (p (flipAt j σ)) (hp0 σ) (hp0 _)
        (hp1 σ) (hp1 _) (fun x ↦ d ω x j)
      have hbc := bhattacharyya_flip_ge hS hA hH hε₀ hε₀H N σ j
      have h1K : 0 ≤ 1 - K := by linarith
      have hsq : (1 - K) ^ 2 ≤ (∑ x, Real.sqrt (p σ x * p (flipAt j σ) x)) ^ 2 :=
        pow_le_pow_left₀ h1K hbc 2
      have : θ ≤ (∑ x, Real.sqrt (p σ x * p (flipAt j σ) x)) ^ 2 / 2 := by
        rw [hθdef]; linarith
      exact le_trans this hle
    have hass := assouad_weighted_sum p (weight H ε₀) (fun h ↦ weight_nonneg hε₀ h) (d ω) θ htest
    have hrm : ∀ σ, ∑ x, p σ x * Z ω σ x ≤ t * W + (1 - t) * W * Q ω σ := by
      intro σ
      refine reverse_markov_sum (p σ) (hp0 σ) (hp1 σ) (Z ω σ) W t (fun x ↦ ?_)
      refine Finset.sum_le_sum fun h _ ↦ ?_
      have := weight_nonneg hε₀ h
      split_ifs <;> nlinarith
    have hsumrm : ∑ σ, ∑ x, p σ x * Z ω σ x ≤
        (2 : ℝ) ^ H * (t * W) + (1 - t) * W * ∑ σ, Q ω σ := by
      calc _ ≤ ∑ σ : Fin H → Bool, (t * W + (1 - t) * W * Q ω σ) :=
            Finset.sum_le_sum fun σ _ ↦ hrm σ
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
              Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
            push_cast; ring
    have hcc := constant_check K hK0 hK
    rw [← hθdef] at hcc
    have h2H : (0 : ℝ) < 2 ^ H := by positivity
    have hkey : (1 - t) * W * ((2 : ℝ) ^ H / 8) ≤ (1 - t) * W * ∑ σ, Q ω σ := by
      have hA' : (2 : ℝ) ^ H * (θ / 2) * W ≤ ∑ σ, ∑ x, p σ x * Z ω σ x := hass
      have hm : (2 : ℝ) ^ H * W * (t + (1 - t) * (1 / 8)) ≤ (2 : ℝ) ^ H * W * (θ / 2) :=
        mul_le_mul_of_nonneg_left (by rw [htdef]; linarith) (by positivity)
      calc (1 - t) * W * ((2 : ℝ) ^ H / 8)
          = (2 : ℝ) ^ H * W * (t + (1 - t) * (1 / 8)) - (2 : ℝ) ^ H * (t * W) := by ring
        _ ≤ (2 : ℝ) ^ H * W * (θ / 2) - (2 : ℝ) ^ H * (t * W) := by linarith
        _ = (2 : ℝ) ^ H * (θ / 2) * W - (2 : ℝ) ^ H * (t * W) := by ring
        _ ≤ (∑ σ, ∑ x, p σ x * Z ω σ x) - (2 : ℝ) ^ H * (t * W) := by linarith
        _ ≤ (1 - t) * W * ∑ σ, Q ω σ := by linarith
    exact le_of_mul_le_mul_left hkey (by rw [htdef]; positivity)
  -- Large loss forces failure of ε-optimality.
  let P : (Fin H → Bool) → Samples (Fin S) (Fin A) H N → Seed → Prop :=
    fun σ x ω ↦ ∃ s, ε < EnvironmentStage.optimalValue (List.ofFn (E σ)) s -
      policyTrajectorySuffix (List.ofFn (E σ)) (piHat ω (fun h s a ↦ (E σ h).reward s a) x) 0 s
  have hincl : ∀ ω σ x, t * W ≤ Z ω σ x → P σ x ω := by
    intro ω σ x hZ
    refine ⟨g0, ?_⟩
    have hgap := gap_ge_weighted_loss hS hA hH hε₀ hε₀H σ (piHat ω r₀ x)
    rw [hr σ]
    have : ε < t * W := by rw [htdef]; linarith
    exact lt_of_lt_of_le this (le_trans hZ hgap)
  have hPm : ∀ σ x, MeasurableSet {ω | P σ x ω} := by
    intro σ x
    refine measurableSet_policy_event (H := H) ⟨0, by omega⟩ (fun ω ↦ piHat ω (fun h s a ↦
      (E σ h).reward s a) x) (fun h s a ↦ hmeas _ x h s a) (fun f ↦ ∃ s, ε <
        EnvironmentStage.optimalValue (List.ofFn (E σ)) s -
          policyTrajectorySuffix (List.ofFn (E σ)) f 0 s) ?_
    intro f f' hff'
    dsimp only
    rw [policyTrajectorySuffix_congr (List.ofFn (E σ)) f f'
      (fun n hn ↦ hff' n (by simpa using hn))]
  -- Integrate over the seed.
  have hjoint : ∀ σ, ((samplingLaw (E σ) N).prod ν).real {q | P σ q.1 q.2} =
      ∫ ω, ∑ x, p σ x * ({ω | P σ x ω}.indicator 1 ω) ∂ν := by
    intro σ
    rw [samplingLaw_prod_real (E σ) ν (P σ) (hPm σ), integral_finset_sum]
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [integral_const_mul, integral_indicator_one (hPm σ x)]
    · intro x _
      exact ((integrable_const (1 : ℝ)).indicator (hPm σ x)).const_mul _
  have hint : ∀ σ, Integrable (fun ω ↦ ∑ x, p σ x * ({ω | P σ x ω}.indicator 1 ω)) ν :=
    fun σ ↦ integrable_finset_sum _ fun x _ ↦
      ((integrable_const (1 : ℝ)).indicator (hPm σ x)).const_mul _
  have htotal : (2 : ℝ) ^ H / 8 ≤ ∑ σ, ((samplingLaw (E σ) N).prod ν).real {q | P σ q.1 q.2} := by
    simp_rw [hjoint]
    rw [← integral_finset_sum _ fun σ _ ↦ hint σ]
    have hmono : ∀ ω, (2 : ℝ) ^ H / 8 ≤
        ∑ σ, ∑ x, p σ x * ({ω | P σ x ω}.indicator 1 ω) := by
      intro ω
      refine le_trans (hQ ω) (Finset.sum_le_sum fun σ _ ↦ Finset.sum_le_sum fun x _ ↦ ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hp0 σ x)
      split_ifs with h
      · rw [Set.indicator_of_mem (show ω ∈ {ω | P σ x ω} from hincl ω σ x h)]; rfl
      · exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    calc (2 : ℝ) ^ H / 8 = ∫ _ω, (2 : ℝ) ^ H / 8 ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_finset_sum _ fun σ _ ↦ hint σ) hmono
  -- Some hidden-bit vector carries probability at least `1/8`.
  by_contra hne
  push_neg at hne
  have hlt : ∑ σ, ((samplingLaw (E σ) N).prod ν).real {q | P σ q.1 q.2} <
      ∑ _σ : Fin H → Bool, (1 : ℝ) / 8 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ ↦ hne (E σ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hlt
  push_cast at hlt
  linarith

end StatisticalRL.FiniteHorizonLowerBound
