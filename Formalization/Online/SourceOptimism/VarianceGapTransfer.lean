import Formalization.Generative.PolicyLearningVarianceTransfer

/-! Deterministic variance/mean-gap transfer for
online UCBVI. No adaptive concentration or zero-count algorithm is supplied. -/
namespace StatisticalRL.OnlineRL
variable {State : Type*} [Fintype State]

/-- An optimistic bounded continuation has gap variance controlled by its
actual probability-row mean gap. This is stronger than a uniform sup-gap
bound for later regret/optimism accounting and requires no independence. -/
theorem onlineOptimisticGap_variance_le_mean
    (d : FiniteDistribution State) (V U : State → ℝ) (H : ℝ)
    (hV : ∀ s, 0 ≤ V s) (hVU : ∀ s, V s ≤ U s)
    (hU : ∀ s, U s ≤ H) :
    d.variance (fun s => V s-U s) ≤
      H*d.expectation (fun s => U s-V s) := by
  have hsq (s : State) : (V s-U s)^2 ≤ H*(U s-V s) := by
    have hn : 0 ≤ U s-V s := sub_nonneg.mpr (hVU s)
    have hh : U s-V s ≤ H := by linarith [hV s, hU s]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]
  exact (d.variance_le_expectation_sq _).trans (by
    have h := d.expectation_mono hsq
    simpa only [FiniteDistribution.expectation_mul] using h)

/-- Standard deviation transfer with the row mean gap rather than a supremum
norm. It applies pointwise to a data-dependent empirical probability row. -/
theorem onlineOptimisticGap_sqrt_variance_transfer
    (d : FiniteDistribution State) (V U : State → ℝ) (H : ℝ)
    (hV : ∀ s, 0 ≤ V s) (hVU : ∀ s, V s ≤ U s)
    (hU : ∀ s, U s ≤ H) :
    Real.sqrt (d.variance V) ≤ Real.sqrt (d.variance U) +
      Real.sqrt (H*d.expectation (fun s => U s-V s)) := by
  have ht := d.sqrt_variance_add_le U (fun s => V s-U s)
  have heq : (fun s => U s+(V s-U s)) = V := by funext s; ring
  rw [heq] at ht
  exact ht.trans (add_le_add le_rfl (Real.sqrt_le_sqrt
    (onlineOptimisticGap_variance_le_mean d V U H hV hVU hU)))

/-- Young absorption of the standard-deviation transfer into the optimistic
row mean. The residual penalty is exactly a²H/4. -/
theorem onlineOptimisticGap_radius_absorb
    (d : FiniteDistribution State) (V U : State → ℝ) (H a : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a)
    (hV : ∀ s, 0 ≤ V s) (hVU : ∀ s, V s ≤ U s)
    (hU : ∀ s, U s ≤ H) :
    a*Real.sqrt (d.variance V) ≤
      d.expectation (fun s => U s-V s) +
        a*Real.sqrt (d.variance U) + a^2*H/4 := by
  let m := d.expectation (fun s => U s-V s)
  have hm : 0 ≤ m := d.expectation_nonneg (fun s => sub_nonneg.mpr (hVU s))
  have hx : (Real.sqrt (H*m))^2 = H*m := Real.sq_sqrt (mul_nonneg hH.le hm)
  have hy : a*Real.sqrt (H*m) ≤ m+a^2*H/4 := by
    have hs := sq_nonneg (Real.sqrt (H*m)-a*H/2)
    have hh : 0 ≤ H*(m+a^2*H/4-a*Real.sqrt (H*m)) := by nlinarith [hs,hx]
    have hn := (nonneg_of_mul_nonneg_right hh hH)
    linarith
  have ht := mul_le_mul_of_nonneg_left
    (onlineOptimisticGap_sqrt_variance_transfer d V U H hV hVU hU) ha
  change a*Real.sqrt (d.variance V) ≤ m+a*Real.sqrt (d.variance U)+a^2*H/4
  dsimp [m] at hy ⊢
  nlinarith [ht,hy]


/-- A fixed true-continuation transition certificate transfers to the
optimistic empirical continuation with only the exact a²H/4 penalty. This
certificate still needs an online, adaptive-sampling concentration proof. -/
theorem onlineOptimisticGap_transition_certificate
    (p d : FiniteDistribution State) (V U : State → ℝ) (H a b : ℝ)
    (hH : 0 < H) (ha : 0 ≤ a)
    (hV : ∀ s, 0 ≤ V s) (hVU : ∀ s, V s ≤ U s)
    (hU : ∀ s, U s ≤ H)
    (hfixed : p.expectation V-d.expectation V ≤ a*Real.sqrt (d.variance V)+b) :
    p.expectation V ≤ d.expectation U+a*Real.sqrt (d.variance U)+b+a^2*H/4 := by
  have h := onlineOptimisticGap_radius_absorb d V U H a hH ha hV hVU hU
  rw [FiniteDistribution.expectation_sub] at h
  linarith

end StatisticalRL.OnlineRL
