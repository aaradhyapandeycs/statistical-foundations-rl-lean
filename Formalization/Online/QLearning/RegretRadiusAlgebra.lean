import Mathlib

namespace StatisticalRL.OnlineRL

/-- Deterministic comparison of the explicit horizon/transition radius with
one leading rate and the lower-order initialization term. -/
theorem qLearning_regret_radius_coarse (H N K L ℓ Λ e : ℝ)
    (hH : 1≤H) (hN : 1≤N) (hK : 0≤K)
    (hΛ : 1≤Λ) (hLL : L≤Λ) (hℓΛ : ℓ≤Λ) (he : 0≤e) :
    e*H*(N*H+16*Real.sqrt (H^3*L)*Real.sqrt N*Real.sqrt K) +
      Real.sqrt (2*(K*H*(e*H)^2)*ℓ) ≤
      (18*e)*Real.sqrt (H^5*N*K*Λ)+e*H^2*N := by
  have hH0 : 0≤H := by linarith
  have hN0 : 0≤N := by linarith
  have hΛ0 : 0≤Λ := by linarith
  let Q := Real.sqrt (H^5*N*K*Λ)
  let U := H*Real.sqrt (H^3*L)*Real.sqrt N*Real.sqrt K
  have hQeq : Q = H*Real.sqrt (H^3*Λ)*Real.sqrt N*Real.sqrt K := by
    dsimp only [Q]
    rw [show H^5*N*K*Λ=(H^2*(H^3*Λ))*N*K by ring]
    rw [Real.sqrt_mul (by positivity : 0≤(H^2*(H^3*Λ))*N),
      Real.sqrt_mul (by positivity : 0≤H^2*(H^3*Λ)),Real.sqrt_mul (sq_nonneg H),Real.sqrt_sq hH0]
  have hUQ : U≤Q := by
    rw [hQeq]
    dsimp only [U]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hLL (pow_nonneg hH0 3))) hH0) (Real.sqrt_nonneg N))
      (Real.sqrt_nonneg K)
  have hdim : 1≤H^2*N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) hN
  have hbase : H^3*K*Λ≤H^5*N*K*Λ := by
    calc
      _ = (H^3*K*Λ)*1 := by ring
      _ ≤ (H^3*K*Λ)*(H^2*N) := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ = _ := by ring
  have htailrad : 2*(K*H*(e*H)^2)*ℓ≤4*e^2*(H^5*N*K*Λ) := by
    calc
      _ = (2*e^2*(H^3*K))*ℓ := by ring
      _ ≤ (2*e^2*(H^3*K))*Λ := mul_le_mul_of_nonneg_left hℓΛ (by positivity)
      _ = (2*e^2)*(H^3*K*Λ) := by ring
      _ ≤ (2*e^2)*(H^5*N*K*Λ) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ 4*e^2*(H^5*N*K*Λ) :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg e]) (by positivity)
  have htail : Real.sqrt (2*(K*H*(e*H)^2)*ℓ)≤2*e*Q := by
    calc
      _ ≤ Real.sqrt (4*e^2*(H^5*N*K*Λ)) := Real.sqrt_le_sqrt htailrad
      _ = 2*e*Q := by
        rw [show 4*e^2*(H^5*N*K*Λ)=(2*e)^2*(H^5*N*K*Λ) by ring,
          Real.sqrt_mul (sq_nonneg (2*e)),Real.sqrt_sq (by positivity : 0≤2*e)]
  have hUscaled := mul_le_mul_of_nonneg_left hUQ (show 0≤16*e by positivity)
  have heq : e*H*(N*H+16*Real.sqrt (H^3*L)*Real.sqrt N*Real.sqrt K)=e*H^2*N+16*e*U := by dsimp [U]; ring
  rw [heq]
  change e*H^2*N+16*e*U+Real.sqrt (2*(K*H*(e*H)^2)*ℓ)≤(18*e)*Q+e*H^2*N
  linarith

end StatisticalRL.OnlineRL
