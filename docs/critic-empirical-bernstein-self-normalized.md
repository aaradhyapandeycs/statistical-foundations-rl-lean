# Independent review: empirical-variance leave-one-out structure

Reviewed 2026-11-02. Exact staged `.local/EmpiricalBernsteinSelfNormalized.lean` SHA-256 `57b62e5173016cef76514262607696eaf5dc7c679e7143fd714d126d0663ebfc`, independently recomputed at handoff. This reviewer owns only this report.

## Verdict and source boundary

**PASS for the deterministic deletion identities, minimization, nonnegative decrements and their stated constants. No stochastic self-bounding or general empirical Bernstein theorem is established.**

I checked the source `prelim.tex:983–998`, label `empirical bernstein`, and the imported actual empirical variance definition. The source target is a high-probability mean-error bound involving the variance under the empirical frequency row, N−1 outside its square root/linear term, and constants 2 and 7/3. It also requires an independent finite random vector family and strict success probability >1−δ. None of those probability conclusions or exact radius constants follows solely from these deterministic identities. The builder handoff correctly preserves that distinction.

The module's name does not change its actual scope: it contains no measure or distribution parameter, no δ, no exponential tail, and no final mean-error confidence interval. The identities are useful structural input toward the missing theorem and apply pointwise under any sample law, iid or otherwise.

## Definitions, normalization and exact identities

For actual observations x_i=V(ω_i), let m=N⁻¹∑x_i and Z be the actual frequency-row variance, namely N⁻¹∑(x_i−m)². The imported `empiricalVariance` is exactly this population-normalized variance of the empirical distribution, not the unbiased sample variance.

The new deleted mean is m_{−i}=∑_{j≠i}x_j/(N−1), and the deleted residual is

`Z_i = (1/N) ∑_{j≠i} (x_j−m_{−i})²`.

The retained denominator N is intentional. Z_i is **not** the ordinary variance of the N−1 observations, whose denominator would be N−1. Calling it a deleted residual is faithful; replacing it silently with that other variance would invalidate the decrements and constants.

The exact identities are

`Δ_i := Z−Z_i = (x_i−m)²/(N−1)`

and

`∑_i Δ_i = N Z/(N−1)`.

I independently checked the algebra: the removed residual sum is ∑_{j≠i}x_j²−(∑_{j≠i}x_j)²/(N−1), while N Z=∑x_j²−(∑x_j)²/N. Their difference is N(x_i−m)²/(N−1), and division by N yields the stated decrement. Summing uses ∑(x_i−m)²=N Z, giving exactly N/(N−1), not 1.

`leaveOneOutResidual_congr` proves changing coordinate i alone leaves Z_i unchanged. The deleted center is also justified by `leaveOneOutResidual_minimizes`: for every real c, the residual at c exceeds Z_i by `(N−1)/N * (c−m_{−i})²`. Thus the chosen deleted mean is the genuine minimizing center, not an arbitrary selected witness.

Both definitions are literal formulas on N≥2, without fallback branches. BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. The minimization theorem is additional structural evidence; no unproved characterization is used to define either object.

## Self-bound constants

Each Δ_i≥0 follows from the exact identity and N−1>0. For a vector in [0,B], the full mean and deleted mean remain in [0,B]. The file correctly proves the looser bound Δ_i≤B²/(N−1) and its consequence `∑Δ_i²≤B² N/(N−1)² Z`.

The sharp range result uses the exact alternate identity

`Δ_i = (N−1)/N² * (x_i−m_{−i})²`.

As both terms inside the difference lie in [0,B], this gives

`0≤Δ_i≤(N−1)B²/N²`.

Multiplying this upper bound by Δ_i and using the exact decrement sum yields

`∑Δ_i² ≤ ((N−1)B²/N²) * (N Z/(N−1)) = (B²/N) Z`.

The coefficient B²/N is therefore correct, with no missing factor N/(N−1). The proof does not assume this quadratic inequality as a self-bounding premise; it produces it from the actual coordinate data. It also does not assume the decrements themselves are independent.

N=2 is included, with both denominators positive. N=0 and N=1 are explicitly excluded, as needed by the deleted mean and source empirical Bernstein regime. B=0, the zero vector and any constant vector give zero variance and decrements without dividing by B or Z. The pointwise identities do not require a positive variance. A deterministic row distribution is also compatible: its actual observations are constant almost surely, although the deterministic theorems apply even to sample arrays outside that row's support.

## Dependence and input audit

The only substantive inequality premise is `∀ s, V s∈[0,B]`, in the range/self-bound lemmas. Exact algebra and minimization hold for arbitrary real-valued V without that restriction. N≥2 is explicit. Finiteness of State is needed by the imported finite distribution/variance object; the purely coordinate lemmas omit it where unused. Other binders are the sample array ω, deleted index i, comparison array ω′ and its coordinate agreement premise, or arbitrary center c in minimization. These are typing or the defining hypotheses of the named structural comparison, not source-theorem concentration premises. No excess tail probability, expected variance, iid certificate or desired mean bound is hidden in a structure or binder.

For an eventual iid use, the actual row experiment from the imported probability modules is the finite product of the true row law. Its coordinates are independent and have that row distribution. However, **this file does not prove a new stochastic independence statement between x_i and Z_i**. The congruence result supplies deleted-coordinate insensitivity, from which an appropriate measurability/product-independence lemma can be derived. It must still be supplied if the next concentration proof requires that fact. The full empirical variance Z and its decrements share observations and are generally dependent; a future proof cannot treat them as independent merely because the original x_i are iid.

Similarly, bounded V is a fixed deterministic input here. Pointwise identities can be applied to data-dependent V, but they do not then license the fixed-vector iid concentration theorem or a self-bounding-coordinate argument that assumes all other inputs fixed. A random family requires the source's actual independence and subsequent lifting argument.

## Missing stochastic theorem

The required next step is an actual finite-product exponential lower-deviation control of empirical variance/standard deviation, or an equivalent direct empirical Bernstein argument, with proved constants. A deterministic ∑Δ_i² bound or Efron–Stein expectation inequality alone is not the needed high-probability theorem.

The existing expectation identity E[Z]=(N−1)Var_P(V)/N does not supply that tail by itself. The target source radius remains

`sqrt(2 log(4|𝒱|/δ)/(N−1)) sqrt(Var_P̂(V)) + 7‖V‖∞ log(4|𝒱|/δ)/(3(N−1))`.

Confidence inversion, constants 2 and 7/3, strict >1−δ probability, and the independent random-family extension remain open. No source lemma should be marked closed by the deterministic structural module. Production integration and its actual export audit are also separate from this staged review.

## Independent compiler and axiom evidence

After coordinating the compiler slot, I copied the stable reviewed source unchanged to `.local/SelfNormalizedIndependentAudit.lean`, appended twelve `#print axioms` commands covering both definitions and every public theorem, and ran:

`bash scripts/lean-local.sh .local/SelfNormalizedIndependentAudit.lean`

Exit status 0, without warnings or errors. All twelve inspected exports report exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom declaration occurs in the reviewed source. The temporary audit source was deleted. This verifies the exact staged implementation and its transitive axiom closure; it does not establish the missing stochastic theorem.
