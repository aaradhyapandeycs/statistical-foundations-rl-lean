# Independent check of the proposed Theorem 3.7 repair

This is an independent mathematical check of the argument in
[critic-theorem37-correction.md](critic-theorem37-correction.md), not a Lean
proof or an author-approved erratum. The checked candidate keeps the source's
accuracy and discount intervals and adds `S≥2`, `A≥2`, `N≥1`, with
`SA≥16` and the sufficient constant `c_N=1/8192`. Rewards and discount are
known, and samples are independent across all queried rows, as stated in
`generative_model_model_based.tex` lines 15–31. It permits a randomized
procedure whose policy output is deterministic and stationary.

## Checks

1. For `p=(4γ−1)/(3γ)` and `α=32(1−γ)^2 ε/(9γ²)`, the source's
   parameter lemma supplies valid Bernoulli probabilities, `1−p≥2α`, and
   `α²/(1−p)≤128(1−γ)^3 ε²`. Algebra gives
   `V₁−V₀=γα/[(1−γp)(1−γ(p+α))]>2ε`. Also
   `γp=(4γ−1)/3≥5/9`. These include the source endpoint `γ=2/3`.
2. In the policy construction, taking the good action first and then using a
   stationary policy that chooses a bad action at that state gives
   `Q*−Q^π=γ(p+α)(V₁−V₀)>ε`. Thus small sup-norm Q loss determines
   all the active-state good actions, regardless of the absorbing-state
   action. A decoder that defaults to the baseline for unmatched patterns is
   total, and its error is contained in the policy-loss event.
3. There are `K=1+(S−1)(A−1)≥1+SA/4≥5` policy hypotheses. Relative to
   the baseline, two sampled rows change. Their total KL is bounded by
   `8Nα²/(1−p)≤1024N(1−γ)^3 ε²≤(1/8)log(SA)`.
   Since `SA≥16` and `K≥SA/4`, this is at most `(1/4)log K`.
   Standard K-hypothesis Fano therefore gives worst-case error at least
   `1−1/4−log 2/log K≥1/4`. This uses K total hypotheses, correcting
   the index mismatch in the printed proof.
4. For Q estimation, the separate one-spike family has
   `K=(S−1)A≥SA/2` alternatives. Each differs from the baseline in one
   independent row and changes the optimal Q value at that coordinate by
   more than `2ε`. The mixture likelihood calculation yields
   `χ²≤((1+α²/[p(1−p)])^N−1)/K`. The proposed N bound and
   `p≥1/2` imply the exponent bound `1/32 log(SA)`; weakening it to
   `1/4 log(SA)` gives `χ²≤2/(SA)^(3/4)≤1/4`. Consequently the
   baseline-to-mixture total variation is at most `1/4`, and the sum of
   the two binary testing errors is at least `3/4`. The total test that
   flags a coordinate more than ε from its baseline value has its errors
   contained in the corresponding Q-estimation errors, giving a worst-case
   error at least `3/8`. Independent internal estimator randomness does not
   increase the data total variation.

The incorrect printed formula is independently visible by one Bellman step:
after a bad forced first action the continuation is optimal, so
`Q*(s,a_bad)=1+γpV₁`, not `V₀`. For example `γ=0.9, ε=0.1` gives an
optimal Q action gap about `0.03053`, below `2ε=0.2`, whereas the forced-good
Q loss of a bad stationary policy is about `0.19938`, above ε. This numerical
check illustrates the distinct quantities; it is not the proof above.

The proof route and displayed constants pass this mathematical check under
the stated fixed-size, known-reward, independent-sampling model. It remains a
proposed replacement: the finite statistical experiments, information-theory
inequalities, actual optimal trajectory Q semantics, and testing reductions
have not yet been formalized together in Lean. It is not evidence that the
original printed theorem is true or that the authors have accepted the repair.
