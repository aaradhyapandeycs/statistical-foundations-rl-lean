# Conditional final arithmetic for sharp policy evaluation

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines 500–634, especially `eq:defn-b123-mb-pe`, `eqn:Chopin`, `eq:T1-bound`, `eq:T2-bound` and `eqn:ice-cream`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyEvaluationFinalArithmetic.lean` proves a conditional deterministic algebra lemma `auxiliary_source_high_sample_radius`. Let `h=1−γ`, `a=√(β/N)`, `b₁=γa`, `b₂=√2·a/√h+a²/h` and `b₃=√2/(γ√h)`. For `0<γ≤1`, `0<h≤1`, `β≥0`, `N>0`, `N≥64β/h`, depth `m≥−log h`, nonnegative `V₀≤1/h`, and the **explicit source intermediate inputs**

```text
E_l ≤ b₁ E_{l+1}+b₂ V_l               for l<m,
V_l ≤ b₃^l V₀                         for l≤m,
E_m ≤ (γ/h)(a+a²)V_m,
```

it derives `E₀ ≤ 3√(8β/(h³N))`. This is purely real-sequence arithmetic: the file does not claim that arbitrary `E,V` satisfy the premises, or that any sampling event occurs. It uses the exact source coefficients and terminal bound; an actual policy-evaluation theorem must first connect the reviewed conditional recursion, true auxiliary growth, and Bernstein event to all these premises, including the terminal level.

The proof derives `b₁b₃≤1/4≤1/2` and `b₁b₃≤e⁻¹` from the source's sufficient sample threshold, unrolls the recursion, and uses `m≥−log h` to control the terminal geometric tail. This depth condition is weaker than the source-selected `m=⌈log(e/h)⌉`; the file proves the source ceiling satisfies it. The source's final weaker `N≥β/h` display is not claimed by this lemma. The separately proved deterministic small-sample bound may bridge that range, but no statistical theorem is asserted here. The source factor `1/γ` is only used under `γ>0`; the independently staged auxiliary growth result proves empirical and true auxiliary values are exactly equal at all levels when `γ=0`.

Validation: built `.local/PolicyEvaluationRecursiveUnroll.olean` from the unchanged staged file with `bash scripts/lean-local.sh -o .local/PolicyEvaluationRecursiveUnroll.olean .local/PolicyEvaluationRecursiveUnroll.lean`, then compiled via `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyEvaluationFinalArithmetic.lean'`. Both passed. Exact-source temporary axiom probes of `auxiliary_source_high_sample_radius` and `auxiliary_source_ceiling_depth` reported only `propext`, `Classical.choice`, and `Quot.sound`. Arithmetic file SHA-256 `d061e921165f62a43bde0b04b38e2ef52ac7eefafd11089987a5b122503dbfeb`; staged recursion dependency SHA-256 `65c60bebfc05de1b07abd78569e1d9f19f0363e72a3d31990e29044693451109`. Independent source and semantic review and integrated-export validation remain outstanding.
