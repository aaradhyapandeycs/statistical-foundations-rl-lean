# Entire-monograph Lean formalization

The goal is the complete end-to-end formalization of arXiv:2610.41903v1, all chapters, appendices, stated results, algorithms and substantive mathematical claims. Keep the full goal open until coverage, Lean proof evidence, and independent source review establish it.

## Source and skills

- Pin the source with `source/provenance.json`. Restore raw inputs with `python3 scripts/fetch_source.py`. Treat upstream files as read-only. Cite exact source labels and ranges.
- Read `skills/lean/skills/lean-workflow/SKILL.md`, then relevant focused skills. The full collection index is `skills/lean/INDEX.md`.
- Source inventory is a checklist, not a source dependency graph or proof certification. An index of theorem environments does not cover prose claims, assumptions, algorithm semantics, or omitted arguments by itself.
- No author approval or frozen statement status may be inferred or fabricated. Follow the exact approval procedure if adopting frozen anchors. Ordinary proved infrastructure may be developed and audited without inventing a frozen manifest.

## Builder and critic teams

- Builders implement real definitions and proofs in assigned files; critics reconstruct source mathematics independently and attempt to refute the translation and its assumptions.
- Keep write sets disjoint and record ownership in `docs/PROGRESS.md`. A builder cannot certify its own source fidelity. The lead integrates after critic findings are addressed.
- Worker briefs include source locators, target scope, imports, owned files, validation command, and stop condition. Use the available worker slots for independent tasks (this session permits three plus the lead), and at most two concurrent Lean compilers.
- The user explicitly excludes Astra models. Use available Sol, Terra, or Luna models for agents and continuation work; do not select Astra as a fallback.
- Preserve theorem signatures during proof completion. No hidden hypotheses, unproved intermediate inputs, weakened conclusions, fallback definitions, custom axioms, `sorry`, or `admit` in library code.
- A source error is an open obligation. Record counterevidence and proposed corrections explicitly; never silently change the paper or call a corrected statement the original theorem.

## Build and evidence

- Lean and Mathlib versions are pinned. Respect the module conventions supported by this version; no forced port to newer syntax.
- Search existing Mathlib APIs before proving. Use small compiler-guided steps and focused checks.
- Public setup: `lake exe cache get`, then `lake build` and `lake env lean Audit.lean`. Do not run `lake update` or `lake clean` during routine work.
- Local development may use ignored read-only dependency links and `scripts/lean-local.sh`; never write dependency artifacts or rebuild shared packages through those links. Only project artifacts go in this project's `.lake/build`.
- `python3 scripts/check.py` compiles the local import closure and runs the axiom audit without rebuilding dependencies. Report actual commands, source hashes, failures and skipped checks.
- Completion requires full source correspondence, meaningful definitions, completed prerequisites, compiled actual exports, and transitive axiom closure allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- Performance claims require measurements. Public release checks include licenses, source provenance, explicit incomplete status, no private local paths, and no transient probes.

The user authorized a public maintained GitHub repository under `aaradhyapandeycs`. Public status must continue to distinguish infrastructure from completed source results and whole-paper completion.
