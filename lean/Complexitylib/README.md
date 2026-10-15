# Vendored switching-lemma proof

This is the dependency closure of `Algebraic.LowerBound.AC0.Switching` from
[SamuelSchlesinger/complexitylib](https://github.com/SamuelSchlesinger/complexitylib),
pinned at `add0aca8ee0d71e68969f2cb45cf91554a50f787`. Its circuit dependencies
under `../Cslib/` come from [leanprover/cslib](https://github.com/leanprover/cslib),
pinned at `311d27ad8458b61e9b7461fc83a480e4be97aef2`.

The 29 modules have been ported to this project's Lean/mathlib 4.19.0 and
checked individually. The semantic DNF and CNF switching bounds and the
combined-advice injection/count were audited for axioms; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No axiom, `sorry`, or
`native_decide` was introduced.

Compatibility edits remove the newer module/public syntax; replace renamed
conditional, `Fin.ofNat`, list-order, and ordered-multiplication APIs; and make
a few coercion and extensionality arguments explicit. `Cslib.Init` imports
mathlib instead of newer linter/tactic configuration. The mathematical
definitions and statements are unchanged. One private list-index helper
uses `DecidableEq` rather than `BEq`/`LawfulBEq`, at its finite-coordinate use.

This dependency supplies **single-formula** switching with bound `(5pt)^s`.
Tal's family common-partial-decision-tree theorem and full Fourier-tail
theorem are proved separately by this project's `TalMultiSwitching.lean`
and `TalComplete.lean`; neither is an imported premise.

The original copyright headers are preserved. `Algebraic/` is MIT licensed
(`Algebraic/LICENSE`); the root and `Cslib/` code is Apache-2.0 licensed
(`LICENSE` and `../Cslib/LICENSE`).

These are substantive proofs by Samuel Schlesinger, not proofs originally
authored by this project. The CSLib initialization dependency also retains
Jesse Alama's author notice. Our port and integration do not supersede these
credits. See the project-wide [NOTICE](../NOTICE) for acknowledgments,
modifications, and redistribution information, and
[third_party_manifest.json](../third_party_manifest.json) for the exact
per-file upstream provenance. Keep the full licenses and original notices
when redistributing these sources or compiled derivatives.
