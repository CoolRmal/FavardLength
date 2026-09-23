# Progress

- 2026-09-23 01:13 EDT: Project created from PalomarTemplate `d06eea17` (Lean v4.34.0,
  Mathlib v4.34.0). The Challenge statements, frozen definitions, and fourteen part contracts are
  in `FavardLength/Statements.lean`.
- 2026-09-23 02:06 EDT: All parts proved (commit `a3cb6a5`); `Main.lean` assembles them and
  `Solution.lean` proves the Challenge theorems. `#print axioms` shows only `propext`,
  `Classical.choice` and `Quot.sound`.
- 2026-09-23: CI ran the pinned Comparator on `a3cb6a5` in the Landrun sandbox: "nanoda kernel
  accepts the solution", "Lean default kernel accepts the solution".
- 2026-09-23: The Challenge docstring was corrected, since the lower-bound constant proved is
  1/320, and the junk-free statement `le_one_of_mem_admissibleExponents` was added. The literature
  search (`docs/literature.md`), the informal proof account (`docs/proof-account.md`), and the
  Palomar metadata were completed.

Remaining before registration: a passing Comparator run on the final commit, then Palomar intake
and review, which need the maintainer's explicit go-ahead.
