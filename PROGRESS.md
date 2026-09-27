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

- 2026-09-23: Moved to Lean and Mathlib v4.35.0-rc2, Palomar's new minimum, and adopted
  PalomarTemplate `cb5c79b`: the toolchain's `lake comparator` under bubblewrap with the NanoDa
  and con-ron kernels. The development built unchanged. A local run of `lake comparator`
  without the sandbox accepted the Solution.
- 2026-09-23: Shortened the registry abstract.
- 2026-09-26/27: Strict improvement beyond 1/4 (the beyond note). Contracts frozen at
  `1d58689`; thirteen agents proved the improved baseline, rational coverage, the new exceptional
  estimate, the assembly, and (through six sub-contracts) the smooth-window exclusion. Commit
  `36fbea2` adds `favard_le_rpow_beyond_quarter` (`Fav(K_n) ≤ C n^{-156307/625000}`) and
  `beyond_quarter_le_decayExponent` (`156307/625000 ≤ α_Fav`) to the Challenge and proves them.
  All six compared theorems use only `propext`, `Classical.choice` and `Quot.sound`, and a local
  `lake comparator --paranoid` run accepts the Solution with every bundled kernel.

Remaining before registration: a passing Comparator run on the final commit, then Palomar intake
and review, which need the maintainer's explicit go-ahead.
