import FavardLength.Main
import FavardLength.Beyond.CellPowerSum
import FavardLength.Beyond.JointMoment
import FavardLength.Beyond.Exceptional
import FavardLength.Beyond.NewExceptional
import FavardLength.Beyond.Assembly.Main
import FavardLength.Beyond.Assembly.Certificate
import FavardLength.Beyond.Coverage.Main

/-!
# Wiring for the beyond-quarter exponent

Plugs the proved contracts of `FavardLength/Beyond/Statements.lean` into the assembly
`beyond_of`. The improved baseline comes from the cell-power sum, the improved joint moment and
the improved exceptional-direction estimate. The new exceptional-energy estimate comes from
exclusion and coverage.
-/

namespace Favard

/-- The improved exceptional-direction estimate at `s₀ = 1/2 - 1/10^7`, `β₀ = 3071/10000`. -/
theorem exceptionalImproved :
    ExceptionalImprovedStatement (1 / 2 - 1 / 10 ^ 7) (3071 / 10000) :=
  exceptionalImproved_of window annular (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jointMomentImproved_of (sineCell_of meanOne) hilbert (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cellPowerSum)

/-- The beyond-quarter bound, given smooth-window exclusion and rational coverage. -/
theorem beyond_of_exclusion_coverage (hX : ExclusionStatement (13 / 125) (1 / 100000))
    (hC : CoverageStatement) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond_of dichotomy (bridge_of triangle) exceptionalImproved
    (newExceptional_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((by norm_num : (0 : ℝ) < 1349 / 25000).trans Assembly.redundancyExp_gt) hX hC)

/-- The beyond-quarter bound, given smooth-window exclusion. -/
theorem beyond_of_exclusion (hX : ExclusionStatement (13 / 125) (1 / 100000)) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond_of_exclusion_coverage hX coverage

end Favard
