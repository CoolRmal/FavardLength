import FavardLength.Main
import FavardLength.Beyond.CellPowerSum
import FavardLength.Beyond.JointMoment
import FavardLength.Beyond.Exceptional
import FavardLength.Beyond.NewExceptional
import FavardLength.Beyond.Assembly.Main
import FavardLength.Beyond.Assembly.Certificate
import FavardLength.Beyond.Coverage.Main
import FavardLength.Beyond.Exclusion.Main
import FavardLength.Beyond.Exclusion.Complementary
import FavardLength.Beyond.Exclusion.RelDeriv
import FavardLength.Beyond.Exclusion.Harmonic
import FavardLength.Beyond.Exclusion.CellSelection
import FavardLength.Beyond.Exclusion.FlatBlock
import FavardLength.Beyond.Exclusion.Window

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

/-- The beyond-quarter bound, given the six sub-contracts of the smooth-window exclusion. -/
theorem beyond_of_exclusion_parts (hcount : Exclusion.ComplementaryCountStatement)
    (hbound : Exclusion.ComplementaryBoundStatement) (hrel : Exclusion.RelDerivStatement)
    (hharm : Exclusion.HarmonicStatement) (hflat : Exclusion.FlatBlockStatement)
    (hwin : Exclusion.WindowBoundStatement) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond_of_exclusion
    (exclusion_of hcount hbound hrel hharm hflat hwin (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))

/-- The beyond-quarter bound, given the window bounds of the smooth-window argument. -/
theorem beyond_of_window (hwin : Exclusion.WindowBoundStatement) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond_of_exclusion_parts Exclusion.complementaryCount Exclusion.complementaryBound
    Exclusion.relDeriv Exclusion.harmonic (Exclusion.flatBlock_of Exclusion.cellSelection) hwin

/-- Smooth-window exclusion with a counted exceptional set of rationals (beyond note (6)–(7)). -/
theorem exclusion {γ ε : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ExclusionStatement γ ε :=
  exclusion_of Exclusion.complementaryCount Exclusion.complementaryBound Exclusion.relDeriv
    Exclusion.harmonic (Exclusion.flatBlock_of Exclusion.cellSelection) Exclusion.windowBound
    hγ0 hγ2 hε0 hε

/-- **The beyond-quarter bound**: `Fav(K_n) ≤ C n^{-156307/625000}` for all `n ≥ 1`. -/
theorem beyond :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond_of_window Exclusion.windowBound

/-- `156307/625000 ≤ α_Fav`. -/
theorem beyond_quarter_le_decayExponent' : 156307 / 625000 ≤ decayExponent := by
  have hsub := admissibleExponents_subset_Iic_one lowerBound
  exact le_csSup ⟨1, fun a ha => hsub ha⟩ ⟨by norm_num, beyond⟩

end Favard
