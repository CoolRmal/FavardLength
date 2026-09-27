import FavardLength

/-!
# Proved solution

This module imports the full proof development and restates the six advertised theorems of
`Challenge.lean`. Comparator checks that each has exactly the Challenge statement and uses only
the permitted axioms. This module deliberately does not import `Challenge`.
-/

open MeasureTheory Set Real

namespace Favard

/-- Every exponent `a ∈ [0, 1/4)` is admissible: `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`. -/
theorem favard_le_rpow_of_lt_quarter {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1 / 4) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a) :=
  decay a ha₀ ha

/-- The decay exponent is at least one quarter: `1/4 ≤ α_Fav`. -/
theorem one_quarter_le_decayExponent : 1 / 4 ≤ decayExponent :=
  exponent_bounds.1

/-- The exponent `156307/625000 = 0.2500912 > 1/4` is admissible:
`Fav(K_n) ≤ C n^{-156307/625000}` for all `n ≥ 1`. -/
theorem favard_le_rpow_beyond_quarter :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) :=
  beyond

/-- The decay exponent exceeds one quarter: `156307/625000 ≤ α_Fav`. -/
theorem beyond_quarter_le_decayExponent : 156307 / 625000 ≤ decayExponent :=
  beyond_quarter_le_decayExponent'

/-- Every admissible exponent is at most one. -/
theorem le_one_of_mem_admissibleExponents {a : ℝ} (ha : a ∈ admissibleExponents) : a ≤ 1 :=
  admissibleExponents_subset_Iic_one lowerBound ha

/-- The decay exponent is at most one: `α_Fav ≤ 1`. -/
theorem decayExponent_le_one : decayExponent ≤ 1 :=
  exponent_bounds.2

end Favard
