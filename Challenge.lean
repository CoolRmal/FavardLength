import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Favard-length decay exponent of the four-corner Cantor set

`C_n ⊆ ℝ` is the depth-`n` approximant of the middle-half Cantor set: the union, over the
`2^n` digit strings `w ∈ {0,3}^n`, of the closed intervals
`[∑_{j=1}^n w_j 4^{-j}, ∑_{j=1}^n w_j 4^{-j} + 4^{-n}]`. The four-corner approximant is
`K_n = C_n × C_n`, a union of `4^n` closed squares of side `4^{-n}`.

With `π_θ(x,y) = x cos θ + y sin θ` and `λ` Lebesgue measure on `ℝ`, the Favard length of `K_n` is
`Fav(K_n) = (1/π) ∫_0^π λ(π_θ(K_n)) dθ`. An exponent `a ≥ 0` is admissible when
`Fav(K_n) ≤ C n^{-a}` for some `C > 0` and every `n ≥ 1`. The decay exponent `α_Fav` is the
supremum of the admissible exponents, taken in `ℝ`.

The results: every `a ∈ [0, 1/4)` is admissible, so `1/4 ≤ α_Fav`. The elementary lower bound
`Fav(K_n) ≥ 1/(4n + √2)` gives `α_Fav ≤ 1`. Neither result asserts that `1/4` itself is
admissible.

The deliberate `sorry`s specify the statements; the proofs are in `Solution.lean`.
-/

open MeasureTheory Set Real

namespace Favard

/-- The depth-`n` approximant `C_n` of the middle-half Cantor set: the union over digit strings
`w ∈ {0,3}^n` of `[∑_{j=1}^n w_j 4^{-j}, ∑_{j=1}^n w_j 4^{-j} + 4^{-n}]`. Here `w` is indexed by
`Fin n`, and the digit with index `j` has weight `4^{-(j+1)}`. -/
noncomputable def cantorApprox (n : ℕ) : Set ℝ :=
  ⋃ w ∈ {w : Fin n → ℝ | ∀ j, w j = 0 ∨ w j = 3},
    Icc (∑ j : Fin n, w j / 4 ^ ((j : ℕ) + 1))
      (∑ j : Fin n, w j / 4 ^ ((j : ℕ) + 1) + 1 / 4 ^ n)

/-- The four-corner Cantor approximant `K_n = C_n × C_n`. -/
def fourCorner (n : ℕ) : Set (ℝ × ℝ) :=
  cantorApprox n ×ˢ cantorApprox n

/-- The projection `π_θ(x, y) = x cos θ + y sin θ`. -/
noncomputable def proj (θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * cos θ + p.2 * sin θ

/-- The Lebesgue length `λ(π_θ(K_n))` of the projection of `K_n` in direction `θ`. -/
noncomputable def projLength (n : ℕ) (θ : ℝ) : ℝ :=
  (volume (proj θ '' fourCorner n)).toReal

/-- The Favard length `Fav(K_n) = (1/π) ∫_0^π λ(π_θ(K_n)) dθ`. -/
noncomputable def favardLength (n : ℕ) : ℝ :=
  (∫ θ in (0)..π, projLength n θ) / π

/-- The admissible exponents: `a ≥ 0` such that `Fav(K_n) ≤ C n^{-a}` for some `C > 0` and
every `n ≥ 1`. -/
def admissibleExponents : Set ℝ :=
  {a | 0 ≤ a ∧ ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a)}

/-- The Favard-length decay exponent `α_Fav`, the real supremum of the admissible exponents. -/
noncomputable def decayExponent : ℝ :=
  sSup admissibleExponents

/-- Every exponent `a ∈ [0, 1/4)` is admissible: `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`. -/
theorem favard_le_rpow_of_lt_quarter {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1 / 4) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a) := by
  sorry

/-- The decay exponent is at least one quarter: `1/4 ≤ α_Fav`. -/
theorem one_quarter_le_decayExponent : 1 / 4 ≤ decayExponent := by
  sorry

/-- The decay exponent is at most one: `α_Fav ≤ 1`. -/
theorem decayExponent_le_one : decayExponent ≤ 1 := by
  sorry

end Favard
