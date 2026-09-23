import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Definitions shared with the Challenge

These definitions must stay textually identical to those in `Challenge.lean`; Comparator
checks that the Solution's statements depend on definitions with the same values.
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

end Favard
