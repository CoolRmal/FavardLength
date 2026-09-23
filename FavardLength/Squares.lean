import FavardLength.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Square codes, projected multiplicity, and energy

Frozen definitions shared by every part of the development. A depth-`n` construction square of
`K_n` is coded by `w : Fin n → Bool × Bool`; level `j` contributes `3 · 4^{-(j+1)}` to the
x-coordinate (resp. y-coordinate) of the lower-left corner when the first (resp. second)
component of `w j` is `true`.
-/

open MeasureTheory Set Real

namespace Favard

/-- A depth-`n` square code: a pair of binary digits (x-digit, y-digit) at each level. -/
abbrev SqCode (n : ℕ) := Fin n → Bool × Bool

/-- The left endpoint `∑_{j<n} 3 [b_j] 4^{-(j+1)}` of the interval of `C_n` coded by `b`. -/
noncomputable def leftEnd {n : ℕ} (b : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, (if b j then (3 : ℝ) else 0) / 4 ^ ((j : ℕ) + 1)

/-- The lower-left corner of the square coded by `w`. -/
noncomputable def corner {n : ℕ} (w : SqCode n) : ℝ × ℝ :=
  (leftEnd fun j => (w j).1, leftEnd fun j => (w j).2)

/-- The closed depth-`n` square coded by `w`, of side `4^{-n}`. -/
noncomputable def square {n : ℕ} (w : SqCode n) : Set (ℝ × ℝ) :=
  Icc (corner w).1 ((corner w).1 + 1 / 4 ^ n) ×ˢ Icc (corner w).2 ((corner w).2 + 1 / 4 ^ n)

open Classical in
/-- The multiplicity `f_n(x)` of the direction-`θ` projections of the depth-`n` squares at `x`:
the number of depth-`n` squares `Q` with `x ∈ π_θ(Q)`. -/
noncomputable def count (n : ℕ) (θ x : ℝ) : ℕ :=
  (Finset.univ.filter fun w : SqCode n => x ∈ proj θ '' square w).card

/-- The projection energy `‖f_n‖₂² = ∫ f_n(x)² dx` in direction `θ`. -/
noncomputable def energy (n : ℕ) (θ : ℝ) : ℝ :=
  ∫ x, (count n θ x : ℝ) ^ 2

end Favard
