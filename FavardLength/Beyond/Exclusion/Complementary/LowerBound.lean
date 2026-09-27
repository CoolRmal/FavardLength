import FavardLength.Beyond.Exclusion.Transform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The complementary lower bound for the cosine products

The finite products at `x` and `x/2` together complete the binary scales (Appendix F,
Appendix H (5)): `A_n(x) A_n(x/2) = ∏_{i=2}^{2n+1} cos(πx/2^i)`, so the double-angle formula
telescopes to

`A_n(x) A_n(x/2) · 4ⁿ sin(πx/(2·4ⁿ)) = sin(πx/2)`

(`cosProd_mul_cosProd_half_mul_sin`). For an odd integer `a ≥ 1` the right side has modulus
one and `|sin y| ≤ |y|`, hence `|A_n(a)| |A_n(a/2)| ≥ 2/(πa)` for every `n`, and in the limit
`|A(a)| |A(a/2)| ≥ 2/(πa)` (`two_div_pi_mul_le_absCosProd_mul`).

Scaling out a power of four only removes cosine factors of modulus one:
`|A_{n+1}(4y)| = |A_n(y)|` for integers `y`, so `|A_n(4^v a)| ≥ |A(a)|` for every `n`
(`absCosProd_le_abs_cosProd_four_pow_mul`).
-/

open Real Finset

namespace Favard.Exclusion

/-! ### Completing the binary scales -/

/-- **Doubling identity**: `A_n(x) A_n(x/2) · 4ⁿ sin(πx/(2·4ⁿ)) = sin(πx/2)`. -/
lemma cosProd_mul_cosProd_half_mul_sin (n : ℕ) (x : ℝ) :
    cosProd n x * cosProd n (x / 2) * (4 ^ n * sin (π * x / (2 * 4 ^ n))) = sin (π * x / 2) := by
  induction n with
  | zero => simp [cosProd_zero]
  | succ n ih =>
    rw [← ih, cosProd_succ, cosProd_succ]
    set u := π * x / (2 * 4 ^ (n + 1)) with hu
    have h1 : π * x / 4 ^ (n + 1) = 2 * u := by rw [hu]; field_simp
    have h2 : π * (x / 2) / 4 ^ (n + 1) = u := by rw [hu]; field_simp
    have h3 : π * x / (2 * 4 ^ n) = 2 * (2 * u) := by rw [hu, pow_succ]; field_simp; ring
    rw [h1, h2, h3, sin_two_mul, sin_two_mul, pow_succ]
    ring

/-- `|sin(πa/2)| = 1` for odd `a`. -/
lemma abs_sin_pi_mul_odd_div_two {a : ℕ} (ha : Odd a) : |sin (π * a / 2)| = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [show π * ((2 * k + 1 : ℕ) : ℝ) / 2 = π / 2 + k * π by push_cast; ring,
    sin_add_nat_mul_pi, sin_pi_div_two, mul_one, abs_pow, abs_neg, abs_one, one_pow]

/-- **Finite complementary lower bound** (Appendix F (5)): for odd `a` and every `n`,
`|A_n(a)| |A_n(a/2)| ≥ 2/(πa)`. -/
lemma two_div_pi_mul_le_abs_cosProd_mul {a : ℕ} (ha : Odd a) (n : ℕ) :
    2 / (π * a) ≤ |cosProd n a| * |cosProd n (a / 2)| := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hsin : |sin (π * a / (2 * 4 ^ n))| ≤ π * a / (2 * 4 ^ n) := by
    have := abs_sin_le_abs (x := π * a / (2 * 4 ^ n))
    rwa [abs_of_pos (show (0 : ℝ) < π * a / (2 * 4 ^ n) by positivity)] at this
  have hone : |cosProd n a| * |cosProd n (a / 2)| * (4 ^ n * |sin (π * a / (2 * 4 ^ n))|) = 1 := by
    rw [← abs_sin_pi_mul_odd_div_two ha, ← cosProd_mul_cosProd_half_mul_sin n a, abs_mul,
      abs_mul, abs_mul, abs_of_pos h4]
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) = 2 * (|cosProd n a| * |cosProd n (a / 2)| *
        (4 ^ n * |sin (π * a / (2 * 4 ^ n))|)) := by rw [hone, mul_one]
    _ ≤ 2 * (|cosProd n a| * |cosProd n (a / 2)| * (4 ^ n * (π * a / (2 * 4 ^ n)))) := by
        gcongr
    _ = |cosProd n a| * |cosProd n (a / 2)| * (π * a) := by
        field_simp

/-- **Complementary lower bound** (Appendix H (5)): for odd `a`,
`|A(a)| |A(a/2)| ≥ 2/(πa)`. -/
theorem two_div_pi_mul_le_absCosProd_mul {a : ℕ} (ha : Odd a) :
    2 / (π * a) ≤ absCosProd a * absCosProd (a / 2) :=
  ge_of_tendsto' ((tendsto_abs_cosProd _).mul (tendsto_abs_cosProd _))
    (two_div_pi_mul_le_abs_cosProd_mul ha)

/-! ### Removing powers of four -/

/-- Splitting off the coarsest factor: `A_{n+1}(4y) = cos(πy) A_n(y)`. -/
lemma cosProd_succ_four_mul (n : ℕ) (y : ℝ) :
    cosProd (n + 1) (4 * y) = cos (π * y) * cosProd n y := by
  unfold cosProd
  rw [prod_range_succ', mul_comm]
  congr 1
  · congr 1
    ring
  · refine prod_congr rfl fun j _ => ?_
    congr 1
    rw [pow_succ _ (j + 1)]
    field_simp

/-- `|A(a)| ≤ |A_n(4^v a)|` for every integer `a ≥ 0` and all `v, n`: the first `min(v, n)`
factors of `A_n(4^v a)` have modulus one and the others form `A_{n-v}(a)`. -/
lemma absCosProd_le_abs_cosProd_four_pow_mul (a : ℕ) :
    ∀ v n : ℕ, absCosProd a ≤ |cosProd n (4 ^ v * a)|
  | 0, n => by simpa using absCosProd_le n a
  | v + 1, 0 => by simpa [cosProd_zero] using absCosProd_le_one a
  | v + 1, n + 1 => by
    have hcos : |cos (π * (4 ^ v * a))| = 1 := by
      have := abs_cos_int_mul_pi ((4 ^ v * a : ℕ) : ℤ)
      push_cast at this
      rwa [mul_comm] at this
    rw [pow_succ', mul_assoc, cosProd_succ_four_mul, abs_mul, hcos, one_mul]
    exact absCosProd_le_abs_cosProd_four_pow_mul a v n

end Favard.Exclusion
