import FavardLength.Fourier.Annular.Expansion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The high-frequency mass on the central interval

On `0 ≤ ξ ≤ (3/8) 4^r` the sinc factor `sinc((4/3) 4^{-r} ξ)` of the normalized energy has
argument in `[0, 1/2]`, so its square is at least `1/2`. Since the integrand of `normEnergy` is
nonnegative and integrable (`sinc(x)² ≤ 2/(1 + x²)` and `|ν̂| ≤ 1`), this gives
`∫_0^{(3/8)4^r} ν̂_{r,t}² ≤ 4π · normEnergy r t`. Rescaling `ξ = 4^n y` turns this into the
bound (manuscript, P3, second display, one-sided form)

`∫_0^{3/(8L)} P₂(t, y)² dy ≤ 4π · normEnergy (n - m) t / 4^n`, with `L = 4^m`.
-/

open Real MeasureTheory

namespace Favard

namespace Annular

/-- `sinc(x)² (1 + x²) ≤ 2`. -/
lemma sinc_sq_mul_one_add_sq_le (x : ℝ) : sinc x ^ 2 * (1 + x ^ 2) ≤ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · have h1 : sinc x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (abs_sinc_le_one x)
    have h2 : sinc x ^ 2 * x ^ 2 = sin x ^ 2 := by
      rw [sinc_of_ne_zero hx]
      field_simp
    nlinarith [sin_sq_le_one x]

/-- `sinc(x)² ≤ 2/(1 + x²)`. -/
lemma sinc_sq_le (x : ℝ) : sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact sinc_sq_mul_one_add_sq_le x

/-- `sinc(x)² ≥ 1/2` for `0 ≤ x ≤ 1/2`. -/
lemma half_le_sinc_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : 1 / 2 ≤ sinc x ^ 2 := by
  rcases eq_or_lt_of_le h0 with rfl | hx
  · norm_num
  · have hs := sin_gt_sub_cube hx
    rw [sinc_of_ne_zero hx.ne']
    have h : 1 - x ^ 2 / 6 ≤ sin x / x := by
      rw [le_div_iff₀ hx]
      nlinarith
    have h2 : 23 / 24 ≤ 1 - x ^ 2 / 6 := by nlinarith
    nlinarith

/-- The integrand of `normEnergy` is integrable. -/
lemma integrable_sinc_sq_mul_nuHat_sq (r : ℕ) (t : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun ξ => sinc (a * ξ) ^ 2 * nuHat r t ξ ^ 2) := by
  refine ((integrable_inv_one_add_mul_sq ha).const_mul 2).mono'
    (by apply Continuous.aestronglyMeasurable; fun_prop) (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc sinc (a * ξ) ^ 2 * nuHat r t ξ ^ 2 ≤ sinc (a * ξ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (nuHat_sq_le_one r t ξ) (sq_nonneg _)
    _ ≤ 2 * (1 + (a * ξ) ^ 2)⁻¹ := by
        rw [mul_one]
        exact sinc_sq_le _

/-- **Central bound in the frequency variable**:
`∫_0^{(3/8) 4^r} ν̂_{r,t}(ξ)² dξ ≤ 4π · normEnergy r t`. -/
lemma integral_nuHat_sq_le (r : ℕ) (t : ℝ) :
    ∫ ξ in (0 : ℝ)..(3 / 8 * 4 ^ r), nuHat r t ξ ^ 2 ≤ 4 * π * normEnergy r t := by
  have ha : (4 / 3 / 4 ^ r : ℝ) ≠ 0 := by positivity
  have hg := integrable_sinc_sq_mul_nuHat_sq r t ha
  have hX : (0 : ℝ) ≤ 3 / 8 * 4 ^ r := by positivity
  calc ∫ ξ in (0 : ℝ)..(3 / 8 * 4 ^ r), nuHat r t ξ ^ 2
      ≤ ∫ ξ in (0 : ℝ)..(3 / 8 * 4 ^ r), 2 * (sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2) := by
        refine intervalIntegral.integral_mono_on hX
          (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop) fun ξ hξ => ?_
        have hx0 : 0 ≤ 4 / 3 / 4 ^ r * ξ := mul_nonneg (by positivity) hξ.1
        have hx1 : 4 / 3 / 4 ^ r * ξ ≤ 1 / 2 := by
          calc 4 / 3 / 4 ^ r * ξ ≤ 4 / 3 / 4 ^ r * (3 / 8 * 4 ^ r) :=
                mul_le_mul_of_nonneg_left hξ.2 (by positivity)
            _ = 1 / 2 := by field_simp; norm_num
        have := half_le_sinc_sq hx0 hx1
        nlinarith [sq_nonneg (nuHat r t ξ)]
    _ = 2 * ∫ ξ in (0 : ℝ)..(3 / 8 * 4 ^ r), sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ 2 * ∫ ξ, sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2 := by
        gcongr
        rw [intervalIntegral.integral_of_le hX]
        exact setIntegral_le_integral hg
          (ae_of_all _ fun ξ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = 4 * π * normEnergy r t := by
        unfold normEnergy
        field_simp
        ring

/-- **Central bound**: `∫_0^{3/(8L)} P₂(t, y)² dy ≤ 4π · normEnergy (n - m) t / 4^n`. -/
lemma integral_highProd_sq_central_le {m n : ℕ} (hmn : m ≤ n) (t : ℝ) :
    ∫ y in (0 : ℝ)..(3 / 8 / 4 ^ m), highProd m n t y ^ 2 ≤
      4 * π * normEnergy (n - m) t / 4 ^ n := by
  simp_rw [highProd_eq_nuHat hmn]
  rw [intervalIntegral.integral_comp_mul_left (fun ξ => nuHat (n - m) t ξ ^ 2)
    (by positivity : (4 : ℝ) ^ n ≠ 0)]
  have h4 : (4 : ℝ) ^ n * (3 / 8 / 4 ^ m) = 3 / 8 * 4 ^ (n - m) := by
    have : (4 : ℝ) ^ n = 4 ^ (n - m) * 4 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [this]
    field_simp
  rw [mul_zero, h4, smul_eq_mul, div_eq_inv_mul (4 * π * normEnergy (n - m) t)]
  exact mul_le_mul_of_nonneg_left (integral_nuHat_sq_le _ _) (inv_nonneg.2 (by positivity))

end Annular

end Favard
