import FavardLength.Statements
import FavardLength.Fourier.Annular.Kernel
import FavardLength.Fourier.Annular.Central

/-!
# Annular lower bound for the high-frequency mass (P3)

We prove `Favard.AnnularStatement` with `A₀ = 16π` and `c_a = 1/4`. Let `r = n - m`,
`M = 4^r`, `L = 4^m`, and `P₂(t, y) = highProd m n t y = ν̂_{r,t}(4^n y)`.

* `Annular.inv_pow_div_two_le_integral_highProd_sq`: expanding `P₂²` over codes and integrating
  against the triangle weight `1 - y`, whose cosine transform is nonnegative, the diagonal gives
  `∫_0^1 P₂² ≥ 1/(2M)`.
* `Annular.integral_highProd_sq_central_le`: on the central interval, the sinc factor of the
  normalized energy is at least `1/√2`, so `∫_0^{3/(8L)} P₂² ≤ 4π · normEnergy r t / 4^n
  ≤ 4π H/(LM) ≤ 1/(4M)` when `16π H ≤ L`.

Subtracting, `∫_{3/(8L)}^1 P₂² ≥ 1/(4M)`. The one-sided triangle weight on `[0, 1]` replaces the
manuscript's two-sided weight together with the evenness of `P₂`.
-/

open MeasureTheory Set Real

namespace Favard

/-- **Annular lower bound for the high-frequency mass** (P3): if `16π H ≤ 4^m` and the
normalized energy of generation `n - m` is at most `H`, then
`∫_{3/(8·4^m)}^1 P₂(t, y)² dy ≥ 4^{-(n-m)}/4`. -/
theorem annular : AnnularStatement := by
  refine ⟨16 * π, 1 / 4, by positivity, by norm_num, fun H _ m n hmn hA t _ hE => ?_⟩
  have hle : m ≤ n := hmn.le
  have hb1 : (3 / 8 / 4 ^ m : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc (3 / 8 : ℝ) ≤ 1 := by norm_num
      _ ≤ 4 ^ m := one_le_pow₀ (by norm_num)
  have hcont : Continuous fun y => highProd m n t y ^ 2 := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
    (ae_of_all _ fun y => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb1,
    ← intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 1)
      (hcont.intervalIntegrable 0 _)]
  have h1 := Annular.inv_pow_div_two_le_integral_highProd_sq hle t
  have h2 := Annular.integral_highProd_sq_central_le hle t
  have h4 : (4 : ℝ) ^ n = 4 ^ (n - m) * 4 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have h3 : 4 * π * normEnergy (n - m) t / 4 ^ n ≤ ((4 : ℝ) ^ (n - m))⁻¹ / 4 := by
    rw [h4, div_le_iff₀ (by positivity)]
    have : ((4 : ℝ) ^ (n - m))⁻¹ / 4 * (4 ^ (n - m) * 4 ^ m) = 4 ^ m / 4 := by
      field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hE pi_pos.le]
  calc 1 / 4 / (4 : ℝ) ^ (n - m) = ((4 : ℝ) ^ (n - m))⁻¹ / 2 - ((4 : ℝ) ^ (n - m))⁻¹ / 4 := by
        ring
    _ ≤ _ := by linarith

end Favard
