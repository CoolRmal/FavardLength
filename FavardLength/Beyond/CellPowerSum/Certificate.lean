import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The numerical certificate `ρ_* + κ ≤ 4^{-β₀}`

With `β₀ = 3071/10000` we show `653285/10^6 ≤ 4^{-β₀}` (`Favard.CellPowerSum.certificate`).
Numerically `4^{-β₀} ≈ 0.65329206`, while the transfer constant is
`261313/400000 + 2/10^7 = 0.6532827` (`ρ_* ≈ 0.65328148`), so `653285/10^6` sits in between.

Raising to the power `10000`, the claim is the exact natural-number inequality
`653285^10000 · 4^3071 ≤ 10^60000` (`Favard.CellPowerSum.certificate_nat`), which the kernel
checks with its GMP-accelerated natural-number arithmetic.
-/

namespace Favard

namespace CellPowerSum

set_option exponentiation.threshold 100000 in
/-- The exact form of the certificate: `653285^10000 · 4^3071 ≤ 10^60000`. -/
theorem certificate_nat : (653285 : ℕ) ^ 10000 * 4 ^ 3071 ≤ 10 ^ 60000 := by
  decide

/-- **The numerical certificate**: `653285/10^6 ≤ 4^{-3071/10000}`. -/
theorem certificate : (653285 / 10 ^ 6 : ℝ) ≤ (4 : ℝ) ^ (-(3071 / 10000 : ℝ)) := by
  have h : ((653285 : ℕ) : ℝ) ^ 10000 * (4 : ℝ) ^ 3071 ≤ (10 : ℝ) ^ 60000 := by
    exact_mod_cast certificate_nat
  rw [← pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (10000 : ℕ) ≠ 0),
    ← Real.rpow_natCast ((4 : ℝ) ^ _) 10000, ← Real.rpow_mul (by norm_num)]
  have he : -(3071 / 10000 : ℝ) * ((10000 : ℕ) : ℝ) = -((3071 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast, div_pow, ← pow_mul,
    div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  simpa using h

end CellPowerSum

end Favard
