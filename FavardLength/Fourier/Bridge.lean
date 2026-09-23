import FavardLength.Basic
import FavardLength.Statements
import FavardLength.Fourier.Bridge.Digits

/-!
# The normalization bridge (P1)

For `θ ∈ [0, π/4]`, `σ = cos θ + sin θ`, `a = 3σ/8` and `t = tan(π/4 - θ) = (cos θ - sin θ)/σ`,
we prove `normEnergy r t = 3/(8σ) · energy r θ`.

By `Favard.Bridge.abs_proj_corner_sub`, projected corners differ by `a` times the differences of
the normalized points `c_w(t)`; since `σ 4^{-r} = a ρ 4^{-r}` with `ρ = 8/3`, the overlap formula
`energy_eq_sum_overlap` gives

`energy r θ = a ∑_{w,w'} (ρ 4^{-r} - |c_w(t) - c_{w'}(t)|)_+`.

The triangle identity with `ℓ = ρ 4^{-r}` writes each overlap as
`(2π)⁻¹ ∫ ℓ² sinc(ℓξ/2)² cos(ξ (c_w - c_{w'})) dξ`; summing under the integral and using
`∑_{w,w'} cos(ξ (c_w - c_{w'})) = 16^r ν̂_{r,t}(ξ)²` (`Favard.Bridge.sum_sum_cos_code`) and
`ℓ² 16^r = ρ²`, the double sum equals `ρ² · normEnergy r t`. Hence
`energy r θ = a ρ² normEnergy r t = (8σ/3) normEnergy r t`.

## Main results

* `Favard.Bridge.sum_sum_max_eq`: `∑_{w,w'} (ρ 4^{-r} - |c_w - c_{w'}|)_+ = ρ² normEnergy r t`.
* `Favard.bridge_of`: `TriangleStatement → BridgeStatement`.
-/

open MeasureTheory Set Real

namespace Favard

namespace Bridge

/-- `tan(π/4 - θ) = (cos θ - sin θ)/(cos θ + sin θ)`. -/
lemma tan_pi_div_four_sub (θ : ℝ) :
    tan (π / 4 - θ) = (cos θ - sin θ) / (cos θ + sin θ) := by
  rw [tan_eq_sin_div_cos, sin_sub, cos_sub, sin_pi_div_four, cos_pi_div_four, ← mul_sub,
    ← mul_add, mul_div_mul_left _ _ (by positivity)]

/-- **Fourier form of the normalized overlap sum**: with `ρ = 8/3`,
`∑_{w,w'} (ρ 4^{-r} - |c_w(t) - c_{w'}(t)|)_+ = ρ² · normEnergy r t`. -/
lemma sum_sum_max_eq (hT : TriangleStatement) (r : ℕ) (t : ℝ) :
    ∑ w : SqCode r, ∑ w' : SqCode r, max 0 (8 / 3 / 4 ^ r - |code t w - code t w'|) =
      (8 / 3) ^ 2 * normEnergy r t := by
  obtain ⟨hint, htri⟩ := hT (8 / 3 / 4 ^ r) (by positivity)
  have hi : ∀ x : ℝ, Integrable fun ξ =>
      (8 / 3 / 4 ^ r : ℝ) ^ 2 * sinc (8 / 3 / 4 ^ r / 2 * ξ) ^ 2 * cos (ξ * x) := by
    intro x
    refine (hint.const_mul _).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun ξ => ?_)
    simpa using abs_cos_le_one (ξ * x)
  calc ∑ w : SqCode r, ∑ w' : SqCode r, max 0 (8 / 3 / 4 ^ r - |code t w - code t w'|)
      = ∑ w : SqCode r, ∑ w' : SqCode r, (2 * π)⁻¹ * ∫ ξ,
          (8 / 3 / 4 ^ r : ℝ) ^ 2 * sinc (8 / 3 / 4 ^ r / 2 * ξ) ^ 2 *
            cos (ξ * (code t w - code t w')) := by
        simp only [htri]
    _ = (2 * π)⁻¹ * ∫ ξ, ∑ w : SqCode r, ∑ w' : SqCode r,
          (8 / 3 / 4 ^ r : ℝ) ^ 2 * sinc (8 / 3 / 4 ^ r / 2 * ξ) ^ 2 *
            cos (ξ * (code t w - code t w')) := by
        rw [integral_finsetSum _ fun w _ => integrable_finsetSum _ fun w' _ => hi _,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [integral_finsetSum _ fun w' _ => hi _, Finset.mul_sum]
    _ = (2 * π)⁻¹ * ∫ ξ, (8 / 3) ^ 2 * (sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
        simp only
        simp_rw [← Finset.mul_sum]
        rw [sum_sum_cos_code, show (8 / 3 / 4 ^ r / 2 : ℝ) = 4 / 3 / 4 ^ r by ring]
        field_simp
    _ = (8 / 3) ^ 2 * normEnergy r t := by
        rw [integral_const_mul, normEnergy]
        ring

end Bridge

open Bridge in
/-- **The normalization bridge** (P1): for `θ ∈ [0, π/4]`,
`normEnergy r (tan(π/4 - θ)) = 3/(8σ) · energy r θ` with `σ = cos θ + sin θ`. -/
theorem bridge_of (hT : TriangleStatement) : BridgeStatement := by
  intro θ hθ r
  obtain ⟨h0, h1⟩ := hθ
  have hσ : 0 < cos θ + sin θ := by
    have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
    linarith
  rw [energy_eq_sum_overlap ⟨h0, by linarith [pi_pos]⟩ r, tan_pi_div_four_sub]
  set t := (cos θ - sin θ) / (cos θ + sin θ)
  have h : ∀ w w' : SqCode r,
      max 0 ((cos θ + sin θ) / 4 ^ r - |proj θ (corner w) - proj θ (corner w')|) =
        3 * (cos θ + sin θ) / 8 * max 0 (8 / 3 / 4 ^ r - |code t w - code t w'|) := by
    intro w w'
    rw [abs_proj_corner_sub hσ, mul_max_of_nonneg _ _ (by positivity), mul_zero]
    congr 1
    field_simp
    ring
  simp_rw [h, ← Finset.mul_sum, sum_sum_max_eq hT]
  field_simp

end Favard
