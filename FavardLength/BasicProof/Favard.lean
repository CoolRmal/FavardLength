import FavardLength.BasicProof.ProjLength

/-!
# The Favard length

Interval integrability of the projection length, the symmetry reduction
`Fav(K_n) = (4/π) ∫_0^{π/4} λ(π_θ(K_n)) dθ`, and the bounds `0 ≤ Fav(K_n) ≤ √2`.
-/

open MeasureTheory Set Real

namespace Favard.BasicProof

theorem intervalIntegrable_projLength (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (projLength n) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := √2) measure_Ioc_lt_top.ne
    (measurable_projLength n).aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (projLength_nonneg n θ)]
  exact projLength_le_sqrt_two n θ

/-- The symmetry `θ ↦ π - θ` halves the Favard integral. -/
theorem integral_projLength_zero_pi (n : ℕ) :
    ∫ θ in (0)..π, projLength n θ = 2 * ∫ θ in (0)..(π / 2), projLength n θ := by
  have hi := intervalIntegrable_projLength n
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 2)) (hi (π / 2) π)]
  have h : ∫ θ in (π / 2)..π, projLength n θ = ∫ θ in (0)..(π / 2), projLength n θ := by
    calc ∫ θ in (π / 2)..π, projLength n θ = ∫ θ in (π / 2)..π, projLength n (π - θ) := by
          simp_rw [projLength_pi_sub]
      _ = ∫ θ in (π - π)..(π - π / 2), projLength n θ :=
          intervalIntegral.integral_comp_sub_left _ _
      _ = ∫ θ in (0)..(π / 2), projLength n θ := by rw [sub_self, sub_half]
  rw [h]
  ring

/-- The symmetry `θ ↦ π/2 - θ` halves the integral over `[0, π/2]`. -/
theorem integral_projLength_zero_pi_div_two (n : ℕ) :
    ∫ θ in (0)..(π / 2), projLength n θ = 2 * ∫ θ in (0)..(π / 4), projLength n θ := by
  have hi := intervalIntegrable_projLength n
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 4)) (hi (π / 4) (π / 2))]
  have h : ∫ θ in (π / 4)..(π / 2), projLength n θ = ∫ θ in (0)..(π / 4), projLength n θ := by
    calc ∫ θ in (π / 4)..(π / 2), projLength n θ
        = ∫ θ in (π / 4)..(π / 2), projLength n (π / 2 - θ) := by
          simp_rw [projLength_pi_div_two_sub]
      _ = ∫ θ in (π / 2 - π / 2)..(π / 2 - π / 4), projLength n θ :=
          intervalIntegral.integral_comp_sub_left _ _
      _ = ∫ θ in (0)..(π / 4), projLength n θ := by
          rw [sub_self, show π / 2 - π / 4 = π / 4 by ring]
  rw [h]
  ring

/-- Symmetry reduction: `Fav(K_n) = (4/π) ∫_0^{π/4} λ(π_θ(K_n)) dθ`. -/
theorem favardLength_eq_quarter (n : ℕ) :
    favardLength n = 4 / π * ∫ θ in (0)..(π / 4), projLength n θ := by
  rw [favardLength, integral_projLength_zero_pi, integral_projLength_zero_pi_div_two]
  ring

theorem favardLength_nonneg (n : ℕ) : 0 ≤ favardLength n :=
  div_nonneg (intervalIntegral.integral_nonneg pi_pos.le fun θ _ => projLength_nonneg n θ)
    pi_pos.le

theorem favardLength_le_sqrt_two (n : ℕ) : favardLength n ≤ √2 := by
  rw [favardLength, div_le_iff₀ pi_pos]
  calc ∫ θ in (0)..π, projLength n θ ≤ ∫ _ in (0)..π, √2 :=
        intervalIntegral.integral_mono_on pi_pos.le (intervalIntegrable_projLength n 0 π)
          intervalIntegrable_const fun θ _ => projLength_le_sqrt_two n θ
    _ = √2 * π := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]

end Favard.BasicProof
