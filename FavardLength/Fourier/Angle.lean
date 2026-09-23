import FavardLength.Statements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Exceptional directions in the angle variable

We transfer the normalized exceptional-set estimate (J9, slope variable `t ∈ [0, 1]`) to the
angle variable `θ ∈ [0, π/4]`, using the normalization bridge (P1).

For `θ ∈ [0, π/4]` put `t = tan(π/4 - θ) ∈ [0, 1]`. The bridge gives
`normEnergy r t = 3/(8σ) · energy r θ` with `σ = cos θ + sin θ ≥ 1`, so a geometric energy bound
`energy r θ ≤ H` implies the normalized bound `normEnergy r t ≤ 3H/8 ≤ H`. Hence the set of
low-energy angles is contained in the image of the set of low-energy slopes under the map
`t ↦ π/4 - arctan t`, which is `1`-Lipschitz because `|arctan'| ≤ 1`; a `1`-Lipschitz map of
`ℝ` does not increase Lebesgue measure (Hausdorff measure `μH[1] = volume`).

## Main results

* `Favard.AngleTransfer.volume_image_le`: `volume (g '' s) ≤ volume s` for `g t = π/4 - arctan t`.
* `Favard.exceptionalAngle_of`: `NormalizedExceptionalStatement → BridgeStatement →
  ExceptionalAngleStatement`, with the same constant.
-/

open MeasureTheory Set Real

namespace Favard

namespace AngleTransfer

/-- The arctangent is `1`-Lipschitz, since `arctan' x = 1/(1 + x²) ≤ 1`. -/
lemma lipschitzWith_arctan : LipschitzWith 1 arctan := by
  refine lipschitzWith_of_nnnorm_deriv_le differentiable_arctan fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.deriv_arctan, Real.norm_eq_abs, NNReal.coe_one,
    abs_of_pos (by positivity), div_le_one (by positivity)]
  nlinarith [sq_nonneg x]

/-- The inverse `t ↦ π/4 - arctan t` of `θ ↦ tan(π/4 - θ)` does not increase Lebesgue measure. -/
lemma volume_image_le (s : Set ℝ) :
    volume ((fun t => π / 4 - arctan t) '' s) ≤ volume s := by
  have h : LipschitzWith 1 fun t => π / 4 - arctan t := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := lipschitzWith_arctan.dist_le_mul y x
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at this ⊢
    rwa [show π / 4 - arctan x - (π / 4 - arctan y) = arctan y - arctan x by ring,
      abs_sub_comm x y]
  simpa [hausdorffMeasure_real] using h.hausdorffMeasure_image_le zero_le_one s

/-- For `θ ∈ [0, π/4]`, `σ = cos θ + sin θ ≥ 1`. -/
lemma one_le_cos_add_sin {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 4)) : 1 ≤ cos θ + sin θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  nlinarith [sin_sq_add_cos_sq θ, cos_le_one θ, sin_le_one θ]

/-- For `θ ∈ [0, π/4]`, the slope `tan(π/4 - θ)` lies in `[0, 1]`. -/
lemma tan_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 4)) : tan (π / 4 - θ) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hθ
  refine ⟨tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [pi_pos]), ?_⟩
  rw [← tan_pi_div_four]
  exact strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (by linarith)

/-- For `θ ∈ [0, π/4]`, `θ = π/4 - arctan (tan (π/4 - θ))`. -/
lemma sub_arctan_tan {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 4)) :
    π / 4 - arctan (tan (π / 4 - θ)) = θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])]
  ring

end AngleTransfer

open AngleTransfer in
/-- **Exceptional directions in the angle variable** (J9): the normalized estimate transfers to
the angle variable with the same constant, via the bridge (P1) and the `1`-Lipschitz inverse
`t ↦ π/4 - arctan t` of the slope map `θ ↦ tan(π/4 - θ)`. -/
theorem exceptionalAngle_of (hN : NormalizedExceptionalStatement) (hB : BridgeStatement) :
    ExceptionalAngleStatement := by
  intro s hs1 hs2
  obtain ⟨C, hC, hCb⟩ := hN s hs1 hs2
  refine ⟨C, hC, fun H hH N hN1 => le_trans (measure_mono ?_)
    ((volume_image_le _).trans (hCb H hH N hN1))⟩
  rintro θ ⟨hθ, hE⟩
  refine ⟨tan (π / 4 - θ), ⟨tan_mem_Icc hθ, fun r hr1 hrN => ?_⟩, sub_arctan_tan hθ⟩
  have hσ := one_le_cos_add_sin hθ
  have hc : 3 / (8 * (cos θ + sin θ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [hB θ hθ r]
  calc 3 / (8 * (cos θ + sin θ)) * energy r θ
      ≤ 3 / (8 * (cos θ + sin θ)) * H := by gcongr; exact hE r hr1 hrN
    _ ≤ 1 * H := by gcongr
    _ = H := one_mul H

end Favard
