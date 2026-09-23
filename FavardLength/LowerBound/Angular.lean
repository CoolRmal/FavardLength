import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Angular separation for the elementary lower bound

For a vector `v = (v₁, v₂)` of length at least `d`, the linear form
`θ ↦ v₁ cos θ + v₂ sin θ` can be small only on a short set of angles of `[0, π/2]`: if it is at
most `δ` in absolute value at two angles `θ, θ' ∈ [0, π/2]` and `2δ ≤ d`, then
`|θ' - θ| ≤ 5δ/d`. This is the angular estimate behind (L2) of the manuscript.

The proof avoids polar coordinates: writing `q = -v₁ sin θ + v₂ cos θ` for the derivative of the
form at `θ`, the rotation identity gives `q sin (θ' - θ) = g(θ') - g(θ) cos (θ' - θ)`, while
`g(θ)² + q² = |v|²`. Jordan's inequality `(2/π)|x| ≤ |sin x|` then bounds `|θ' - θ|`.
-/

open Real

namespace Favard.LowerBound

/-- Rotation identity: the linear form at `θ'` in terms of the form and its derivative at `θ`. -/
theorem linForm_rotate (v₁ v₂ θ θ' : ℝ) :
    v₁ * cos θ' + v₂ * sin θ' =
      (v₁ * cos θ + v₂ * sin θ) * cos (θ' - θ) + (-v₁ * sin θ + v₂ * cos θ) * sin (θ' - θ) := by
  have h : θ' = θ + (θ' - θ) := by ring
  conv_lhs => rw [h, cos_add, sin_add]
  ring

/-- **Angular separation.** If `d² ≤ v₁² + v₂²`, `2δ ≤ d`, and `|v₁ cos θ + v₂ sin θ| ≤ δ` at two
angles `θ, θ' ∈ [0, π/2]`, then `|θ' - θ| ≤ 5δ/d`. -/
theorem abs_sub_le_of_abs_linForm_le {v₁ v₂ d δ θ θ' : ℝ} (hd : 0 < d)
    (hv : d ^ 2 ≤ v₁ ^ 2 + v₂ ^ 2) (hδ : 2 * δ ≤ d) (hθ : θ ∈ Set.Icc 0 (π / 2))
    (hθ' : θ' ∈ Set.Icc 0 (π / 2)) (h : |v₁ * cos θ + v₂ * sin θ| ≤ δ)
    (h' : |v₁ * cos θ' + v₂ * sin θ'| ≤ δ) :
    |θ' - θ| ≤ 5 * δ / d := by
  set g := v₁ * cos θ + v₂ * sin θ with hg
  set q := -v₁ * sin θ + v₂ * cos θ with hq
  set x := θ' - θ with hx
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans h
  have hgq : g ^ 2 + q ^ 2 = v₁ ^ 2 + v₂ ^ 2 := by
    have := sin_sq_add_cos_sq θ
    simp only [hg, hq]
    linear_combination (v₁ ^ 2 + v₂ ^ 2) * this
  -- `|q sin x| ≤ 2δ` from the rotation identity
  have hqs : |q| * |sin x| ≤ 2 * δ := by
    have e := linForm_rotate v₁ v₂ θ θ'
    have hqx : q * sin x = (v₁ * cos θ' + v₂ * sin θ') - g * cos x := by
      rw [e]; ring
    rw [← abs_mul, hqx]
    have hgc : |g * cos x| ≤ δ := by
      rw [abs_mul]
      calc |g| * |cos x| ≤ |g| * 1 := by gcongr; exact abs_cos_le_one x
        _ = |g| := mul_one _
        _ ≤ δ := h
    calc |(v₁ * cos θ' + v₂ * sin θ') - g * cos x|
        ≤ |v₁ * cos θ' + v₂ * sin θ'| + |g * cos x| := abs_sub _ _
      _ ≤ δ + δ := add_le_add h' hgc
      _ = 2 * δ := by ring
  have hxabs : |x| ≤ π / 2 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
  have hjordan := mul_abs_le_abs_sin hxabs
  have hg2 : g ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs g]
    exact pow_le_pow_left₀ (abs_nonneg g) h 2
  -- `q² ≥ 3d²/4`
  have hq2 : 3 / 4 * d ^ 2 ≤ |q| ^ 2 := by
    rw [sq_abs]
    nlinarith
  -- `|q| |x| ≤ π δ`
  have hpi := pi_pos
  have hqx : |q| * |x| ≤ π * δ := by
    have h1 : |q| * (2 / π * |x|) ≤ 2 * δ :=
      (mul_le_mul_of_nonneg_left hjordan (abs_nonneg q)).trans hqs
    have h2 : |q| * (2 / π * |x|) = 2 / π * (|q| * |x|) := by ring
    rw [h2] at h1
    have h3 : |q| * |x| = π / 2 * (2 / π * (|q| * |x|)) := by field_simp
    rw [h3]
    calc π / 2 * (2 / π * (|q| * |x|)) ≤ π / 2 * (2 * δ) := by gcongr
      _ = π * δ := by ring
  -- square and compare
  have hpi4 := pi_le_four
  have hsq : (d * |x|) ^ 2 ≤ (5 * δ) ^ 2 := by
    have hA : 0 ≤ |q| * |x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hB : (|q| * |x|) ^ 2 ≤ (π * δ) ^ 2 := pow_le_pow_left₀ hA hqx 2
    have hC : (π * δ) ^ 2 ≤ 16 * δ ^ 2 := by
      rw [mul_pow]
      have : π ^ 2 ≤ 16 := by nlinarith
      nlinarith [sq_nonneg δ]
    have hD : 3 / 4 * d ^ 2 * |x| ^ 2 ≤ |q| ^ 2 * |x| ^ 2 :=
      mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
    nlinarith [sq_nonneg (d * |x|), sq_nonneg δ]
  have hle : d * |x| ≤ 5 * δ :=
    (pow_le_pow_iff_left₀ (mul_nonneg hd.le (abs_nonneg _)) (by positivity) two_ne_zero).1 hsq
  rw [le_div_iff₀ hd]
  linarith

end Favard.LowerBound
