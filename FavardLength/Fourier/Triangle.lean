import FavardLength.Statements
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The triangle (Fejér) identity

We prove `TriangleStatement`: for `ℓ > 0` the function `ξ ↦ sinc(ℓξ/2)²` is integrable and
the triangle function `g_ℓ(x) = (ℓ - |x|)_+` satisfies the no-`2π` Fourier inversion formula
`g_ℓ(x) = (2π)⁻¹ ∫ ℓ² sinc(ℓξ/2)² cos(ξx) dξ`.

1. *Cosine transform.* Since `g_ℓ` is even and supported on `[-ℓ, ℓ]`,
   `∫ g_ℓ(x) cos(ax) dx = 2 ∫_0^ℓ (ℓ - x) cos(ax) dx = 2(1 - cos(aℓ))/a² = ℓ² sinc(aℓ/2)²`
   (antiderivative `(ℓ - x) sin(ax)/a - cos(ax)/a²`), and `∫ g_ℓ(x) sin(ax) dx = 0` by oddness.
2. *Fourier transform.* Hence Mathlib's Fourier transform (with the `2π` in the phase) is
   `𝓕 g_ℓ(w) = ℓ² sinc(πℓw)²`, which is integrable because `sinc² z ≤ 2/(1 + z²)`.
3. *Inversion.* `MeasureTheory.Integrable.fourierInv_fourier_eq` gives
   `g_ℓ(x) = ∫ e^{2πiwx} ℓ² sinc(πℓw)² dw`; the substitution `w = ξ/(2π)` and taking real parts
   give the statement.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace Favard

namespace Triangle

/-- The triangle function `g_ℓ(x) = (ℓ - |x|)_+`. -/
noncomputable def tri (ℓ x : ℝ) : ℝ := max 0 (ℓ - |x|)

lemma continuous_tri (ℓ : ℝ) : Continuous (tri ℓ) := by
  unfold tri; fun_prop

lemma tri_neg (ℓ x : ℝ) : tri ℓ (-x) = tri ℓ x := by
  simp [tri, abs_neg]

lemma tri_eq_zero_of_notMem {ℓ x : ℝ} (hx : x ∉ Icc (-ℓ) ℓ) : tri ℓ x = 0 := by
  have : ℓ ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl hx.le)
  simp [tri, this]

lemma tri_of_mem_Icc {ℓ x : ℝ} (hx : x ∈ Icc 0 ℓ) : tri ℓ x = ℓ - x := by
  rw [tri, abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]

lemma hasCompactSupport_tri (ℓ : ℝ) : HasCompactSupport (tri ℓ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => tri_eq_zero_of_notMem hx

/-- `sinc z · z = sin z` for every real `z`. -/
lemma sinc_mul_self (z : ℝ) : sinc z * z = sin z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [sinc_of_ne_zero hz, div_mul_cancel₀ _ hz]

/-- The decay bound `sinc² z ≤ 2 (1 + z²)⁻¹`. -/
lemma sinc_sq_le (z : ℝ) : sinc z ^ 2 ≤ 2 * (1 + z ^ 2)⁻¹ := by
  have h1 : sinc z ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact abs_sinc_le_one z
  have h2 : sinc z ^ 2 * z ^ 2 ≤ 1 := by
    rw [← mul_pow, sinc_mul_self]; exact sin_sq_le_one z
  have hpos : 0 < 1 + z ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

/-- `ξ ↦ sinc(cξ)²` is integrable for `c ≠ 0`. -/
lemma integrable_sinc_sq {c : ℝ} (hc : c ≠ 0) : Integrable fun ξ : ℝ => sinc (c * ξ) ^ 2 := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 2).comp_mul_left' hc)
    ((continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sinc_sq_le _

/-- `∫_0^ℓ (ℓ - x) cos(ax) dx = (ℓ²/2) sinc(ℓa/2)²`. -/
lemma integral_sub_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) :
    ∫ x in (0 : ℝ)..ℓ, (ℓ - x) * cos (a * x) = ℓ ^ 2 / 2 * sinc (ℓ / 2 * a) ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, cos_zero, mul_one, mul_zero, sinc_zero, one_pow]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    simp [integral_id]
    ring
  · have hderiv : ∀ x ∈ uIcc 0 ℓ, HasDerivAt
        (fun x => (ℓ - x) * sin (a * x) / a - cos (a * x) / a ^ 2) ((ℓ - x) * cos (a * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun x => a * x) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      have := ((((hasDerivAt_id x).const_sub ℓ).mul h1.sin).div_const a).sub
        (h1.cos.div_const (a ^ 2))
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
      apply Continuous.intervalIntegrable; fun_prop)]
    have hla : ℓ / 2 * a ≠ 0 := by positivity
    rw [sinc_of_ne_zero hla]
    have hc : cos (a * ℓ) = 1 - 2 * sin (ℓ / 2 * a) ^ 2 := by
      rw [show a * ℓ = 2 * (ℓ / 2 * a) by ring, cos_two_mul, cos_sq']; ring
    simp only [sub_self, zero_mul, zero_div, mul_zero, sin_zero, cos_zero, sub_zero, zero_sub, hc]
    field_simp
    ring

/-- The triangle function times a continuous function is integrable. -/
lemma integrable_tri_mul (ℓ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable fun x => tri ℓ x * g x :=
  ((continuous_tri ℓ).mul hg).integrable_of_hasCompactSupport (hasCompactSupport_tri ℓ).mul_right

/-- **Cosine transform of the triangle function**: `∫ g_ℓ(x) cos(ax) dx = ℓ² sinc(ℓa/2)²`. -/
lemma integral_tri_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) :
    ∫ x, tri ℓ x * cos (a * x) = ℓ ^ 2 * sinc (ℓ / 2 * a) ^ 2 := by
  have hsupp : ∀ x ∉ Icc (-ℓ) ℓ, tri ℓ x * cos (a * x) = 0 := fun x hx => by
    rw [tri_eq_zero_of_notMem hx, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hint : ∀ b c : ℝ, IntervalIntegrable (fun x => tri ℓ x * cos (a * x)) volume b c :=
    fun b c => ((continuous_tri ℓ).mul (by fun_prop)).intervalIntegrable b c
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-ℓ) 0) (hint 0 ℓ)]
  have hneg : ∫ x in (-ℓ)..0, tri ℓ x * cos (a * x) = ∫ x in (0 : ℝ)..ℓ, tri ℓ x * cos (a * x) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := ℓ) fun x => tri ℓ x * cos (a * x)
    simp only [neg_zero, tri_neg, mul_neg, cos_neg] at this
    exact this.symm
  have hpos : ∫ x in (0 : ℝ)..ℓ, tri ℓ x * cos (a * x) = ∫ x in (0 : ℝ)..ℓ, (ℓ - x) * cos (a * x) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le hℓ.le] at hx
      simp only [tri_of_mem_Icc hx]
  rw [hneg, hpos, integral_sub_mul_cos hℓ]
  ring

/-- The sine transform of the (even) triangle function vanishes. -/
lemma integral_tri_mul_sin (ℓ a : ℝ) : ∫ x, tri ℓ x * sin (a * x) = 0 := by
  have h := integral_neg_eq_self (fun x => tri ℓ x * sin (a * x)) volume
  simp only [tri_neg, mul_neg, sin_neg, integral_neg] at h
  linarith

/-- **Fourier transform of the triangle function** (Mathlib normalization, phase `e^{-2πixw}`):
`𝓕 g_ℓ(w) = ℓ² sinc(πℓw)²`. -/
lemma fourier_tri {ℓ : ℝ} (hℓ : 0 < ℓ) (w : ℝ) :
    𝓕 (fun x => (tri ℓ x : ℂ)) w = ((ℓ ^ 2 * sinc (ℓ / 2 * (2 * π * w)) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • (tri ℓ v : ℂ) =
      ((tri ℓ v * cos (2 * π * w * v) : ℝ) : ℂ) -
        ((tri ℓ v * sin (2 * π * w * v) : ℝ) : ℂ) * Complex.I := by
    intro v
    rw [Complex.exp_mul_I, smul_eq_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * v * w = -(2 * π * w * v) by ring, cos_neg, sin_neg]
    push_cast
    ring
  simp_rw [h]
  rw [integral_sub, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_tri_mul_cos hℓ, integral_tri_mul_sin]
  · simp
  · exact (integrable_tri_mul ℓ (by fun_prop)).ofReal
  · exact (integrable_tri_mul ℓ (by fun_prop)).ofReal.mul_const _

/-- **Triangle identity**: the no-`2π` Fourier inversion formula for the triangle function. -/
theorem _root_.Favard.triangle : TriangleStatement := by
  intro ℓ hℓ
  have hc : ℓ / 2 ≠ 0 := by positivity
  refine ⟨integrable_sinc_sq hc, fun x => ?_⟩
  set f : ℝ → ℂ := fun x => (tri ℓ x : ℂ) with hf_def
  have hcont : Continuous f := Complex.continuous_ofReal.comp (continuous_tri ℓ)
  have hf : Integrable f := by
    simpa using (integrable_tri_mul ℓ (g := fun _ => 1) continuous_const).ofReal (𝕜 := ℂ)
  have hFf : 𝓕 f = fun w => ((ℓ ^ 2 * sinc (ℓ / 2 * (2 * π * w)) ^ 2 : ℝ) : ℂ) :=
    funext (fourier_tri hℓ)
  have hFint : Integrable (𝓕 f) := by
    have := (integrable_sinc_sq (c := ℓ / 2 * (2 * π)) (by positivity)).const_mul (ℓ ^ 2)
    have hreal : Integrable fun w : ℝ => ℓ ^ 2 * sinc (ℓ / 2 * (2 * π * w)) ^ 2 :=
      this.congr (Filter.Eventually.of_forall fun w => by simp only [mul_assoc (ℓ / 2)])
    rw [hFf]
    exact hreal.ofReal
  have key := hf.fourierInv_fourier_eq hFint hcont.continuousAt (v := x)
  rw [fourierInv_eq', hFf] at key
  set G : ℝ → ℂ := fun ξ =>
    Complex.exp (↑(ξ * x) * Complex.I) * ((ℓ ^ 2 * sinc (ℓ / 2 * ξ) ^ 2 : ℝ) : ℂ) with hG
  have hGint : Integrable G := by
    refine Integrable.mono' ((integrable_sinc_sq hc).const_mul (ℓ ^ 2)) (by fun_prop)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hG, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcv : ∫ w : ℝ, Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) •
      ((ℓ ^ 2 * sinc (ℓ / 2 * (2 * π * w)) ^ 2 : ℝ) : ℂ) = (2 * π)⁻¹ • ∫ ξ, G ξ := by
    have := Measure.integral_comp_mul_left G (2 * π)
    rw [abs_of_pos (by positivity)] at this
    rw [← this]
    congr 1
    ext w
    simp only [hG, smul_eq_mul, Real.inner_apply]
    ring_nf
  rw [hcv] at key
  have hre := congrArg Complex.re key
  rw [Complex.real_smul, Complex.re_ofReal_mul, ← RCLike.re_to_complex, ← integral_re hGint]
    at hre
  simp only [hf_def, Complex.ofReal_re] at hre
  rw [tri] at hre
  rw [← hre]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [hG, RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  ring

end Triangle

end Favard
