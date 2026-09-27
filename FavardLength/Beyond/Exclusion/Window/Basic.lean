import FavardLength.Beyond.Exclusion.Cutoff
import FavardLength.Beyond.Exclusion.Density

/-!
# The smooth window transform

For a sum of tail copies `g = ∑_i f_{n,t}(· - β_i)` and a window length `T > 0`, the windowed
transform of Appendix G §4 is `I(ξ) = ∫ χ(x/T) e^{-2πiξx} g(x) dx`. We record the basic
properties of the modulated cutoff `φ(x) = χ(x/T) e^{-2πiξx}`: continuity, `‖φ‖ ≤ 1`, support
in `[T/4, 3T/4]`, the Lipschitz bound `‖φ(x) - φ(y)‖ ≤ (C/T + 2πξ)|x - y|`, and
`∫ φ = T χ̂(Tξ)` with Mathlib's normalization of the Fourier transform.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace Favard.Exclusion

/-- The modulated cutoff `φ(x) = χ(x/T) e^{-2πiξx}`. -/
noncomputable def windowTest (T ξ x : ℝ) : ℂ :=
  (cutoff (x / T) : ℂ) * Complex.exp (↑(-2 * π * ξ * x) * Complex.I)

/-- The windowed transform `I(ξ) = ∫ χ(x/T) e^{-2πiξx} g(x) dx` of the sum of copies
`g = ∑_i f_{n,t}(· - β_i)` (Appendix G §4). -/
noncomputable def windowTransform (n : ℕ) (t T ξ : ℝ) {m : ℕ} (β : Fin m → ℝ) : ℂ :=
  ∫ x, windowTest T ξ x * (copySum n t β x : ℂ)

lemma continuous_windowTest (T ξ : ℝ) : Continuous (windowTest T ξ) := by
  have := continuous_cutoff
  unfold windowTest
  fun_prop

lemma norm_windowTest_le_one (T ξ x : ℝ) : ‖windowTest T ξ x‖ ≤ 1 := by
  rw [windowTest, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _)]
  exact cutoff_le_one _

/-- The modulated cutoff vanishes outside `(T/4, 3T/4)`. -/
lemma windowTest_eq_zero {T ξ x : ℝ} (hT : 0 < T) (hx : x ∉ Ioo (T / 4) (3 * T / 4)) :
    windowTest T ξ x = 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
  have h : cutoff (x / T) = 0 := by
    rcases hx with hx | hx
    · exact cutoff_eq_zero_of_le (by rw [div_le_iff₀ hT]; linarith)
    · exact cutoff_eq_zero_of_ge (by rw [le_div_iff₀ hT]; linarith)
  rw [windowTest, h, Complex.ofReal_zero, zero_mul]

/-- The phase `e^{-2πiξx}` is `2π|ξ|`-Lipschitz. -/
lemma norm_exp_sub_exp_le (ξ x y : ℝ) :
    ‖Complex.exp (↑(-2 * π * ξ * x) * Complex.I) - Complex.exp (↑(-2 * π * ξ * y) * Complex.I)‖
      ≤ 2 * π * |ξ| * |x - y| := by
  have h : Complex.exp (↑(-2 * π * ξ * x) * Complex.I) =
      Complex.exp (↑(-2 * π * ξ * y) * Complex.I) *
        Complex.exp (Complex.I * ↑(-2 * π * ξ * (x - y))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h, show ∀ a b : ℂ, a * b - a = a * (b - 1) from fun a b => by ring, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos pi_pos]

/-- The cutoff is Lipschitz. -/
lemma exists_abs_cutoff_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |cutoff u - cutoff v| ≤ C * |u - v| := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_iteratedDeriv_cutoff 1
  refine ⟨C, hC, fun u v => ?_⟩
  have hd : ∀ x ∈ (univ : Set ℝ), DifferentiableAt ℝ cutoff x := fun x _ =>
    (contDiff_cutoff (n := 1)).differentiable one_ne_zero x
  have hb : ∀ x ∈ (univ : Set ℝ), ‖deriv cutoff x‖ ≤ C := fun x _ => by
    rw [← iteratedDeriv_one, Real.norm_eq_abs]
    exact hbd 1 le_rfl x
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ v) (mem_univ u)
  simpa only [Real.norm_eq_abs] using this

/-- **Lipschitz bound for the modulated cutoff**: `‖φ(x) - φ(y)‖ ≤ (C/T + 2πξ)|x - y|`. -/
lemma exists_norm_windowTest_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T ξ x y : ℝ, 0 < T → 0 ≤ ξ →
      ‖windowTest T ξ x - windowTest T ξ y‖ ≤ (C / T + 2 * π * ξ) * |x - y| := by
  obtain ⟨C, hC, hlip⟩ := exists_abs_cutoff_sub_le
  refine ⟨C, hC, fun T ξ x y hT hξ => ?_⟩
  set ex := Complex.exp (↑(-2 * π * ξ * x) * Complex.I)
  set ey := Complex.exp (↑(-2 * π * ξ * y) * Complex.I)
  have hsplit : windowTest T ξ x - windowTest T ξ y =
      ((cutoff (x / T) - cutoff (y / T) : ℝ) : ℂ) * ex + (cutoff (y / T) : ℂ) * (ex - ey) := by
    simp only [windowTest, ex, ey]
    push_cast
    ring
  have h1 : ‖((cutoff (x / T) - cutoff (y / T) : ℝ) : ℂ) * ex‖ ≤ C / T * |x - y| := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    refine (hlip _ _).trans (le_of_eq ?_)
    rw [← sub_div, abs_div, abs_of_pos hT]
    ring
  have h2 : ‖(cutoff (y / T) : ℂ) * (ex - ey)‖ ≤ 2 * π * ξ * |x - y| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _)]
    calc cutoff (y / T) * ‖ex - ey‖ ≤ 1 * (2 * π * |ξ| * |x - y|) :=
          mul_le_mul (cutoff_le_one _) (norm_exp_sub_exp_le ξ x y) (norm_nonneg _) zero_le_one
      _ = 2 * π * ξ * |x - y| := by rw [abs_of_nonneg hξ, one_mul]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **The constant mode**: `∫ χ(x/T) e^{-2πiξx} dx = T χ̂(Tξ)`. -/
lemma integral_windowTest {T : ℝ} (hT : 0 < T) (ξ : ℝ) :
    ∫ x, windowTest T ξ x = (T : ℂ) * 𝓕 (fun u => (cutoff u : ℂ)) (T * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_div
    (fun u : ℝ => Complex.exp (↑(-2 * π * u * (T * ξ)) * Complex.I) • (cutoff u : ℂ)) T
  rw [abs_of_pos hT, Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [windowTest, smul_eq_mul]
  rw [mul_comm]
  congr 3
  field_simp

end Favard.Exclusion
