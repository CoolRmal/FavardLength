import FavardLength.Beyond.Exclusion.Density
import FavardLength.Fourier.Annular.Expansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Fourier transform of the tail density and the cosine products

We prove the product formula for the entire extension of the transform of `f_{n,t}`,

`Ψ_{n,t}(z) = A_n(4(1-t)z) A_n(4(1+t)z) b_n(z)`, `b_n(z) = (ρ4^{-n})⁻¹ ∫_{|y| ≤ ρ4^{-n}/2}
e^{-2πizy} dy`,

(`Exclusion.tailFTC_eq`), and its real specialization
`ψ_{n,t}(ξ) = ν̂_{n,t}(2πξ) sinc(πρ4^{-n}ξ) = A_n(4(1-t)ξ) A_n(4(1+t)ξ) sinc(πρ4^{-n}ξ)`
(Appendix G (1)): `tailMoment n t 0 ξ = ψ_{n,t}(ξ)` and `𝓕 f_{n,t} = ψ_{n,t}`.

We also record the elementary properties of the cosine products `A_n` and of the infinite
product modulus `|A| = inf_n |A_n|`.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace Favard.Exclusion

open Bridge

/-! ### The complex digit sum -/

/-- The four normalized digits average `e^{-2πizd/4^j}` to
`cos(π(1-t)z/4^j) cos(π(1+t)z/4^j)`. -/
lemma sum_exp_digit_complex (t : ℝ) (z : ℂ) (j : ℕ) :
    ∑ p : Bool × Bool, Complex.exp (-2 * π * Complex.I * z * ((digit t p / 4 ^ j : ℝ) : ℂ)) =
      4 * (Complex.cos (π * (4 * (1 - t) * z) / 4 ^ (j + 1)) *
        Complex.cos (π * (4 * (1 + t) * z) / 4 ^ (j + 1))) := by
  have h4 : (4 : ℂ) ^ (j + 1) = 4 * 4 ^ j := by ring
  have hA : π * (4 * (1 - t) * z) / 4 ^ (j + 1) = π * (1 - t) * z / 4 ^ j := by
    rw [h4]; ring
  have hB : π * (4 * (1 + t) * z) / 4 ^ (j + 1) = π * (1 + t) * z / 4 ^ j := by
    rw [h4]; ring
  rw [hA, hB]
  have hcc : Complex.cos (2 * π * z / 4 ^ j) + Complex.cos (2 * π * t * z / 4 ^ j) =
      2 * Complex.cos (π * (1 + t) * z / 4 ^ j) * Complex.cos (π * (1 - t) * z / 4 ^ j) := by
    have e1 : (2 * π * z / 4 ^ j + 2 * π * t * z / 4 ^ j) / 2 = π * (1 + t) * z / 4 ^ j := by
      ring
    have e2 : (2 * π * z / 4 ^ j - 2 * π * t * z / 4 ^ j) / 2 = π * (1 - t) * z / 4 ^ j := by
      ring
    rw [Complex.cos_add_cos, e1, e2]
  have hprod : 4 * (Complex.cos (π * (1 - t) * z / 4 ^ j) *
      Complex.cos (π * (1 + t) * z / 4 ^ j)) =
      2 * Complex.cos (2 * π * z / 4 ^ j) + 2 * Complex.cos (2 * π * t * z / 4 ^ j) := by
    linear_combination (-2 : ℂ) * hcc
  rw [hprod, Complex.two_cos, Complex.two_cos]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, digit]
  push_cast
  have f1 : -2 * π * Complex.I * z * (1 / 4 ^ j) = -(2 * π * z / 4 ^ j) * Complex.I := by ring
  have f2 : -2 * π * Complex.I * z * (t / 4 ^ j) = -(2 * π * t * z / 4 ^ j) * Complex.I := by
    ring
  have f3 : -2 * π * Complex.I * z * (-t / 4 ^ j) = (2 * π * t * z / 4 ^ j) * Complex.I := by
    ring
  have f4 : -2 * π * Complex.I * z * (-1 / 4 ^ j) = (2 * π * z / 4 ^ j) * Complex.I := by ring
  rw [f1, f2, f3, f4]
  ring

/-- **Code expansion at complex frequency**:
`∑_w e^{-2πiz c_w(t)} = 4^n A_n(4(1-t)z) A_n(4(1+t)z)`. -/
lemma sum_exp_code_complex (n : ℕ) (t : ℝ) (z : ℂ) :
    ∑ w : SqCode n, Complex.exp (-2 * π * Complex.I * z * (code t w : ℂ)) =
      4 ^ n * (cosProdC n (4 * (1 - t) * z) * cosProdC n (4 * (1 + t) * z)) := by
  have h : ∀ w : SqCode n, Complex.exp (-2 * π * Complex.I * z * (code t w : ℂ)) =
      ∏ j : Fin n, Complex.exp (-2 * π * Complex.I * z *
        ((digit t (w j) / 4 ^ (j : ℕ) : ℝ) : ℂ)) := by
    intro w
    rw [← Complex.exp_sum, code, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [h]
  rw [← Fintype.prod_sum fun (j : Fin n) (p : Bool × Bool) =>
    Complex.exp (-2 * π * Complex.I * z * ((digit t p / 4 ^ (j : ℕ) : ℝ) : ℂ))]
  simp_rw [sum_exp_digit_complex]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    cosProdC, cosProdC, ← Finset.prod_mul_distrib,
    Finset.prod_range fun j => Complex.cos (π * (4 * (1 - t) * z) / 4 ^ (j + 1)) *
      Complex.cos (π * (4 * (1 + t) * z) / 4 ^ (j + 1))]

/-! ### The product formula -/

/-- The complex exponential times the indicator of a box is the indicator of the exponential. -/
lemma exp_mul_indicator_box (n : ℕ) (z : ℂ) (c x : ℝ) :
    Complex.exp (-2 * π * Complex.I * z * x) *
        (((Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)).indicator 1 x : ℝ) : ℂ) =
      (Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)).indicator
        (fun x : ℝ => Complex.exp (-2 * π * Complex.I * z * x)) x := by
  by_cases hx : x ∈ Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n) <;> simp [hx]

lemma integrable_exp_mul_indicator_box (n : ℕ) (z : ℂ) (c : ℝ) :
    Integrable fun x : ℝ => Complex.exp (-2 * π * Complex.I * z * x) *
        (((Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)).indicator 1 x : ℝ) : ℂ) := by
  simp_rw [exp_mul_indicator_box]
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

/-- One box: `∫ e^{-2πizx} 1_{[c - a, c + a]}(x) dx = e^{-2πizc} ∫_{-a}^{a} e^{-2πizy} dy`. -/
lemma integral_exp_mul_indicator_box (n : ℕ) (z : ℂ) (c : ℝ) :
    ∫ x : ℝ, Complex.exp (-2 * π * Complex.I * z * x) *
        (((Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)).indicator 1 x : ℝ) : ℂ) =
      Complex.exp (-2 * π * Complex.I * z * c) *
        ∫ y in (-(4 / 3 / 4 ^ n : ℝ))..(4 / 3 / 4 ^ n),
          Complex.exp (-2 * π * Complex.I * z * y) := by
  have ha : (0 : ℝ) ≤ 4 / 3 / 4 ^ n := by positivity
  simp_rw [exp_mul_indicator_box]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    show c - 4 / 3 / 4 ^ n = -(4 / 3 / 4 ^ n) + c by ring,
    show c + 4 / 3 / 4 ^ n = 4 / 3 / 4 ^ n + c by ring,
    ← intervalIntegral.integral_comp_add_right, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Product formula** for the entire extension of the transform:
`Ψ_{n,t}(z) = A_n(4(1-t)z) A_n(4(1+t)z) b_n(z)`. -/
theorem tailFTC_eq (n : ℕ) (t : ℝ) (z : ℂ) :
    tailFTC n t z = cosProdC n (4 * (1 - t) * z) * cosProdC n (4 * (1 + t) * z) * boxFTC n z := by
  have h1 : ∀ x : ℝ, Complex.exp (-2 * π * Complex.I * z * x) * (tailDensity n t x : ℂ) =
      3 / 8 * ∑ w : SqCode n, Complex.exp (-2 * π * Complex.I * z * x) *
        (((Icc (code t w - 4 / 3 / 4 ^ n) (code t w + 4 / 3 / 4 ^ n)).indicator 1 x : ℝ) : ℂ) := by
    intro x
    rw [tailDensity, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    ring
  rw [tailFTC]
  simp_rw [h1]
  rw [integral_const_mul, integral_finsetSum _ fun w _ => integrable_exp_mul_indicator_box n z _]
  simp_rw [integral_exp_mul_indicator_box]
  rw [← Finset.sum_mul, sum_exp_code_complex, boxFTC]
  ring

/-- The box transform at a real frequency is `sinc(πρ4^{-n}ξ)`. -/
lemma boxFTC_ofReal (n : ℕ) (ξ : ℝ) :
    boxFTC n ξ = (sinc (8 / 3 * π / 4 ^ n * ξ) : ℂ) := by
  rw [boxFTC]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul, mul_one, sinc_zero, Complex.ofReal_one]
    push_cast
    field_simp
    ring
  · have hc : -2 * π * Complex.I * (ξ : ℂ) ≠ 0 := by
      have : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
      simp [hπ, this, Complex.I_ne_zero]
    have hθ : 8 / 3 * π / 4 ^ n * ξ ≠ 0 := by
      have : (0 : ℝ) < 8 / 3 * π / 4 ^ n := by positivity
      exact mul_ne_zero this.ne' hξ
    rw [integral_exp_mul_complex hc, sinc_of_ne_zero hθ]
    set θ : ℝ := 8 / 3 * π / 4 ^ n * ξ with hθdef
    have e1 : -2 * (π : ℂ) * Complex.I * ξ * ((4 / 3 / 4 ^ n : ℝ) : ℂ) =
        -(θ : ℂ) * Complex.I := by rw [hθdef]; push_cast; ring
    have e2 : -2 * (π : ℂ) * Complex.I * ξ * ((-(4 / 3 / 4 ^ n) : ℝ) : ℂ) =
        (θ : ℂ) * Complex.I := by rw [hθdef]; push_cast; ring
    rw [e1, e2]
    have hs := Complex.two_sin (θ : ℂ)
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hs' : Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I) =
        -2 * Complex.I * Complex.sin θ := by
      linear_combination Complex.I * hs +
        (Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) * hI
    rw [hs']
    have hθc : (θ : ℂ) = 8 / 3 * π / 4 ^ n * ξ := by rw [hθdef]; push_cast; ring
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
    push_cast
    rw [hθc]
    field_simp

/-! ### Real frequencies -/

lemma cosProdC_ofReal (n : ℕ) (x : ℝ) : cosProdC n (x : ℂ) = (cosProd n x : ℂ) := by
  unfold cosProdC cosProd
  push_cast
  rfl

/-- `ν̂_{n,t}(2πξ) = A_n(4(1-t)ξ) A_n(4(1+t)ξ)`. -/
lemma nuHat_two_pi_mul (n : ℕ) (t ξ : ℝ) :
    nuHat n t (2 * π * ξ) = cosProd n (4 * (1 - t) * ξ) * cosProd n (4 * (1 + t) * ξ) := by
  unfold nuHat cosProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold phi
  rw [cos_add_cos, pow_succ]
  have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
  have e1 : (2 * π * ξ / 4 ^ j + t * (2 * π * ξ / 4 ^ j)) / 2 =
      π * (4 * (1 + t) * ξ) / (4 ^ j * 4) := by field_simp
  have e2 : (2 * π * ξ / 4 ^ j - t * (2 * π * ξ / 4 ^ j)) / 2 =
      π * (4 * (1 - t) * ξ) / (4 ^ j * 4) := by field_simp
  rw [e1, e2]
  ring

/-- `ψ_{n,t}(ξ) = A_n(4(1-t)ξ) A_n(4(1+t)ξ) sinc(πρ4^{-n}ξ)` (Appendix G (1)). -/
lemma tailFT_eq (n : ℕ) (t ξ : ℝ) :
    tailFT n t ξ = cosProd n (4 * (1 - t) * ξ) * cosProd n (4 * (1 + t) * ξ) *
      sinc (8 / 3 * π / 4 ^ n * ξ) := by
  rw [tailFT, nuHat_two_pi_mul]

/-- The entire extension restricts to `ψ_{n,t}` on the real line. -/
lemma tailFTC_ofReal (n : ℕ) (t ξ : ℝ) : tailFTC n t ξ = (tailFT n t ξ : ℂ) := by
  rw [tailFTC_eq, boxFTC_ofReal, tailFT_eq,
    show (4 : ℂ) * (1 - (t : ℂ)) * (ξ : ℂ) = ((4 * (1 - t) * ξ : ℝ) : ℂ) by push_cast; ring,
    show (4 : ℂ) * (1 + (t : ℂ)) * (ξ : ℂ) = ((4 * (1 + t) * ξ : ℝ) : ℂ) by push_cast; ring,
    cosProdC_ofReal, cosProdC_ofReal]
  push_cast
  ring

/-- The zeroth moment is the transform: `M_0(ξ) = ψ_{n,t}(ξ)`. -/
theorem tailMoment_zero (n : ℕ) (t ξ : ℝ) : tailMoment n t 0 ξ = (tailFT n t ξ : ℂ) := by
  rw [← tailFTC_ofReal, tailMoment, tailFTC]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [pow_zero, one_mul]
  congr 2
  push_cast
  ring

/-- `tailMoment` is `tailFTC` at a real point for `j = 0`, and in general
`M_j(ξ) = ∫ x^j e^{-2πiξx} f_{n,t}(x) dx` in the exponent convention of `tailFTC`. -/
lemma tailMoment_eq (n : ℕ) (t : ℝ) (j : ℕ) (ξ : ℝ) :
    tailMoment n t j ξ =
      ∫ x : ℝ, (x : ℂ) ^ j * (Complex.exp (-2 * π * Complex.I * ξ * x) * tailDensity n t x) := by
  rw [tailMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc]
  congr 3
  push_cast
  ring

/-- **The Fourier transform of the tail density** (Mathlib's convention
`𝓕 f (ξ) = ∫ e^{-2πixξ} f(x) dx`) is `ψ_{n,t}`. -/
theorem fourier_tailDensity (n : ℕ) (t ξ : ℝ) :
    𝓕 (fun x => (tailDensity n t x : ℂ)) ξ = (tailFT n t ξ : ℂ) := by
  rw [← tailMoment_zero, tailMoment, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, pow_zero, one_mul]
  congr 2
  push_cast
  ring

lemma abs_tailFT_le_one (n : ℕ) (t ξ : ℝ) : |tailFT n t ξ| ≤ 1 := by
  rw [tailFT, abs_mul]
  calc |nuHat n t (2 * π * ξ)| * |sinc (8 / 3 * π / 4 ^ n * ξ)|
      ≤ 1 * 1 := mul_le_mul (Annular.abs_nuHat_le_one _ _ _) (abs_sinc_le_one _)
        (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ### Cosine products -/

lemma cosProd_zero (x : ℝ) : cosProd 0 x = 1 := by simp [cosProd]

lemma cosProd_succ (n : ℕ) (x : ℝ) :
    cosProd (n + 1) x = cosProd n x * Real.cos (π * x / 4 ^ (n + 1)) := by
  rw [cosProd, Finset.prod_range_succ, ← cosProd]

lemma abs_cosProd_le_one (n : ℕ) (x : ℝ) : |cosProd n x| ≤ 1 := by
  rw [cosProd, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_cos_le_one _

lemma abs_cosProd_succ_le (n : ℕ) (x : ℝ) : |cosProd (n + 1) x| ≤ |cosProd n x| := by
  rw [cosProd_succ, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-- `|A_n(x)|` is nonincreasing in `n`. -/
lemma antitone_abs_cosProd (x : ℝ) : Antitone fun n => |cosProd n x| :=
  antitone_nat_of_succ_le fun n => abs_cosProd_succ_le n x

lemma absCosProd_nonneg (x : ℝ) : 0 ≤ absCosProd x :=
  le_ciInf fun _ => abs_nonneg _

lemma bddBelow_abs_cosProd (x : ℝ) : BddBelow (Set.range fun n => |cosProd n x|) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact abs_nonneg _⟩

/-- `|A(x)| ≤ |A_n(x)|` for every `n`. -/
lemma absCosProd_le (n : ℕ) (x : ℝ) : absCosProd x ≤ |cosProd n x| :=
  ciInf_le (bddBelow_abs_cosProd x) n

lemma absCosProd_le_one (x : ℝ) : absCosProd x ≤ 1 :=
  (absCosProd_le 0 x).trans (by simp [cosProd_zero])

/-- `|A_n(x)| → |A(x)|`. -/
lemma tendsto_abs_cosProd (x : ℝ) :
    Filter.Tendsto (fun n => |cosProd n x|) Filter.atTop (nhds (absCosProd x)) :=
  tendsto_atTop_ciInf (antitone_abs_cosProd x) (bddBelow_abs_cosProd x)

end Favard.Exclusion
