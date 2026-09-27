import FavardLength.Beyond.Exclusion.RelDeriv.Tangent
import FavardLength.Beyond.Exclusion.Analytic

/-!
# Complex displacement ratios for the cosine products and the box factor

For real `a` and complex `w`, the cosine addition formula with `|cos w| ≤ e^{|w|}` and
`|sin w| ≤ |w| e^{|w|}` gives

`|cos(a + w)| ≤ e^{|w|}(|cos a| + |sin a| |w|) ≤ |cos a| exp(|w|(1 + |tan a|))`

(`Exclusion.norm_cos_add_le_exp`). Multiplying over the factors of `A_n` gives the **complex
ratio bound** (Appendix G §2)

`|A_n(x + z)| ≤ |A_n(x)| exp(|z| tanSum n x)`

at every real `x` where no factor vanishes (`Exclusion.norm_cosProdC_add_le`); with a real
displacement it bounds `|A_n(x₀)|` by `|A_n(x)|` (`Exclusion.abs_cosProd_le_mul_exp`).

For the box factor `b_n(z)` of the product formula we prove `|b_n(z)| ≤ exp(8π/3 |Im z|)`
(`Exclusion.norm_boxFTC_le`), and at real frequencies `sinc θ ≥ 1/2` for `0 ≤ θ ≤ π/2`
(`Exclusion.half_le_sinc`).
-/

open Real

namespace Favard.Exclusion

/-! ### Elementary complex bounds -/

/-- `|cos w| ≤ e^{|w|}`. -/
lemma norm_cos_le_exp_norm (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have h := Complex.two_cos w
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ :=
    (Complex.norm_exp_le_exp_norm _).trans (by simp)
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ :=
    (Complex.norm_exp_le_exp_norm _).trans (by simp)
  have h3 : ‖2 * Complex.cos w‖ ≤ 2 * Real.exp ‖w‖ := by
    rw [h]
    exact (norm_add_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_two] at h3
  linarith

/-- `|sin w| ≤ |w| e^{|w|}`. -/
lemma norm_sin_le_mul_exp_norm (w : ℂ) : ‖Complex.sin w‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have h := Complex.two_sin w
  have e1 := Complex.norm_exp_sub_sum_le_norm_mul_exp (-w * Complex.I) 1
  have e2 := Complex.norm_exp_sub_sum_le_norm_mul_exp (w * Complex.I) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, norm_mul, norm_neg, Complex.norm_I, mul_one] at e1 e2
  have h3 : ‖2 * Complex.sin w‖ ≤ 2 * (‖w‖ * Real.exp ‖w‖) := by
    rw [h, norm_mul, Complex.norm_I, mul_one,
      show Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I) =
        (Complex.exp (-w * Complex.I) - 1) - (Complex.exp (w * Complex.I) - 1) by ring]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_two] at h3
  linarith

/-- `|cos(a + w)| ≤ e^{|w|}(|cos a| + |sin a| |w|)` for real `a`. -/
lemma norm_cos_add_le (a : ℝ) (w : ℂ) :
    ‖Complex.cos (a + w)‖ ≤ Real.exp ‖w‖ * (|Real.cos a| + |Real.sin a| * ‖w‖) := by
  rw [Complex.cos_add]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (norm_cos_le_exp_norm w) (abs_nonneg (Real.cos a))
  have h2 := mul_le_mul_of_nonneg_left (norm_sin_le_mul_exp_norm w) (abs_nonneg (Real.sin a))
  calc |Real.cos a| * ‖Complex.cos w‖ + |Real.sin a| * ‖Complex.sin w‖
      ≤ |Real.cos a| * Real.exp ‖w‖ + |Real.sin a| * (‖w‖ * Real.exp ‖w‖) := add_le_add h1 h2
    _ = Real.exp ‖w‖ * (|Real.cos a| + |Real.sin a| * ‖w‖) := by ring

/-- **One factor**: if `cos a ≠ 0`, then `|cos(a + w)| ≤ |cos a| exp(|w|(1 + |tan a|))`. -/
lemma norm_cos_add_le_exp (a : ℝ) (ha : Real.cos a ≠ 0) (w : ℂ) :
    ‖Complex.cos (a + w)‖ ≤ |Real.cos a| * Real.exp (‖w‖ * (1 + |Real.tan a|)) := by
  refine (norm_cos_add_le a w).trans ?_
  have hc : 0 < |Real.cos a| := abs_pos.mpr ha
  have hs : |Real.sin a| = |Real.cos a| * |Real.tan a| := by
    rw [Real.tan_eq_sin_div_cos, abs_div]
    field_simp
  have h1 : 1 + |Real.tan a| * ‖w‖ ≤ Real.exp (|Real.tan a| * ‖w‖) := by
    have := Real.add_one_le_exp (|Real.tan a| * ‖w‖)
    linarith
  rw [hs]
  calc Real.exp ‖w‖ * (|Real.cos a| + |Real.cos a| * |Real.tan a| * ‖w‖)
      = |Real.cos a| * Real.exp ‖w‖ * (1 + |Real.tan a| * ‖w‖) := by ring
    _ ≤ |Real.cos a| * Real.exp ‖w‖ * Real.exp (|Real.tan a| * ‖w‖) := by gcongr
    _ = |Real.cos a| * Real.exp (‖w‖ * (1 + |Real.tan a|)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-! ### The cosine products -/

/-- **Complex ratio bound for the cosine products** (Appendix G §2): if no factor of `A_n`
vanishes at the real point `x`, then `|A_n(x + z)| ≤ |A_n(x)| exp(|z| tanSum n x)`. -/
theorem norm_cosProdC_add_le (n : ℕ) (x : ℝ) (hx : ∀ j, Real.cos (π * x / 4 ^ (j + 1)) ≠ 0)
    (z : ℂ) : ‖cosProdC n (x + z)‖ ≤ |cosProd n x| * Real.exp (‖z‖ * tanSum n x) := by
  rw [cosProdC, Complex.norm_prod, cosProd, Finset.abs_prod, tanSum, Finset.mul_sum,
    Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have e : (π : ℂ) * (x + z) / 4 ^ (j + 1) =
      ((π * x / 4 ^ (j + 1) : ℝ) : ℂ) + π * z / 4 ^ (j + 1) := by
    push_cast
    ring
  have hn : ‖(π : ℂ) * z / 4 ^ (j + 1)‖ = π / 4 ^ (j + 1) * ‖z‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, norm_pow,
      Complex.norm_ofNat]
    ring
  rw [e]
  refine (norm_cos_add_le_exp _ (hx j) _).trans (le_of_eq ?_)
  rw [hn]
  ring_nf

/-- **Real ratio bound**: `|A_n(x₀)| ≤ |A_n(x)| exp(|x₀ - x| tanSum n x)` if no factor of `A_n`
vanishes at `x`. -/
theorem abs_cosProd_le_mul_exp (n : ℕ) (x x₀ : ℝ)
    (hx : ∀ j, Real.cos (π * x / 4 ^ (j + 1)) ≠ 0) :
    |cosProd n x₀| ≤ |cosProd n x| * Real.exp (|x₀ - x| * tanSum n x) := by
  have h := norm_cosProdC_add_le n x hx ((x₀ - x : ℝ) : ℂ)
  rwa [← Complex.ofReal_add, add_sub_cancel, cosProdC_ofReal, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h

/-! ### The box factor -/

/-- The box factor is bounded by `|b_n(z)| ≤ exp(8π/3 |Im z|)`. -/
lemma norm_boxFTC_le (n : ℕ) (z : ℂ) : ‖boxFTC n z‖ ≤ Real.exp (8 * π / 3 * |z.im|) := by
  set a : ℝ := 4 / 3 / 4 ^ n with ha_def
  have ha : 0 ≤ a := by positivity
  have ha1 : a ≤ 4 / 3 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have hbound : ∀ y ∈ Set.uIoc (-a) a,
      ‖Complex.exp (-2 * π * Complex.I * z * y)‖ ≤ Real.exp (2 * π * |z.im| * a) := by
    intro y hy
    rw [norm_exp_neg_two_pi_I_mul]
    apply Real.exp_le_exp.2
    have hy' : |y| ≤ a := by
      rw [Set.uIoc_of_le (by linarith)] at hy
      exact abs_le.2 ⟨hy.1.le, hy.2⟩
    calc 2 * π * z.im * y ≤ |2 * π * z.im * y| := le_abs_self _
      _ = 2 * π * |z.im| * |y| := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      _ ≤ 2 * π * |z.im| * a := by gcongr
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [boxFTC, norm_mul]
  have h38 : ‖(3 / 8 * 4 ^ n : ℂ)‖ = 3 / 8 * 4 ^ n := by
    rw [show (3 / 8 * 4 ^ n : ℂ) = ((3 / 8 * 4 ^ n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h38]
  have hlen : |a - -a| = 2 * a := by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]
  rw [hlen] at hint
  have h1 : 3 / 8 * 4 ^ n * (2 * a) = (1 : ℝ) := by rw [ha_def]; field_simp; norm_num
  calc 3 / 8 * 4 ^ n * ‖∫ y in -a..a, Complex.exp (-2 * π * Complex.I * z * y)‖
      ≤ 3 / 8 * 4 ^ n * (Real.exp (2 * π * |z.im| * a) * (2 * a)) := by gcongr
    _ = Real.exp (2 * π * |z.im| * a) := by rw [mul_comm (Real.exp _), ← mul_assoc, h1, one_mul]
    _ ≤ Real.exp (8 * π / 3 * |z.im|) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ 2 * π * |z.im| := by positivity
      nlinarith

/-- `sinc θ ≥ 1/2` for `0 ≤ θ ≤ π/2`. -/
lemma half_le_sinc {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : 1 / 2 ≤ Real.sinc θ := by
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · norm_num
  · rw [Real.sinc_of_ne_zero hpos.ne', le_div_iff₀ hpos]
    have hs := Real.mul_le_sin h0 h1
    have hπ : 1 / 2 ≤ 2 / π := by
      rw [le_div_iff₀ pi_pos]
      linarith [pi_le_four]
    nlinarith

end Favard.Exclusion
