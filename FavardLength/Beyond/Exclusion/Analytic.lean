import FavardLength.Beyond.Exclusion.Transform
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The transform of the tail density is entire; derivatives are moments

For `|t| ≤ 1` the tail density is bounded with support in `[-ρ/2, ρ/2]`, so its transform
`Ψ_{n,t}(z) = ∫ e^{-2πizx} f_{n,t}(x) dx` is an entire function of `z ∈ ℂ` whose derivatives are
obtained by differentiating under the integral sign:

`Ψ^{(j)}(z) = ∫ (-2πix)^j e^{-2πizx} f_{n,t}(x) dx`, and at real `ξ`,
`Ψ^{(j)}(ξ) = (-2πi)^j M_j(ξ)` (`Exclusion.iteratedDeriv_tailFTC_ofReal`).

Together with the product formula `Exclusion.tailFTC_eq`, this is the input for Cauchy's
estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) in the
relative-derivative bound of Appendix G §2.
-/

open MeasureTheory Set Real Metric

namespace Favard.Exclusion

/-- The integrals `Ψ_j(z) = ∫ (-2πix)^j e^{-2πizx} f_{n,t}(x) dx`, so that `Ψ_0 = Ψ` and
`Ψ_j = Ψ^{(j)}` (`Exclusion.iteratedDeriv_tailFTC`). -/
noncomputable def tailFTCIter (n : ℕ) (t : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (-2 * π * Complex.I * x) ^ j * Complex.exp (-2 * π * Complex.I * z * x) *
    tailDensity n t x

lemma tailFTCIter_zero (n : ℕ) (t : ℝ) : tailFTCIter n t 0 = tailFTC n t := by
  funext z
  simp [tailFTCIter, tailFTC]

/-- `‖e^{-2πizx}‖ = e^{2π Im(z) x}`. -/
lemma norm_exp_neg_two_pi_I_mul (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-2 * π * Complex.I * z * x)‖ = Real.exp (2 * π * z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma hasDerivAt_tailFTCIter_integrand (j : ℕ) (x : ℝ) (c : ℂ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (-2 * π * Complex.I * x) ^ j *
        Complex.exp (-2 * π * Complex.I * w * x) * c)
      ((-2 * π * Complex.I * x) ^ (j + 1) * Complex.exp (-2 * π * Complex.I * w * x) * c) w := by
  have h1 : HasDerivAt (fun w : ℂ => -2 * π * Complex.I * w * x) (-2 * π * Complex.I * 1 * x) w :=
    ((hasDerivAt_id w).const_mul (-2 * π * Complex.I)).mul_const (x : ℂ)
  have h2 := ((h1.cexp).const_mul ((-2 * π * Complex.I * x) ^ j)).mul_const c
  convert h2 using 1
  ring

/-- **Differentiation under the integral sign**: `Ψ_j' = Ψ_{j+1}`. -/
theorem hasDerivAt_tailFTCIter {t : ℝ} (ht : |t| ≤ 1) (n j : ℕ) (z : ℂ) :
    HasDerivAt (tailFTCIter n t j) (tailFTCIter n t (j + 1) z) z := by
  set C : ℝ := (2 * π * (4 / 3)) ^ (j + 1) * Real.exp (2 * π * (|z.im| + 1) * (4 / 3)) with hC
  have hmeas : ∀ (i : ℕ) (w : ℂ), AEStronglyMeasurable (fun x : ℝ =>
      (-2 * π * Complex.I * x) ^ i * Complex.exp (-2 * π * Complex.I * w * x) *
        (tailDensity n t x : ℂ)) volume := fun i w =>
    ((by fun_prop : Continuous fun x : ℝ => (-2 * π * Complex.I * x) ^ i *
      Complex.exp (-2 * π * Complex.I * w * x)).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp (measurable_tailDensity n t)).aestronglyMeasurable
  have hbound : ∀ x : ℝ, ∀ w ∈ ball z 1, ‖(-2 * π * Complex.I * x) ^ (j + 1) *
      Complex.exp (-2 * π * Complex.I * w * x) * (tailDensity n t x : ℂ)‖ ≤
        C * tailDensity n t x := by
    intro x w hw
    have hf0 := tailDensity_nonneg n t x
    by_cases hx : |x| ≤ 4 / 3
    · have hwim : |w.im| ≤ |z.im| + 1 := by
        have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
        rw [mem_ball, dist_eq_norm] at hw
        have := abs_sub_abs_le_abs_sub w.im z.im
        linarith
      rw [norm_mul, norm_mul, norm_pow, norm_exp_neg_two_pi_I_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hf0]
      have hn : ‖-2 * π * Complex.I * (x : ℂ)‖ = 2 * π * |x| := by
        simp [Complex.norm_real, abs_of_pos pi_pos]
      rw [hn, hC]
      have hexp : Real.exp (2 * π * w.im * x) ≤ Real.exp (2 * π * (|z.im| + 1) * (4 / 3)) := by
        refine Real.exp_le_exp.2 ?_
        calc 2 * π * w.im * x ≤ |2 * π * w.im * x| := le_abs_self _
          _ = 2 * π * |w.im| * |x| := by
              rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          _ ≤ 2 * π * (|z.im| + 1) * (4 / 3) := by gcongr
      have hpow : (2 * π * |x|) ^ (j + 1) ≤ (2 * π * (4 / 3)) ^ (j + 1) := by gcongr
      exact mul_le_mul_of_nonneg_right (mul_le_mul hpow hexp (Real.exp_pos _).le
        (by positivity)) hf0
    · have : tailDensity n t x = 0 := tailDensity_eq_zero ht n (lt_of_not_ge hx)
      simp [this]
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := z)
    (F := fun w x => (-2 * π * Complex.I * x) ^ j * Complex.exp (-2 * π * Complex.I * w * x) *
      (tailDensity n t x : ℂ))
    (F' := fun w x => (-2 * π * Complex.I * x) ^ (j + 1) *
      Complex.exp (-2 * π * Complex.I * w * x) * (tailDensity n t x : ℂ))
    (bound := fun x => C * tailDensity n t x) (ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall fun w => hmeas j w)
    (integrable_mul_tailDensity ht n (by fun_prop)) (hmeas (j + 1) z)
    (Filter.Eventually.of_forall hbound) ((integrable_tailDensity n t).const_mul C)
    (Filter.Eventually.of_forall fun x w _ =>
      hasDerivAt_tailFTCIter_integrand j x (tailDensity n t x : ℂ) w)
  exact h

/-- The iterated derivatives of the entire extension: `Ψ^{(j)} = Ψ_j`. -/
theorem iteratedDeriv_tailFTC {t : ℝ} (ht : |t| ≤ 1) (n j : ℕ) :
    iteratedDeriv j (tailFTC n t) = tailFTCIter n t j := by
  induction j with
  | zero => rw [iteratedDeriv_zero, tailFTCIter_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hasDerivAt_tailFTCIter ht n j z).deriv

/-- For `|t| ≤ 1`, `Ψ_{n,t}` is entire. -/
theorem differentiable_tailFTC {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    Differentiable ℂ (tailFTC n t) := by
  rw [← tailFTCIter_zero]
  exact fun z => (hasDerivAt_tailFTCIter ht n 0 z).differentiableAt

/-- At real points the iterated integrals are the moments: `Ψ_j(ξ) = (-2πi)^j M_j(ξ)`. -/
lemma tailFTCIter_ofReal (n : ℕ) (t : ℝ) (j : ℕ) (ξ : ℝ) :
    tailFTCIter n t j ξ = (-2 * π * Complex.I) ^ j * tailMoment n t j ξ := by
  rw [tailFTCIter, tailMoment, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e : Complex.exp (-2 * π * Complex.I * (ξ : ℂ) * x) =
      Complex.exp (↑(-2 * π * ξ * x) * Complex.I) := by
    congr 1; push_cast; ring
  simp only
  rw [e, mul_pow]
  ring

/-- **Derivatives are moments**: `ψ^{(j)}(ξ) = Ψ^{(j)}(ξ) = (-2πi)^j M_j(ξ)`. -/
theorem iteratedDeriv_tailFTC_ofReal {t : ℝ} (ht : |t| ≤ 1) (n j : ℕ) (ξ : ℝ) :
    iteratedDeriv j (tailFTC n t) ξ = (-2 * π * Complex.I) ^ j * tailMoment n t j ξ := by
  rw [iteratedDeriv_tailFTC ht, tailFTCIter_ofReal]

end Favard.Exclusion
