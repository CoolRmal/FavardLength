import FavardLength.Fourier.Annular.Expansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The triangle kernel and the total high-frequency mass

The one-sided triangle weight `1 - y` on `[0, 1]` has a nonnegative cosine transform:
`∫_0^1 (1 - y) cos(λ y) dy = (1 - cos λ)/λ² ≥ 0` for `λ ≠ 0`, and it equals `1/2` for `λ = 0`.

Expanding `ν̂_{r,t}(a y)² = 4^{-2r} ∑_{d,d'} cos(a y (c_d - c_{d'}))` over codes and integrating
against `1 - y`, every term is nonnegative, and the `4^r` diagonal terms contribute `1/2` each.
Hence (manuscript, P3, first display, in one-sided form)

`∫_0^1 P₂(t, y)² dy ≥ ∫_0^1 (1 - y) P₂(t, y)² dy ≥ 4^{-r}/2`, with `r = n - m`.
-/

open Real Finset

namespace Favard

namespace Annular

/-- The cosine transform of the one-sided triangle weight, for a nonzero frequency. -/
lemma integral_one_sub_mul_cos_of_ne_zero {l : ℝ} (hl : l ≠ 0) :
    ∫ y in (0 : ℝ)..1, (1 - y) * cos (l * y) = (1 - cos l) / l ^ 2 := by
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => (1 - y) * sin (l * y) / l - cos (l * y) / l ^ 2)
        ((1 - y) * cos (l * y)) y := by
    intro y _
    have h1 : HasDerivAt (fun y => l * y) l y := by
      simpa using (hasDerivAt_id y).const_mul l
    have hs := (Real.hasDerivAt_sin (l * y)).comp y h1
    have hc := (Real.hasDerivAt_cos (l * y)).comp y h1
    have := ((((hasDerivAt_id y).const_sub 1).mul hs).div_const l).sub (hc.div_const (l ^ 2))
    refine this.congr_deriv ?_
    simp only [Function.comp, id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  simp
  ring

/-- The cosine transform of the one-sided triangle weight at frequency zero is `1/2`. -/
lemma integral_one_sub_mul_cos_zero :
    ∫ y in (0 : ℝ)..1, (1 - y) * cos (0 * y) = 1 / 2 := by
  simp only [zero_mul, cos_zero, mul_one]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id]
  norm_num

/-- **The triangle kernel is positive definite**: `∫_0^1 (1 - y) cos(λ y) dy ≥ 0`. -/
lemma integral_one_sub_mul_cos_nonneg (l : ℝ) :
    0 ≤ ∫ y in (0 : ℝ)..1, (1 - y) * cos (l * y) := by
  rcases eq_or_ne l 0 with rfl | hl
  · rw [integral_one_sub_mul_cos_zero]
    norm_num
  · rw [integral_one_sub_mul_cos_of_ne_zero hl]
    exact div_nonneg (by linarith [cos_le_one l]) (sq_nonneg l)

/-- **Diagonal lower bound**: `∫_0^1 (1 - y) ν̂_{r,t}(a y)² dy ≥ 4^{-r}/2` for every scale `a`. -/
lemma inv_pow_div_two_le_integral_one_sub_mul_nuHat_sq (r : ℕ) (t a : ℝ) :
    ((4 : ℝ) ^ r)⁻¹ / 2 ≤ ∫ y in (0 : ℝ)..1, (1 - y) * nuHat r t (a * y) ^ 2 := by
  set K : ℝ → ℝ := fun l => ∫ y in (0 : ℝ)..1, (1 - y) * cos (l * y) with hK
  have hexp : (fun y => (1 - y) * nuHat r t (a * y) ^ 2) = fun y => ((4 : ℝ) ^ r)⁻¹ ^ 2 *
      ∑ d : Fin r → Fin 4, ∑ d' : Fin r → Fin 4,
        (1 - y) * cos ((a * (code r t d - code r t d')) * y) := by
    funext y
    rw [nuHat_sq, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d' _ => ?_
    ring_nf
  have hint : ∀ l : ℝ,
      IntervalIntegrable (fun y => (1 - y) * cos (l * y)) MeasureTheory.volume 0 1 := fun l => by apply Continuous.intervalIntegrable; fun_prop
  rw [hexp, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    fun d _ => (by
      apply Continuous.intervalIntegrable
      fun_prop)]
  simp_rw [intervalIntegral.integral_finsetSum fun d' _ => hint _]
  change _ ≤ _ * ∑ d : Fin r → Fin 4, ∑ d' : Fin r → Fin 4, K (a * (code r t d - code r t d'))
  have hdiag : ∑ d : Fin r → Fin 4, (1 / 2 : ℝ) ≤
      ∑ d : Fin r → Fin 4, ∑ d' : Fin r → Fin 4, K (a * (code r t d - code r t d')) := by
    refine Finset.sum_le_sum fun d _ => ?_
    have hdd : K (a * (code r t d - code r t d)) = 1 / 2 := by
      simp only [hK, sub_self, mul_zero]
      exact integral_one_sub_mul_cos_zero
    rw [← hdd]
    exact Finset.single_le_sum (f := fun d' => K (a * (code r t d - code r t d')))
      (fun d' _ => integral_one_sub_mul_cos_nonneg _) (Finset.mem_univ d)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul] at hdiag
  have hpos : 0 < ((4 : ℝ) ^ r)⁻¹ ^ 2 := by positivity
  calc ((4 : ℝ) ^ r)⁻¹ / 2 = ((4 : ℝ) ^ r)⁻¹ ^ 2 * (((4 ^ r : ℕ) : ℝ) * (1 / 2)) := by
        push_cast
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag hpos.le

/-- **Total high-frequency mass**: `∫_0^1 P₂(t, y)² dy ≥ 4^{-(n-m)}/2`. -/
lemma inv_pow_div_two_le_integral_highProd_sq {m n : ℕ} (hmn : m ≤ n) (t : ℝ) :
    ((4 : ℝ) ^ (n - m))⁻¹ / 2 ≤ ∫ y in (0 : ℝ)..1, highProd m n t y ^ 2 := by
  calc ((4 : ℝ) ^ (n - m))⁻¹ / 2 ≤ ∫ y in (0 : ℝ)..1, (1 - y) * highProd m n t y ^ 2 := by
        simp_rw [highProd_eq_nuHat hmn]
        exact inv_pow_div_two_le_integral_one_sub_mul_nuHat_sq _ _ _
    _ ≤ ∫ y in (0 : ℝ)..1, highProd m n t y ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop) fun y hy => ?_
        have := sq_nonneg (highProd m n t y)
        nlinarith [hy.1]

end Annular

end Favard
