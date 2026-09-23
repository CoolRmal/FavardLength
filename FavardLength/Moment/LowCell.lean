import FavardLength.Statements
import FavardLength.Moment.LowCell.Pointwise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Low-frequency cell majorants (manuscript J4–J5)

We prove `Favard.lowCell_of : MeanOneStatement → LowCellStatement`. Write `L = 4^m`,
`h = π / L`, `I_i = [iπ/L, (i+1)π/L]` and `D = lowD m`, `D(w) = ∏_{k<m} cos(4^k w)`. The majorants
are
`b_i = (2/h) ∫_{I_i} D² + 2h ∫_{I_i} D'²`,
which dominate `D²` on `I_i` by the pointwise bound `Favard.LowCell.sq_le_of_hasDerivAt`.
Summing over the cells gives `∑ b_i = (2/h) ∫_0^π D² + 2h ∫_0^π D'²`, and:

* `∫_0^π D² = π 2^{-m}`: `cos² x = (1 + cos 2x)/2` and the mean-one lemma with `β = 2`, `a = 0`
  (the interval `[0, π]` is one period `2π/2`);
* `∫_0^π D'² ≤ 2π 4^{2m} 2^{-m}`: with `D' = ∑_k (∏_{j≠k} cos(4^j w)) (-4^k sin(4^k w))`, the
  Cauchy–Schwarz inequality gives `D'² ≤ (∑_k 4^k)(∑_k 4^k ∏_{j≠k} cos²(4^j w))`, and each
  product with one factor removed has integral `π 2^{1-m}` by the mean-one lemma.

Hence `∑ b_i ≤ 2 · 2^m + 4π² 2^m`. No Parseval identity is needed.
-/

open MeasureTheory Set Real

namespace Favard

namespace LowCell

/-- The derivative of `lowD m`:
`D'(w) = ∑_{k<m} (∏_{j<m, j≠k} cos(4^j w)) · (-(4^k sin(4^k w)))`. -/
noncomputable def lowDDeriv (m : ℕ) (w : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m,
    (∏ j ∈ (Finset.range m).erase k, cos (4 ^ j * w)) * (-(4 ^ k * sin (4 ^ k * w)))

lemma hasDerivAt_lowD (m : ℕ) (w : ℝ) : HasDerivAt (lowD m) (lowDDeriv m w) w := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.range m) (x := w)
    (f := fun k w => cos (4 ^ k * w)) (f' := fun k => -(4 ^ k * sin (4 ^ k * w)))
    fun k _ => by
      convert ((hasDerivAt_id' w).const_mul ((4 : ℝ) ^ k)).cos using 1
      ring
  simp only [smul_eq_mul] at h
  exact h

lemma continuous_lowDDeriv (m : ℕ) : Continuous (lowDDeriv m) := by
  unfold lowDDeriv
  fun_prop

lemma continuous_lowD (m : ℕ) : Continuous (lowD m) := by
  unfold lowD
  fun_prop

/-- `∏_{j∈S} cos²(4^j w) = 2^{-|S|} ∏_{j∈S} (1 + cos(2·4^j w))`. -/
lemma prod_cos_sq (S : Finset ℕ) (w : ℝ) :
    ∏ j ∈ S, cos (4 ^ j * w) ^ 2 = (1 / 2) ^ S.card * ∏ j ∈ S, (1 + cos (2 * 4 ^ j * w)) := by
  rw [Finset.pow_card_mul_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [cos_sq, ← mul_assoc]
  ring

/-- The mean of a lacunary product of squared cosines over `[0, π]`:
`∫_0^π ∏_{j∈S} cos²(4^j w) dw = π 2^{-|S|}`. -/
lemma integral_prod_cos_sq (hM : MeanOneStatement) (S : Finset ℕ) :
    ∫ w in (0 : ℝ)..π, ∏ j ∈ S, cos (4 ^ j * w) ^ 2 = π / 2 ^ S.card := by
  have h := hM 2 two_pos 0 S (fun k _ => Nat.zero_le k) 0
  have hπ : (0 : ℝ) + 2 * π / (2 * 4 ^ 0) = π := by ring
  rw [hπ] at h
  simp_rw [prod_cos_sq]
  rw [intervalIntegral.integral_const_mul, h, one_div, inv_pow]
  ring

/-- `∫_0^π D² = π 2^{-m}`. -/
lemma integral_lowD_sq (hM : MeanOneStatement) (m : ℕ) :
    ∫ w in (0 : ℝ)..π, lowD m w ^ 2 = π / 2 ^ m := by
  simp_rw [lowD, ← Finset.prod_pow]
  rw [integral_prod_cos_sq hM, Finset.card_range]

/-- Cauchy–Schwarz bound for the derivative:
`D'(w)² ≤ (∑_k 4^k) (∑_k 4^k ∏_{j≠k} cos²(4^j w))`. -/
lemma lowDDeriv_sq_le (m : ℕ) (w : ℝ) :
    lowDDeriv m w ^ 2 ≤ (∑ k ∈ Finset.range m, (4 : ℝ) ^ k) *
      ∑ k ∈ Finset.range m, 4 ^ k * ∏ j ∈ (Finset.range m).erase k, cos (4 ^ j * w) ^ 2 := by
  unfold lowDDeriv
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k _
    positivity
  · intro k _
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => sq_nonneg _)
  · intro k _
    have hP : 0 ≤ ∏ j ∈ (Finset.range m).erase k, cos (4 ^ j * w) ^ 2 :=
      Finset.prod_nonneg fun j _ => sq_nonneg _
    have hs := sin_sq_le_one (4 ^ k * w)
    rw [mul_pow, neg_sq, mul_pow, ← Finset.prod_pow]
    nlinarith [mul_le_mul_of_nonneg_left hs
      (mul_nonneg hP (by positivity : (0 : ℝ) ≤ ((4 : ℝ) ^ k) ^ 2))]

/-- `∑_{k<m} 4^k ≤ 4^m`. -/
lemma sum_four_pow_le (m : ℕ) : ∑ k ∈ Finset.range m, (4 : ℝ) ^ k ≤ 4 ^ m := by
  have h := geom_sum_mul (4 : ℝ) m
  have h0 : 0 ≤ ∑ k ∈ Finset.range m, (4 : ℝ) ^ k := Finset.sum_nonneg fun _ _ => by positivity
  norm_num at h
  linarith

/-- `∫_0^π D'² ≤ 2π 4^m 4^m 2^{-m}`. -/
lemma integral_lowDDeriv_sq_le (hM : MeanOneStatement) (m : ℕ) :
    ∫ w in (0 : ℝ)..π, lowDDeriv m w ^ 2 ≤ 2 * π * 4 ^ m * 4 ^ m / 2 ^ m := by
  set S := ∑ k ∈ Finset.range m, (4 : ℝ) ^ k with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hS : S ≤ 4 ^ m := sum_four_pow_le m
  have hcont : ∀ k, Continuous fun w => ∏ j ∈ (Finset.range m).erase k, cos (4 ^ j * w) ^ 2 :=
    fun k => by fun_prop
  have h2 : (2 : ℝ) ^ m ≤ 2 * 2 ^ (m - 1) := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (m - 1 + 1) := pow_le_pow_right₀ one_le_two (by omega)
      _ = 2 * 2 ^ (m - 1) := by ring
  have hπm : π / 2 ^ (m - 1) ≤ 2 * π / 2 ^ m := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pi_pos]
  calc ∫ w in (0 : ℝ)..π, lowDDeriv m w ^ 2
      ≤ ∫ w in (0 : ℝ)..π, S * ∑ k ∈ Finset.range m,
          4 ^ k * ∏ j ∈ (Finset.range m).erase k, cos (4 ^ j * w) ^ 2 := by
        refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ fun w _ => lowDDeriv_sq_le m w
        · exact ((continuous_lowDDeriv m).pow 2).intervalIntegrable _ _
        · exact Continuous.intervalIntegrable
            (continuous_const.mul (continuous_finsetSum _ fun k _ =>
              continuous_const.mul (hcont k))) _ _
    _ = S * ∑ k ∈ Finset.range m, 4 ^ k * (π / 2 ^ (m - 1)) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        · congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [intervalIntegral.integral_const_mul, integral_prod_cos_sq hM,
            Finset.card_erase_of_mem hk, Finset.card_range]
        · exact fun k _ => (continuous_const.mul (hcont k)).intervalIntegrable _ _
    _ = S * S * (π / 2 ^ (m - 1)) := by rw [← Finset.sum_mul, mul_assoc]
    _ ≤ 4 ^ m * 4 ^ m * (2 * π / 2 ^ m) := by
        have : 0 ≤ π / 2 ^ (m - 1) := by positivity
        gcongr
    _ = 2 * π * 4 ^ m * 4 ^ m / 2 ^ m := by ring

end LowCell

open LowCell in
/-- **Low-frequency cell majorants** (J4–J5): the numbers
`b_i = (2/h) ∫_{I_i} D² + 2h ∫_{I_i} D'²`, `h = π/4^m`, dominate `D²` on the cells
`I_i = [iπ/4^m, (i+1)π/4^m]` and sum to at most `(2 + 4π²) 2^m`. -/
theorem lowCell_of (hM : MeanOneStatement) : LowCellStatement := by
  refine ⟨2 + 4 * π ^ 2, by positivity, fun m => ?_⟩
  have hL : (0 : ℝ) < 4 ^ m := by positivity
  set h : ℝ := π / 4 ^ m with hh
  have hh0 : 0 < h := div_pos pi_pos hL
  set a : ℕ → ℝ := fun i => i * π / 4 ^ m with ha
  have hstep : ∀ i, a (i + 1) - a i = h := fun i => by
    simp only [ha, hh]; push_cast; ring
  have hmono : ∀ i, a i ≤ a (i + 1) := fun i => by linarith [hstep i]
  refine ⟨fun i => 2 / h * (∫ w in a i..a (i + 1), lowD m w ^ 2) +
    2 * h * ∫ w in a i..a (i + 1), lowDDeriv m w ^ 2, fun i => ?_, fun i _ w hw => ?_, ?_⟩
  · have h1 := intervalIntegral.integral_nonneg (μ := volume) (hmono i)
      fun w _ => sq_nonneg (lowD m w)
    have h2 := intervalIntegral.integral_nonneg (μ := volume) (hmono i)
      fun w _ => sq_nonneg (lowDDeriv m w)
    positivity
  · have hw' : w ∈ Icc (a i) (a (i + 1)) := by
      simpa only [ha, Nat.cast_add, Nat.cast_one] using hw
    have := sq_le_of_hasDerivAt (hasDerivAt_lowD m) (continuous_lowDDeriv m)
      (by linarith [hstep i]) hw'
    rwa [hstep i] at this
  · have ha0 : a 0 = 0 := by simp [ha]
    have haL : a (4 ^ m) = π := by simp only [ha]; push_cast; field_simp
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
        (f := fun w => lowD m w ^ 2) (a := a)
        (fun k _ => ((continuous_lowD m).pow 2).intervalIntegrable _ _),
      intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
        (f := fun w => lowDDeriv m w ^ 2) (a := a)
        (fun k _ => ((continuous_lowDDeriv m).pow 2).intervalIntegrable _ _),
      ha0, haL, integral_lowD_sq hM]
    have hD' := integral_lowDDeriv_sq_le hM m
    have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    calc 2 / h * (π / 2 ^ m) + 2 * h * ∫ w in (0 : ℝ)..π, lowDDeriv m w ^ 2
        ≤ 2 / h * (π / 2 ^ m) + 2 * h * (2 * π * 4 ^ m * 4 ^ m / 2 ^ m) := by gcongr
      _ = (2 + 4 * π ^ 2) * 2 ^ m := by
        rw [hh, h4]
        field_simp
        ring

end Favard
