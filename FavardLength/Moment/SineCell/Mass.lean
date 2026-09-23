import FavardLength.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Short-interval mass bounds for the Riesz product (P4)

For `R = riesz m n = ∏_{k=m+1}^{n} (1 + cos(4^k w))` we prove, assuming the mean-one lemma
`MeanOneStatement`, the short-interval mass bound behind (P4)/(J2) of the manuscript in the
following form: for every `j : ℕ` and every interval `[a, b]`,
`∫_a^b R ≤ 2^j (b - a + 2π/4^{m+j+1})`.

The proof follows the manuscript: the first `j` factors are bounded by `2` each, so that
`R ≤ 2^j riesz (m + j) n`; the remaining product has period `2π/4^{m+j+1}` and mean one over
every full period (`MeanOneStatement` with `β = 1`), and `[a, b]` is covered by at most
`(b - a)/T + 1` consecutive periods of length `T = 2π/4^{m+j+1}`. The choice of `j` (with
`4^{-j} ≈ (b - a) 4^m`) is left to the user of these bounds.

The auxiliary lemmas of the SineCell part live in the namespace `Favard.SineCell`, to avoid
clashes with lemmas of the other parts.
-/

open MeasureTheory Set Real

namespace Favard.SineCell

/-- The Riesz product is nonnegative. -/
lemma riesz_nonneg (m n : ℕ) (w : ℝ) : 0 ≤ riesz m n w :=
  Finset.prod_nonneg fun k _ => by linarith [neg_one_le_cos (4 ^ k * w)]

lemma continuous_riesz (m n : ℕ) : Continuous (riesz m n) := by
  unfold riesz
  fun_prop

lemma measurable_riesz (m n : ℕ) : Measurable (riesz m n) :=
  (continuous_riesz m n).measurable

/-- Removing the lowest factor of the Riesz product costs at most a factor `2`. -/
lemma riesz_le_two_mul (m n : ℕ) (w : ℝ) : riesz m n w ≤ 2 * riesz (m + 1) n w := by
  rcases lt_or_ge m n with h | h
  · rw [riesz, ← Finset.insert_Ioc_add_one_left_eq_Ioc h, Finset.prod_insert (by simp)]
    exact mul_le_mul_of_nonneg_right (by linarith [cos_le_one (4 ^ (m + 1) * w)])
      (riesz_nonneg _ _ _)
  · have h1 : Finset.Ioc m n = ∅ := Finset.Ioc_eq_empty (by omega)
    have h2 : Finset.Ioc (m + 1) n = ∅ := Finset.Ioc_eq_empty (by omega)
    simp [riesz, h1, h2]

/-- Bounding the `j` lowest factors of the Riesz product by `2` each. -/
lemma riesz_le_two_pow_mul (m n j : ℕ) (w : ℝ) : riesz m n w ≤ 2 ^ j * riesz (m + j) n w := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc riesz m n w ≤ 2 ^ j * riesz (m + j) n w := ih
      _ ≤ 2 ^ j * (2 * riesz (m + j + 1) n w) := by
        gcongr
        exact riesz_le_two_mul _ _ _
      _ = 2 ^ (j + 1) * riesz (m + (j + 1)) n w := by rw [← add_assoc]; ring

/-- The Riesz product has mean one over every interval of length `2π/4^{m+1}`. -/
lemma integral_riesz_period (hM : MeanOneStatement) (m n : ℕ) (x : ℝ) :
    ∫ w in x..x + 2 * π / 4 ^ (m + 1), riesz m n w = 2 * π / 4 ^ (m + 1) := by
  have := hM 1 one_pos (m + 1) (Finset.Ioc m n) (fun k hk => (Finset.mem_Ioc.1 hk).1) x
  simpa [riesz] using this

/-- The integral of the Riesz product over an interval of length `ℓ` is at most `ℓ` plus one
period `2π/4^{m+1}`. -/
lemma integral_riesz_le (hM : MeanOneStatement) (m n : ℕ) (x : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ w in x..x + ℓ, riesz m n w ≤ ℓ + 2 * π / 4 ^ (m + 1) := by
  set T : ℝ := 2 * π / 4 ^ (m + 1) with hT
  have hTpos : 0 < T := by positivity
  set N : ℕ := ⌈ℓ / T⌉₊ with hN
  have hNT : ℓ ≤ N * T := by
    have := Nat.le_ceil (ℓ / T)
    rwa [div_le_iff₀ hTpos] at this
  have hNT' : (N : ℝ) * T ≤ ℓ + T := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg hℓ hTpos.le)
    have h2 := mul_lt_mul_of_pos_right h1 hTpos
    rw [add_mul, div_mul_cancel₀ _ hTpos.ne', one_mul] at h2
    exact h2.le
  have hint : ∫ w in x..x + N * T, riesz m n w = N * T := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := riesz m n) (μ := volume)
      (a := fun k : ℕ => x + k * T) (n := N)
      (fun k _ => (continuous_riesz m n).intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    have h' : ∀ k : ℕ, ∫ w in x + k * T..x + (k + 1 : ℕ) * T, riesz m n w = T := by
      intro k
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc]
      exact integral_riesz_period hM m n (x + k * T)
    rw [← h, Finset.sum_congr rfl fun k _ => h' k]
    simp
  calc ∫ w in x..x + ℓ, riesz m n w ≤ ∫ w in x..x + N * T, riesz m n w :=
        intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
          (ae_of_all _ fun w => riesz_nonneg m n w)
          ((continuous_riesz m n).intervalIntegrable _ _)
    _ = N * T := hint
    _ ≤ ℓ + T := hNT'

/-- **Short-interval mass bound** (P4): for every `j`, the integral of the Riesz product over an
interval of length `ℓ` is at most `2^j (ℓ + 2π/4^{m+j+1})`. -/
lemma integral_riesz_le_two_pow (hM : MeanOneStatement) (m n j : ℕ) (x : ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    ∫ w in x..x + ℓ, riesz m n w ≤ 2 ^ j * (ℓ + 2 * π / 4 ^ (m + j + 1)) := by
  calc ∫ w in x..x + ℓ, riesz m n w ≤ ∫ w in x..x + ℓ, 2 ^ j * riesz (m + j) n w :=
        intervalIntegral.integral_mono_on (by linarith)
          ((continuous_riesz m n).intervalIntegrable _ _)
          (((continuous_riesz _ n).const_mul _).intervalIntegrable _ _)
          fun w _ => riesz_le_two_pow_mul m n j w
    _ = 2 ^ j * ∫ w in x..x + ℓ, riesz (m + j) n w := intervalIntegral.integral_const_mul _ _
    _ ≤ 2 ^ j * (ℓ + 2 * π / 4 ^ (m + j + 1)) := by
        gcongr
        exact integral_riesz_le hM (m + j) n x hℓ

/-- The short-interval mass bound (P4) as a lower Lebesgue integral over a closed interval. -/
lemma lintegral_riesz_Icc_le (hM : MeanOneStatement) (m n j : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ w in Icc a b, ENNReal.ofReal (riesz m n w) ≤
      ENNReal.ofReal (2 ^ j * (b - a + 2 * π / 4 ^ (m + j + 1))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (continuous_riesz m n).integrableOn_Icc
    (ae_of_all _ fun w => riesz_nonneg m n w)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have := integral_riesz_le_two_pow hM m n j a (sub_nonneg.2 hab)
  rwa [add_sub_cancel] at this

end Favard.SineCell
