import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary inequalities for the exceptional-direction estimate

Scalar ingredients of the proof of (J9):

* `ofReal_sq_le_split`: the pointwise splitting `q² ≤ a⁻² (pq)² + a^s |p|^{-s} q²` according to
  whether `|p| ≥ a` or `|p| < a`, stated in `ℝ≥0∞` where `0^{-s} = ⊤`;
* `exists_pow_four_between`: a scale `L = 4^m` with `x ≤ L ≤ max 1 (4x)`;
* `natCast_add_one_le_of_pow_four_le`: such an `m` is `O(2 + log H)` when `x ≍ H`;
* `le_of_forall_threshold`: optimization of the threshold `a` in `c v ≤ P v a⁻² + D a^s`.
-/

open Real

namespace Favard.Exceptional

/-- Pointwise splitting according to whether `|p| ≥ a` (then `q² ≤ a⁻²(pq)²`) or `|p| < a` (then
`1 ≤ a^s |p|^{-s}`). The reciprocal power is taken in `ℝ≥0∞`, so the case `p = 0` is included. -/
lemma ofReal_sq_le_split {s a κ : ℝ} (hs : 0 < s) (ha : 0 < a) (hκ : 0 < κ) (p q : ℝ) :
    ENNReal.ofReal (q ^ 2) ≤
      ENNReal.ofReal ((a ^ 2 * κ)⁻¹) * ENNReal.ofReal (κ * (p * q) ^ 2) +
        ENNReal.ofReal (a ^ s) * (ENNReal.ofReal |p| ^ (-s) * ENNReal.ofReal (q ^ 2)) := by
  rcases le_or_gt a |p| with h | h
  · refine le_add_right ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : a ^ 2 ≤ p ^ 2 := by
      rw [← sq_abs p]; exact pow_le_pow_left₀ ha.le h 2
    have : (a ^ 2 * κ)⁻¹ * (κ * (p * q) ^ 2) = p ^ 2 * q ^ 2 / a ^ 2 := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg q]
  · refine le_add_left ?_
    rw [← mul_assoc]
    refine le_mul_of_one_le_left (by simp) ?_
    rw [ENNReal.rpow_neg, ← div_eq_mul_inv]
    have h0 : ENNReal.ofReal (a ^ s) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [ENNReal.le_div_iff_mul_le (Or.inr h0) (Or.inr ENNReal.ofReal_ne_top), one_mul,
      ← ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h.le) hs.le

/-- A power of four between `x` and `max 1 (4x)`. -/
lemma exists_pow_four_between (x : ℝ) :
    ∃ m : ℕ, x ≤ 4 ^ m ∧ (4 : ℝ) ^ m ≤ max 1 (4 * x) := by
  rcases le_or_gt x 1 with h | h
  · exact ⟨0, by simpa using h, by simp⟩
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h.le (by norm_num : (1 : ℝ) < 4)
    refine ⟨n + 1, hn2.le, le_max_of_le_right ?_⟩
    rw [pow_succ]; linarith

lemma one_le_log_four : 1 ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- If `4^m ≤ K H` with `K, H ≥ 1`, then `m + 1 ≤ (1 + log K)(2 + log H)`. -/
lemma natCast_add_one_le_of_pow_four_le {m : ℕ} {K H : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hm : (4 : ℝ) ^ m ≤ K * H) : (m : ℝ) + 1 ≤ (1 + Real.log K) * (2 + Real.log H) := by
  have hlog : (m : ℝ) * Real.log 4 ≤ Real.log K + Real.log H := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hm
  have hK0 : 0 ≤ Real.log K := Real.log_nonneg hK
  have hH0 : 0 ≤ Real.log H := Real.log_nonneg hH
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_le_mul_of_nonneg_left one_le_log_four hm0, mul_nonneg hK0 hH0]

/-- Optimization of the threshold: if `c v ≤ P v / a² + D a^s` for every `a > 0`, then
`v ≤ (2D/c) (2P/c)^{s/2}`. One takes `a^s = c v / (2D)`. -/
lemma le_of_forall_threshold {c v P D s : ℝ} (hc : 0 < c) (hv : 0 < v) (hD : 0 < D) (hs : 0 < s)
    (h : ∀ a : ℝ, 0 < a → c * v ≤ P * v / a ^ 2 + D * a ^ s) :
    v ≤ 2 * D / c * (2 * P / c) ^ (s / 2) := by
  set x := c * v / (2 * D) with hx
  have hx0 : 0 < x := by positivity
  set a := x ^ s⁻¹
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have has : a ^ s = x := Real.rpow_inv_rpow hx0.le hs.ne'
  have h1 := h a ha0
  rw [has] at h1
  have hDx : D * x = c * v / 2 := by rw [hx]; field_simp
  have h2 : a ^ 2 ≤ 2 * P / c := by
    rw [le_div_iff₀ hc]
    have h3 : c * v / 2 ≤ P * v / a ^ 2 := by linarith
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  have h4 : (a ^ 2) ^ (s / 2) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le, ← has]
    congr 1; push_cast; ring
  have h5 : x ≤ (2 * P / c) ^ (s / 2) := by
    rw [← h4]; exact Real.rpow_le_rpow (by positivity) h2 (by positivity)
  rw [hx, div_le_iff₀ (by positivity)] at h5
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

end Favard.Exceptional
