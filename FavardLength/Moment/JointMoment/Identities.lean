import FavardLength.Statements

/-!
# Product identities for the joint negative moment

This file collects the elementary identities behind the joint negative-moment estimate (J1) of
the manuscript (section "The joint negative-moment estimate", step 5).

With `u = y(1+t)` and `v = y(1-t)`:
* `lowProd m t y = A_m(u) A_m(v)`, where `A_m(w) = ∏_{k=0}^{m} cos(4^k w / 2)` (`halfProd`);
* `highProd m n t y ^ 2 = R(u) R(v) / 4^(n-m)`, where `R = riesz m n`;
* the telescoping identity `sin(4^m w) = 2 · 4^m sin(w/2) D(w) A_m(w)`, with `D = lowD m`.

From the last identity we deduce the pointwise bound, in `ℝ≥0∞`,
`|A_m(w)|^{-s} ≤ (2 · 4^m √β)^s |sin(4^m w)|^{-s}` whenever `D(w)² ≤ β` and `β > 0`.
-/

open Real Finset

namespace Favard

namespace JointMoment

/-- The half-frequency cosine product `A_m(w) = ∏_{k=0}^{m} cos(4^k w / 2)`. -/
noncomputable def halfProd (m : ℕ) (w : ℝ) : ℝ :=
  ∏ k ∈ range (m + 1), cos (4 ^ k * w / 2)

/-- `φ_t(z) = cos(z(1+t)/2) cos(z(1-t)/2)`. -/
lemma phi_eq_cos_mul_cos (t z : ℝ) :
    phi t z = cos (z * (1 + t) / 2) * cos (z * (1 - t) / 2) := by
  rw [phi, cos_add_cos]
  ring_nf

/-- The low-frequency product factors as `A_m(y(1+t)) A_m(y(1-t))`. -/
lemma lowProd_eq_halfProd_mul (m : ℕ) (t y : ℝ) :
    lowProd m t y = halfProd m (y * (1 + t)) * halfProd m (y * (1 - t)) := by
  rw [lowProd, halfProd, halfProd, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [phi_eq_cos_mul_cos]
  ring_nf

/-- `φ_t(z)² = (1 + cos(z(1+t)))(1 + cos(z(1-t)))/4`. -/
lemma phi_sq (t z : ℝ) :
    phi t z ^ 2 = (1 + cos (z * (1 + t))) * (1 + cos (z * (1 - t))) / 4 := by
  rw [phi_eq_cos_mul_cos, mul_pow, cos_sq, cos_sq]
  ring_nf

/-- The squared high-frequency product is `R(y(1+t)) R(y(1-t)) / 4^(n-m)`. -/
lemma highProd_sq (m n : ℕ) (t y : ℝ) :
    highProd m n t y ^ 2 =
      riesz m n (y * (1 + t)) * riesz m n (y * (1 - t)) / 4 ^ (n - m) := by
  rw [highProd, riesz, riesz, ← prod_pow, ← prod_mul_distrib, ← Nat.card_Ioc m n, ← prod_const,
    ← prod_div_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [phi_sq]
  ring_nf

/-- The Riesz product is nonnegative. -/
lemma riesz_nonneg (m n : ℕ) (w : ℝ) : 0 ≤ riesz m n w :=
  prod_nonneg fun k _ => by linarith [neg_one_le_cos (4 ^ k * w)]

/-- The telescoping identity `sin(4^m w) = 2 · 4^m sin(w/2) D(w) A_m(w)`. -/
lemma sin_four_pow_mul_eq (m : ℕ) (w : ℝ) :
    sin (4 ^ m * w) = 2 * 4 ^ m * sin (w / 2) * lowD m w * halfProd m w := by
  induction m with
  | zero =>
    simp only [pow_zero, one_mul, lowD, range_zero, prod_empty, mul_one, halfProd, zero_add,
      range_one, prod_singleton]
    rw [← sin_two_mul]
    ring_nf
  | succ m ih =>
    rw [lowD, prod_range_succ, ← lowD, halfProd, prod_range_succ, ← halfProd]
    have h1 : (4 : ℝ) ^ (m + 1) * w = 2 * (2 * (4 ^ m * w)) := by ring
    have h2 : (4 : ℝ) ^ (m + 1) * w / 2 = 2 * (4 ^ m * w) := by ring
    rw [h2, h1, sin_two_mul, sin_two_mul, ih]
    ring

/-- Reciprocal powers in `ℝ≥0∞`: if `|σ| ≤ c |a|` with `c > 0`, then
`|a|^{-s} ≤ c^s |σ|^{-s}`. Both sides may be `⊤`. -/
lemma ofReal_abs_rpow_neg_le {a σ c s : ℝ} (hs : 0 < s) (hc : 0 < c) (h : |σ| ≤ c * |a|) :
    ENNReal.ofReal |a| ^ (-s) ≤ ENNReal.ofReal (c ^ s) * ENNReal.ofReal |σ| ^ (-s) := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · rw [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (by simpa using rpow_pos_of_pos hc s)]
    exact le_top
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have ha : 0 < |a| := by
    by_contra ha
    have : |a| = 0 := le_antisymm (not_lt.1 ha) (abs_nonneg a)
    rw [this, mul_zero] at h
    linarith
  rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hσ',
    ← ENNReal.ofReal_mul (rpow_nonneg hc.le s)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_neg ha.le, rpow_neg hσ'.le, ← div_eq_mul_inv, le_div_iff₀ (rpow_pos_of_pos hσ' s),
    inv_mul_le_iff₀ (rpow_pos_of_pos ha s), mul_comm, ← mul_rpow hc.le ha.le]
  exact rpow_le_rpow hσ'.le h hs.le

/-- The pointwise bound `|A_m(w)|^{-s} ≤ (2 · 4^m √β)^s |sin(4^m w)|^{-s}` in `ℝ≥0∞`, whenever
`D(w)² ≤ β` with `β > 0`. -/
lemma ofReal_abs_halfProd_rpow_neg_le {m : ℕ} {w β s : ℝ} (hs : 0 < s) (hβ : 0 < β)
    (hD : lowD m w ^ 2 ≤ β) :
    ENNReal.ofReal |halfProd m w| ^ (-s) ≤
      ENNReal.ofReal ((2 * 4 ^ m * √β) ^ s) * ENNReal.ofReal |sin (4 ^ m * w)| ^ (-s) := by
  refine ofReal_abs_rpow_neg_le hs (by positivity) ?_
  rw [sin_four_pow_mul_eq, abs_mul, abs_mul, abs_mul]
  have h1 : |2 * (4 : ℝ) ^ m| = 2 * 4 ^ m := abs_of_pos (by positivity)
  have h2 : |sin (w / 2)| ≤ 1 := abs_sin_le_one _
  have h3 : |lowD m w| ≤ √β := abs_le_sqrt hD
  rw [h1]
  have h4 : 0 ≤ |halfProd m w| := abs_nonneg _
  have h5 : 0 ≤ |lowD m w| := abs_nonneg _
  have h6 : 0 ≤ |sin (w / 2)| := abs_nonneg _
  have h7 : (0 : ℝ) ≤ 2 * 4 ^ m := by positivity
  calc 2 * 4 ^ m * |sin (w / 2)| * |lowD m w| * |halfProd m w|
      ≤ 2 * 4 ^ m * 1 * √β * |halfProd m w| := by gcongr
    _ = 2 * 4 ^ m * √β * |halfProd m w| := by ring

end JointMoment

end Favard
