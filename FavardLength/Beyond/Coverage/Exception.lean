import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The short-vector exception has small measure

Appendix I.4 of the beyond note. If the lattice attached to a slope `x ∈ [0, 1]` has a nonzero
vector `(q, p)` with `|q| < A/(rR)` and `|p - x q| < A/R`, then `x` lies within `A/(qR)` of a
fraction `p/q` with `1 ≤ q ≤ A/(rR)` and `0 ≤ p ≤ q`. The union of these intervals has measure at
most `∑_q (q + 1) 2A/(qR) ≤ 4 A² / (r R²)`.
-/

open MeasureTheory Set Finset

namespace Favard.Coverage

/-- The union of the intervals of radius `A/(qR)` about the fractions `p/q` with
`1 ≤ q ≤ A/(rR)` and `0 ≤ p ≤ q` (Appendix I, (15)). -/
def exceptionalSet (A R r : ℝ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 ⌊A / (r * R)⌋₊, ⋃ p ∈ Finset.range (q + 1),
    Metric.closedBall ((p : ℝ) / q) (A / (q * R))

/-- **Measure of the exceptional set** (Appendix I, (16)). -/
theorem volume_exceptionalSet_le {A R r : ℝ} (hA : 0 ≤ A) (hR : 0 < R) (hr : 0 < r) :
    volume (exceptionalSet A R r) ≤ ENNReal.ofReal (4 * A ^ 2 / (r * R ^ 2)) := by
  set Q := ⌊A / (r * R)⌋₊ with hQ
  have h1 : volume (exceptionalSet A R r) ≤
      ∑ q ∈ Finset.Icc 1 Q, ∑ p ∈ Finset.range (q + 1),
        volume (Metric.closedBall ((p : ℝ) / q) (A / (q * R))) := by
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun q _ => ?_)
    exact measure_biUnion_finset_le _ _
  refine h1.trans ?_
  simp only [Real.volume_closedBall]
  have hnn : ∀ q ∈ Finset.Icc 1 Q, ∀ p ∈ Finset.range (q + 1),
      (0 : ℝ) ≤ 2 * (A / (q * R)) := fun q _ p _ => by positivity
  rw [Finset.sum_congr rfl fun q hq => (ENNReal.ofReal_sum_of_nonneg (hnn q hq)).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun q hq => sum_nonneg (hnn q hq)]
  apply ENNReal.ofReal_le_ofReal
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      ∑ p ∈ Finset.range (q + 1), 2 * (A / (q * R)) ≤ 4 * A / R := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hq).1
    rw [sum_const, card_range, nsmul_eq_mul]
    push_cast
    rw [show ((q : ℝ) + 1) * (2 * (A / (q * R))) = (2 * A / R) * ((q + 1) / q) by
      field_simp]
    rw [show 4 * A / R = (2 * A / R) * 2 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc ∑ q ∈ Finset.Icc 1 Q, ∑ p ∈ Finset.range (q + 1), 2 * (A / (q * R))
      ≤ ∑ q ∈ Finset.Icc 1 Q, 4 * A / R := sum_le_sum hterm
    _ = Q * (4 * A / R) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ A / (r * R) * (4 * A / R) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
    _ = 4 * A ^ 2 / (r * R ^ 2) := by field_simp

/-- A positive denominator with a good approximation puts `x` in the exceptional set. -/
theorem mem_exceptionalSet_of_pos {A R r x : ℝ} (hR : 0 < R) (hAR : A ≤ R)
    (hx : x ∈ Icc (0 : ℝ) 1) {q : ℕ} {p : ℤ} (hq0 : 1 ≤ q) (hq : (q : ℝ) < A / (r * R))
    (hp : |(p : ℝ) - x * q| < A / R) : x ∈ exceptionalSet A R r := by
  have hAR1 : A / R ≤ 1 := (div_le_one hR).2 hAR
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  obtain ⟨hx0, hx1⟩ := hx
  have hpabs := abs_lt.1 hp
  have hp0 : 0 ≤ p := by
    have : (-1 : ℝ) < p := by nlinarith
    have : (-1 : ℤ) < p := by exact_mod_cast this
    omega
  have hpq : p ≤ q := by
    have : (p : ℝ) < q + 1 := by nlinarith
    have : p < (q : ℤ) + 1 := by exact_mod_cast this
    omega
  simp only [exceptionalSet, Set.mem_iUnion, exists_prop]
  refine ⟨q, Finset.mem_Icc.2 ⟨hq0, Nat.le_floor hq.le⟩, p.toNat,
    Finset.mem_range.2 (by omega), ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hpcast : ((p.toNat : ℕ) : ℝ) = p := by exact_mod_cast Int.toNat_of_nonneg hp0
  rw [hpcast]
  have hqpos : (0 : ℝ) < q := by linarith
  rw [show x - p / q = -((p - x * q) / q) by field_simp; ring, abs_neg, abs_div,
    abs_of_pos hqpos, div_le_div_iff₀ hqpos (by positivity)]
  have h1 : |(p : ℝ) - x * q| * R ≤ A := by
    have := (lt_div_iff₀ hR).1 hp
    linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hqpos.le]

/-- **Short vectors are exceptional** (Appendix I, (14)–(15)). A nonzero integer vector `(q, p)`
with `|q| < A/(rR)` and `|p - x q| < A/R`, for `x ∈ [0, 1]` and `A ≤ R`, puts `x` in the
exceptional set. -/
theorem mem_exceptionalSet {A R r x : ℝ} (hR : 0 < R) (hAR : A ≤ R) (hx : x ∈ Icc (0 : ℝ) 1)
    {q p : ℤ} (hqp : (q, p) ≠ 0) (hq : |(q : ℝ)| < A / (r * R))
    (hp : |(p : ℝ) - x * q| < A / R) : x ∈ exceptionalSet A R r := by
  have hAR1 : A / R ≤ 1 := (div_le_one hR).2 hAR
  rcases lt_trichotomy q 0 with hneg | hzero | hpos
  · apply mem_exceptionalSet_of_pos hR hAR hx (q := q.natAbs) (p := -p) (by omega)
    · have : ((q.natAbs : ℕ) : ℝ) = |(q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rwa [this]
    · have : ((q.natAbs : ℕ) : ℝ) = -(q : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      rw [this, show ((-p : ℤ) : ℝ) - x * -(q : ℝ) = -((p : ℝ) - x * q) by push_cast; ring,
        abs_neg]
      exact hp
  · exfalso
    subst hzero
    have : |(p : ℝ)| < 1 := by simpa using hp.trans_le hAR1
    have hp0 : p = 0 := by
      have : |p| < 1 := by exact_mod_cast this
      rw [abs_lt] at this
      omega
    exact hqp (by rw [hp0]; rfl)
  · apply mem_exceptionalSet_of_pos hR hAR hx (q := q.natAbs) (p := p) (by omega)
    · have : ((q.natAbs : ℕ) : ℝ) = |(q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rwa [this]
    · have : ((q.natAbs : ℕ) : ℝ) = (q : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
      rwa [this]

end Favard.Coverage
