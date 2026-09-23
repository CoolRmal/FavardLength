import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary sum and exponent bounds for the joint moment

* Concavity of `x ↦ x^s` (`0 ≤ s ≤ 1`): `∑_{i∈t} β_i^s ≤ |t|^{1-s} (∑_{i∈t} β_i)^s`.
* The exponent bookkeeping `((2L)^s)² L^{1-s} (√L)^s = 4^s L^{3s/2} L` for `L = 4^m`, used to
  collect the final power `L^{3s/2}` in (J1).
-/

open Real Finset

namespace Favard

namespace JointMoment

/-- Concavity of `x ↦ x^s`: `∑_{i∈t} β_i^s ≤ |t|^{1-s} (∑_{i∈t} β_i)^s` for `0 ≤ s ≤ 1`. -/
lemma sum_rpow_le_card_rpow_mul {ι : Type*} (t : Finset ι) {β : ι → ℝ} (hβ : ∀ i ∈ t, 0 ≤ β i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ i ∈ t, β i ^ s ≤ (t.card : ℝ) ^ (1 - s) * (∑ i ∈ t, β i) ^ s := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp only [sum_empty, card_empty, Nat.cast_zero]
    positivity
  have hn : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hJ := (Real.concaveOn_rpow hs0 hs1).le_map_sum (t := t) (w := fun _ => (t.card : ℝ)⁻¹)
    (p := β) (fun _ _ => by positivity) (by simp [hn.ne']) hβ
  simp only [smul_eq_mul, ← mul_sum] at hJ
  rw [mul_rpow (by positivity) (sum_nonneg hβ), inv_rpow hn.le] at hJ
  have h := mul_le_mul_of_nonneg_left hJ hn.le
  rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h
  rw [rpow_sub hn, rpow_one]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Exponent bookkeeping: `((2L)^s)² L^{1-s} (2^m)^s = 4^s L^{3s/2} L` for `L = 4^m`. -/
lemma exponent_identity (m : ℕ) (s : ℝ) :
    ((2 * (4 : ℝ) ^ m) ^ s) ^ 2 * ((4 : ℝ) ^ m) ^ (1 - s) * ((2 : ℝ) ^ m) ^ s =
      4 ^ s * ((4 : ℝ) ^ m) ^ (3 * s / 2) * 4 ^ m := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have e4 : (4 : ℝ) ^ m = 2 ^ (2 * (m : ℝ)) := by
    rw [rpow_mul h2.le, rpow_natCast]
    norm_num
  have e2 : (2 : ℝ) ^ m = 2 ^ (m : ℝ) := (rpow_natCast 2 m).symm
  have e24 : 2 * (4 : ℝ) ^ m = 2 ^ (1 + 2 * (m : ℝ)) := by rw [rpow_add h2, rpow_one, e4]
  have e4s : (4 : ℝ) ^ s = 2 ^ (2 * s) := by
    rw [rpow_mul h2.le]
    norm_num
  rw [e24, e4, e2, e4s, ← rpow_mul h2.le, ← rpow_mul h2.le, ← rpow_mul h2.le,
    ← rpow_mul h2.le, ← rpow_mul_natCast h2.le, ← rpow_add h2, ← rpow_add h2, ← rpow_add h2,
    ← rpow_add h2]
  congr 1
  push_cast
  ring

end JointMoment

end Favard
