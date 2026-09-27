import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The transfer operator on the 4-adic grid of cell centres

For the cells `I_i = [iπ/4^m, (i+1)π/4^m]`, `i < 4^m`, with centres
`c_i = (i + 1/2)π/4^m` (`Favard.CellPowerSum.centre m i`), we bound the sums
`∑_{i<4^m} ∏_{k<m} (|cos(4^k c_i)| + d_k) ≤ ∏_{k<m} 4(r + d_k)`
for all `d_k ≥ 0`, provided the four-branch averages satisfy
`∑_{j<4} |cos((x + jπ)/4)| ≤ 4r` on `[0, π]` (`Favard.CellPowerSum.sum_prod_le`).

The proof is by induction on `m`. Writing `i = j 4^m + i'` with `j < 4`, `i' < 4^m`, one has
`4 c_i = c'_{i'} + jπ` for the generation-`m` centres `c'`, so by `π`-periodicity of `|cos|` all
factors with `k ≥ 1` depend only on `i'`, and the factor `k = 0` is summed over the four branches
`j`. This is the discrete replacement for the sampling inequality of Appendix B.1.2.

We also prove the exact four-branch evaluation (Appendix B.10 (30)): for `x ∈ [0, π]` and
`z = x/4`, `∑_{j<4} |cos((x + jπ)/4)| = (1 + √2) cos z + sin z ≤ √(4 + 2√2)`, in the rational form
`≤ 261313/100000` (`Favard.CellPowerSum.sum_abs_cos_le`).
-/

open Finset Real

namespace Favard

namespace CellPowerSum

/-- The centre `c_i = (i + 1/2)π/4^m` of the `i`-th cell of generation `m`. -/
noncomputable def centre (m i : ℕ) : ℝ :=
  ((i : ℝ) + 1 / 2) * π / 4 ^ m

lemma centre_pos (m i : ℕ) : 0 < centre m i := by
  unfold centre
  positivity

lemma centre_le_pi {m i : ℕ} (hi : i < 4 ^ m) : centre m i ≤ π := by
  unfold centre
  have hL : (0 : ℝ) < 4 ^ m := by positivity
  have hi' : (i : ℝ) + 1 ≤ 4 ^ m := by exact_mod_cast hi
  rw [div_le_iff₀ hL]
  nlinarith [pi_pos]

/-- Splitting a range of length `n b` into `n` blocks of length `b`. -/
lemma sum_range_mul_eq (h : ℕ → ℝ) (n b : ℕ) :
    ∑ i ∈ range (n * b), h i = ∑ j ∈ range n, ∑ i ∈ range b, h (j * b + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- `|cos|` is `π`-periodic. -/
lemma abs_cos_add_nat_mul_pi (y : ℝ) (n : ℕ) : |cos (y + n * π)| = |cos y| := by
  rw [cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The branches of `c ↦ 4c mod π`: `4 c_{j 4^m + i} = c'_i + jπ`. -/
lemma centre_succ (m i j : ℕ) :
    centre (m + 1) (j * 4 ^ m + i) = (centre m i + j * π) / 4 := by
  unfold centre
  push_cast
  field_simp
  ring

lemma abs_cos_centre_succ (m i j k : ℕ) :
    |cos (4 ^ (k + 1) * centre (m + 1) (j * 4 ^ m + i))| = |cos (4 ^ k * centre m i)| := by
  have h : (4 : ℝ) ^ (k + 1) * centre (m + 1) (j * 4 ^ m + i) =
      4 ^ k * centre m i + ((4 ^ k * j : ℕ) : ℝ) * π := by
    rw [centre_succ]
    push_cast
    ring
  rw [h, abs_cos_add_nat_mul_pi]

/-- An elementary inequality behind `ρ_* = √(4 + 2√2)/4`: if `c² + s² = 1` and `t = √2`, then
`(1 + t) c + s ≤ √((1 + t)² + 1) = √(4 + 2√2) ≤ 261313/100000`. -/
lemma add_sqrt_two_mul_le {c s t : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (ht : t ^ 2 = 2)
    (ht1 : t ≤ 141422 / 100000) : c + s + t * c ≤ 261313 / 100000 := by
  nlinarith [sq_nonneg ((1 + t) * s - c), sq_nonneg (c + s + t * c - 261313 / 100000)]

/-- The exact four-branch evaluation (Appendix B.10 (30)): for `x ∈ [0, π]`,
`∑_{j<4} |cos((x + jπ)/4)| = (1 + √2) cos(x/4) + sin(x/4) ≤ 261313/100000`. -/
lemma sum_abs_cos_le {x : ℝ} (hx : x ∈ Set.Icc 0 π) :
    ∑ j ∈ range 4, |cos ((x + j * π) / 4)| ≤ 261313 / 100000 := by
  obtain ⟨hx0, hxπ⟩ := hx
  set z := x / 4 with hz
  have hz0 : 0 ≤ z := by positivity
  have hzπ : z ≤ π / 4 := by rw [hz]; linarith
  have h0 : (x + ((0 : ℕ) : ℝ) * π) / 4 = z := by push_cast; ring
  have h1 : (x + ((1 : ℕ) : ℝ) * π) / 4 = z + π / 4 := by push_cast; ring
  have h2 : (x + ((2 : ℕ) : ℝ) * π) / 4 = z + π / 2 := by push_cast; ring
  have h3 : (x + ((3 : ℕ) : ℝ) * π) / 4 = z + π / 4 + π / 2 := by push_cast; ring
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, h0, h1, h2, h3,
    cos_add_pi_div_two, abs_neg]
  have hc : 0 ≤ cos z := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs : 0 ≤ sin z := sin_nonneg_of_nonneg_of_le_pi hz0 (by linarith [pi_pos])
  have hc' : 0 ≤ cos (z + π / 4) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs' : 0 ≤ sin (z + π / 4) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [pi_pos]) (by linarith [pi_pos])
  rw [abs_of_nonneg hc, abs_of_nonneg hs, abs_of_nonneg hc', abs_of_nonneg hs', cos_add, sin_add,
    cos_pi_div_four, sin_pi_div_four]
  have ht : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht1 : √2 ≤ 141422 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have key := add_sqrt_two_mul_le (c := cos z) (s := sin z) (by linarith [sin_sq_add_cos_sq z])
    ht ht1
  linarith

/-- **The transfer bound.** If the four-branch sums are at most `4r` on `[0, π]`, then for all
`d_k ≥ 0`, `∑_{i<4^m} ∏_{k<m} (|cos(4^k c_i)| + d_k) ≤ ∏_{k<m} 4(r + d_k)`. -/
theorem sum_prod_le {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ x ∈ Set.Icc 0 π, ∑ j ∈ range 4, |cos ((x + j * π) / 4)| ≤ 4 * r) (m : ℕ) (d : ℕ → ℝ)
    (hd : ∀ k, 0 ≤ d k) :
    ∑ i ∈ range (4 ^ m), ∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + d k) ≤
      ∏ k ∈ range m, (4 * (r + d k)) := by
  induction m generalizing d with
  | zero => simp
  | succ m ih =>
    set P : ℕ → ℝ := fun i => ∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + d (k + 1)) with hP
    have hP0 : ∀ i, 0 ≤ P i := fun i =>
      prod_nonneg fun k _ => add_nonneg (abs_nonneg _) (hd _)
    have hfactor : ∀ i j : ℕ,
        ∏ k ∈ range (m + 1), (|cos (4 ^ k * centre (m + 1) (j * 4 ^ m + i))| + d k) =
          (|cos ((centre m i + j * π) / 4)| + d 0) * P i := by
      intro i j
      rw [prod_range_succ', pow_zero, one_mul, centre_succ, mul_comm]
      congr 1
      refine prod_congr rfl fun k _ => ?_
      rw [← centre_succ, abs_cos_centre_succ]
    rw [pow_succ', sum_range_mul_eq, sum_comm]
    simp_rw [hfactor, ← sum_mul]
    calc ∑ i ∈ range (4 ^ m), (∑ j ∈ range 4, (|cos ((centre m i + j * π) / 4)| + d 0)) * P i
        ≤ ∑ i ∈ range (4 ^ m), (4 * (r + d 0)) * P i := by
          refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (hP0 i)
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
          have := hr (centre m i) ⟨(centre_pos m i).le, centre_le_pi (mem_range.1 hi)⟩
          push_cast
          linarith
      _ = (4 * (r + d 0)) * ∑ i ∈ range (4 ^ m), P i := by rw [mul_sum]
      _ ≤ (4 * (r + d 0)) * ∏ k ∈ range m, (4 * (r + d (k + 1))) :=
          mul_le_mul_of_nonneg_left (ih (fun k => d (k + 1)) fun k => hd _)
            (by nlinarith [hd 0])
      _ = ∏ k ∈ range (m + 1), (4 * (r + d k)) := by rw [prod_range_succ', mul_comm]

end CellPowerSum

end Favard
