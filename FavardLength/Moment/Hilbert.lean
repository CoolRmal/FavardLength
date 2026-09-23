import FavardLength.Statements
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finite Hilbert-matrix inequality

We prove (manuscript J6) that the Hilbert matrix `(1 / (i + j + 1))_{i,j}` is bounded on `ℓ²`,
restricted to nonnegative vectors, with constant `4`:
`∑_{i,j<L} b_i b_j / (i + j + 1) ≤ 4 ∑_{i<L} b_i²`.

The proof is the Schur test with weights `√(i+1)`: by AM-GM,
`2 b_i b_j ≤ b_i² √(i+1)/√(j+1) + b_j² √(j+1)/√(i+1)`, and the row sums
`∑_j √(i+1) / ((i+j+1) √(j+1))` are at most `4`, by splitting at `j = i` and comparing with the
telescoping sums of `2 (√(j+1) - √j)` and `2 (1/√a - 1/√(a+1))`.
-/

open Finset Real

namespace Favard

namespace Hilbert

/-- `∑_{j<n} 1/√(j+1) ≤ 2√n`. -/
lemma sum_inv_sqrt_le (n : ℕ) :
    ∑ j ∈ range n, 1 / √((j : ℝ) + 1) ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    set s := √(n : ℝ) with hs
    set t := √((n : ℝ) + 1) with ht
    have hs0 : 0 ≤ s := sqrt_nonneg _
    have ht0 : 0 < t := sqrt_pos.2 (by positivity)
    have hs2 : s ^ 2 = n := sq_sqrt (by positivity)
    have ht2 : t ^ 2 = n + 1 := sq_sqrt (by positivity)
    have key : 1 / t ≤ 2 * t - 2 * s := by
      rw [div_le_iff₀ ht0]
      nlinarith [sq_nonneg (s - t)]
    linarith

/-- `∑_{k<n} 1/((a+k+1)√(a+k+1)) ≤ 2/√a - 2/√(a+n)` for `a > 0`. -/
lemma sum_inv_pow_three_halves_le (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∑ k ∈ range n, 1 / ((a + k + 1) * √(a + k + 1)) ≤ 2 / √a - 2 / √(a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    have hc : 0 < a + n := by positivity
    set s := √(a + n) with hs
    set t := √(a + n + 1) with ht
    have hs0 : 0 < s := sqrt_pos.2 hc
    have ht0 : 0 < t := sqrt_pos.2 (by positivity)
    have hs2 : s ^ 2 = a + n := sq_sqrt hc.le
    have ht2 : t ^ 2 = a + n + 1 := sq_sqrt (by positivity)
    have hst : s ≤ t := sqrt_le_sqrt (by linarith)
    have key : 1 / ((a + n + 1) * t) ≤ 2 / s - 2 / t := by
      rw [← ht2, div_sub_div _ _ hs0.ne' ht0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      -- `s * t ≤ 2 t² (t - s) * t`, from `2t(t - s) ≥ 1` and `s ≤ t`
      have h1 : 1 ≤ 2 * t * (t - s) := by nlinarith [sq_nonneg (s - t)]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ t ^ 2 * t)]
    rw [show a + ((n : ℝ) + 1) = a + n + 1 by ring]
    linarith

/-- The Schur row sums with weights `√(i+1)`: `∑_{j<L} √(i+1) / ((i+j+1) √(j+1)) ≤ 4`. -/
lemma row_sum_le (i L : ℕ) :
    ∑ j ∈ range L, √((i : ℝ) + 1) / (((i : ℝ) + j + 1) * √((j : ℝ) + 1)) ≤ 4 := by
  set u := √((i : ℝ) + 1) with hu
  have hu0 : 0 < u := sqrt_pos.2 (by positivity)
  let g : ℕ → ℝ := fun j =>
    if j < i + 1 then 1 / (u * √((j : ℝ) + 1)) else u * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)))
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [g]; split_ifs <;> positivity
  have hterm : ∀ j : ℕ, u / (((i : ℝ) + j + 1) * √((j : ℝ) + 1)) ≤ g j := fun j => by
    have hv : 0 < √((j : ℝ) + 1) := sqrt_pos.2 (by positivity)
    have hu2 : u ^ 2 = (i : ℝ) + 1 := sq_sqrt (by positivity)
    simp only [g]
    split_ifs with hj
    · -- `j ≤ i`: use `i + j + 1 ≥ i + 1 = u²`
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (i : ℝ) + 1 ≤ (i : ℝ) + j + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ u * √((j : ℝ) + 1))]
    · -- `j > i`: use `i + j + 1 ≥ j + 1`
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left hu0.le (by positivity)
      apply mul_le_mul_of_nonneg_right _ hv.le
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  calc ∑ j ∈ range L, u / (((i : ℝ) + j + 1) * √((j : ℝ) + 1))
      ≤ ∑ j ∈ range L, g j := sum_le_sum fun j _ => hterm j
    _ ≤ ∑ j ∈ range (i + 1 + L), g j :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun j _ _ => hg0 j
    _ = ∑ j ∈ range (i + 1), 1 / (u * √((j : ℝ) + 1)) +
          u * ∑ k ∈ range L, 1 / (((i : ℝ) + 1 + k + 1) * √((i : ℝ) + 1 + k + 1)) := by
        rw [sum_range_add, mul_sum]
        congr 1
        · exact sum_congr rfl fun j hj => by simp only [g, mem_range.1 hj, ite_true]
        · refine sum_congr rfl fun k _ => ?_
          simp only [g, show ¬ (i + 1 + k < i + 1) by omega, ite_false]
          push_cast
          ring_nf
    _ ≤ 2 + 2 := by
        gcongr
        · calc ∑ j ∈ range (i + 1), 1 / (u * √((j : ℝ) + 1))
              = (1 / u) * ∑ j ∈ range (i + 1), 1 / √((j : ℝ) + 1) := by
                rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [one_div_mul_one_div]
            _ ≤ (1 / u) * (2 * u) := by
                gcongr
                have := sum_inv_sqrt_le (i + 1)
                push_cast at this
                exact this
            _ = 2 := by field_simp
        · have h := sum_inv_pow_three_halves_le ((i : ℝ) + 1) (by positivity) L
          have hpos : 0 ≤ 2 / √((i : ℝ) + 1 + L) := by positivity
          calc u * ∑ k ∈ range L, 1 / (((i : ℝ) + 1 + k + 1) * √((i : ℝ) + 1 + k + 1))
              ≤ u * (2 / u) := by gcongr; linarith
            _ = 2 := by field_simp
    _ = 4 := by norm_num

end Hilbert

open Hilbert in
/-- **Finite Hilbert-matrix inequality** (J6), with constant `4`, via the Schur test. -/
theorem hilbert : HilbertStatement := by
  refine ⟨4, by norm_num, fun L b hb => ?_⟩
  set T : ℕ → ℕ → ℝ := fun i j =>
    √((i : ℝ) + 1) / (((i : ℝ) + j + 1) * √((j : ℝ) + 1)) with hT
  -- AM-GM with the Schur weights
  have hamgm : ∀ i j, b i * b j / ((i : ℝ) + j + 1) ≤
      1 / 2 * (b i ^ 2 * T i j) + 1 / 2 * (b j ^ 2 * T j i) := fun i j => by
    have hu : 0 < √((i : ℝ) + 1) := sqrt_pos.2 (by positivity)
    have hv : 0 < √((j : ℝ) + 1) := sqrt_pos.2 (by positivity)
    have hK : 0 < (i : ℝ) + j + 1 := by positivity
    have hsym : (j : ℝ) + i + 1 = (i : ℝ) + j + 1 := by ring
    simp only [hT, hsym]
    rw [div_le_iff₀ hK]
    have e : (1 / 2 * (b i ^ 2 * (√((i : ℝ) + 1) / (((i : ℝ) + j + 1) * √((j : ℝ) + 1)))) +
        1 / 2 * (b j ^ 2 * (√((j : ℝ) + 1) / (((i : ℝ) + j + 1) * √((i : ℝ) + 1))))) *
          ((i : ℝ) + j + 1) =
        (b i ^ 2 * √((i : ℝ) + 1) ^ 2 + b j ^ 2 * √((j : ℝ) + 1) ^ 2) /
          (2 * (√((i : ℝ) + 1) * √((j : ℝ) + 1))) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (b i * √((i : ℝ) + 1) - b j * √((j : ℝ) + 1))]
  calc ∑ i ∈ range L, ∑ j ∈ range L, b i * b j / ((i : ℝ) + j + 1)
      ≤ ∑ i ∈ range L, ∑ j ∈ range L,
          (1 / 2 * (b i ^ 2 * T i j) + 1 / 2 * (b j ^ 2 * T j i)) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hamgm i j
    _ = ∑ i ∈ range L, ∑ j ∈ range L, b i ^ 2 * T i j := by
        simp only [sum_add_distrib]
        rw [sum_comm (f := fun i j => 1 / 2 * (b j ^ 2 * T j i)), ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ => by ring
    _ = ∑ i ∈ range L, b i ^ 2 * ∑ j ∈ range L, T i j := by simp only [mul_sum]
    _ ≤ ∑ i ∈ range L, b i ^ 2 * 4 := by
        gcongr with i hi
        exact row_sum_le i L
    _ = 4 * ∑ i ∈ range L, b i ^ 2 := by rw [← sum_mul, mul_comm]

end Favard
