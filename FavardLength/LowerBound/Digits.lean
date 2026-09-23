import FavardLength.Squares
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Separation and counting of square codes

Two depth-`n` square codes whose first difference is at level `k` have lower-left corners at
Euclidean distance at least `(1/2) 4^{-k}`: in a coordinate whose level-`k` digits differ, the
level-`k` contribution `3 · 4^{-(k+1)}` dominates the total `4^{-(k+1)}` of the deeper levels.
For a fixed code there are exactly `4^{n-j}` codes agreeing with it below level `j`.
-/

open Finset

namespace Favard.LowerBound

/-- The geometric sum `∑_{j<n} 3 · 4^{-(j+1)} = 1 - 4^{-n}` is at most one. -/
theorem sum_three_div_pow_le_one (n : ℕ) : ∑ j : Fin n, (3 : ℝ) / 4 ^ ((j : ℕ) + 1) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have h : ∑ j : Fin n, (3 : ℝ) / 4 ^ ((j.succ : ℕ) + 1) =
        1 / 4 * ∑ j : Fin n, (3 : ℝ) / 4 ^ ((j : ℕ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [h]
    simp only [Fin.val_zero, zero_add, pow_one]
    linarith

/-- **Digit separation.** If the digits `x j ∈ [-3, 3]` vanish below level `k` and `|x k| = 3`,
then `|∑_j x_j 4^{-(j+1)}| ≥ 2 · 4^{-(k+1)}`. -/
theorem two_div_pow_le_abs_sum {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 3) (k : Fin n)
    (hlt : ∀ j, j < k → x j = 0) (hk : |x k| = 3) :
    2 / 4 ^ ((k : ℕ) + 1) ≤ |∑ j, x j / 4 ^ ((j : ℕ) + 1)| := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    set T := ∑ j : Fin n, x j.succ / 4 ^ ((j : ℕ) + 1) with hT
    have hsplit : ∑ j : Fin n, x j.succ / 4 ^ ((j.succ : ℕ) + 1) = T / 4 := by
      rw [hT, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hsplit]
    simp only [Fin.val_zero, zero_add, pow_one]
    cases k using Fin.cases with
    | zero =>
      have hTle : |T| ≤ 1 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans
          (sum_three_div_pow_le_one n))
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ ((j : ℕ) + 1))]
        exact div_le_div_of_nonneg_right (hx _) (by positivity)
      simp only [Fin.val_zero, zero_add, pow_one] at hk ⊢
      have h1 : |x 0 / 4| = 3 / 4 := by rw [abs_div, hk]; norm_num
      have h2 : |T / 4| ≤ 1 / 4 := by
        rw [abs_div]; norm_num; linarith
      have := abs_sub_abs_le_abs_sub (x 0 / 4) (-(T / 4))
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    | succ k =>
      have h0 : x 0 = 0 := hlt 0 (Fin.succ_pos k)
      have hih := ih (fun j => x j.succ) (fun j => hx _) k
        (fun j hj => hlt _ (Fin.succ_lt_succ_iff.2 hj)) hk
      rw [h0, zero_div, zero_add, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        Fin.val_succ]
      rw [pow_succ]
      calc 2 / (4 ^ ((k : ℕ) + 1) * 4) = 2 / 4 ^ ((k : ℕ) + 1) / 4 := by ring
        _ ≤ |T| / 4 := by gcongr

/-- Two distinct codes have a first level at which they differ. -/
theorem exists_first_diff {n : ℕ} {w w' : SqCode n} (h : w ≠ w') :
    ∃ k : Fin n, (∀ j, j < k → w j = w' j) ∧ w k ≠ w' k := by
  classical
  set s := univ.filter fun j => w j ≠ w' j with hs
  have hne : s.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    exact h (funext fun j => not_not.1 (hemp (mem_univ j)))
  refine ⟨s.min' hne, fun j hj => ?_, (mem_filter.1 (s.min'_mem hne)).2⟩
  by_contra hjw
  exact absurd (s.min'_le j (mem_filter.2 ⟨mem_univ j, hjw⟩)) (not_le.2 hj)

/-- A difference of two corner digits `3 [a] - 3 [b]` lies in `[-3, 3]`. -/
theorem abs_digit_sub_le (a b : Bool) :
    |(if a then (3 : ℝ) else 0) - (if b then 3 else 0)| ≤ 3 := by
  cases a <;> cases b <;> norm_num

/-- Distinct corner digits differ by exactly `3`. -/
theorem abs_digit_sub_of_ne {a b : Bool} (h : a ≠ b) :
    |(if a then (3 : ℝ) else 0) - (if b then 3 else 0)| = 3 := by
  cases a <;> cases b <;> simp_all

/-- The difference of two left endpoints as a digit sum. -/
theorem leftEnd_sub_leftEnd {n : ℕ} (b b' : Fin n → Bool) :
    leftEnd b - leftEnd b' = ∑ j : Fin n,
      ((if b j then (3 : ℝ) else 0) - (if b' j then 3 else 0)) / 4 ^ ((j : ℕ) + 1) := by
  unfold leftEnd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_div]

/-- Left endpoints whose digit strings first differ at level `k` are `2 · 4^{-(k+1)}` apart. -/
theorem two_div_pow_le_abs_leftEnd_sub {n : ℕ} {b b' : Fin n → Bool} (k : Fin n)
    (hlt : ∀ j, j < k → b j = b' j) (hk : b k ≠ b' k) :
    2 / 4 ^ ((k : ℕ) + 1) ≤ |leftEnd b - leftEnd b'| := by
  rw [leftEnd_sub_leftEnd]
  refine two_div_pow_le_abs_sum _ (fun j => abs_digit_sub_le _ _) k (fun j hj => ?_)
    (abs_digit_sub_of_ne hk)
  rw [hlt j hj, sub_self]

/-- **Corner separation.** If two codes first differ at level `k`, their lower-left corners are
at Euclidean distance at least `(1/2) 4^{-k}`. -/
theorem sq_le_corner_sub {n : ℕ} {w w' : SqCode n} (k : Fin n)
    (hlt : ∀ j, j < k → w j = w' j) (hk : w k ≠ w' k) :
    (1 / (2 * 4 ^ (k : ℕ))) ^ 2 ≤
      ((corner w).1 - (corner w').1) ^ 2 + ((corner w).2 - (corner w').2) ^ 2 := by
  have heq : (1 : ℝ) / (2 * 4 ^ (k : ℕ)) = 2 / 4 ^ ((k : ℕ) + 1) := by
    rw [pow_succ]; field_simp; norm_num
  rw [heq]
  have hpos : (0 : ℝ) ≤ 2 / 4 ^ ((k : ℕ) + 1) := by positivity
  by_cases h1 : (w k).1 = (w' k).1
  · have h2 : (w k).2 ≠ (w' k).2 := fun h2 => hk (Prod.ext h1 h2)
    have hsep := two_div_pow_le_abs_leftEnd_sub (b := fun j => (w j).2)
      (b' := fun j => (w' j).2) k (fun j hj => by rw [hlt j hj]) h2
    have := pow_le_pow_left₀ hpos hsep 2
    rw [sq_abs] at this
    simp only [corner]
    nlinarith [sq_nonneg (leftEnd (fun j => (w j).1) - leftEnd fun j => (w' j).1)]
  · have hsep := two_div_pow_le_abs_leftEnd_sub (b := fun j => (w j).1)
      (b' := fun j => (w' j).1) k (fun j hj => by rw [hlt j hj]) h1
    have := pow_le_pow_left₀ hpos hsep 2
    rw [sq_abs] at this
    simp only [corner]
    nlinarith [sq_nonneg (leftEnd (fun j => (w j).2) - leftEnd fun j => (w' j).2)]

/-- For `j ≤ n`, exactly `4^{n-j}` depth-`n` codes agree with a given code below level `j`. -/
theorem card_agree_below {n j : ℕ} (hj : j ≤ n) (w : SqCode n) :
    (univ.filter fun w' : SqCode n => ∀ i : Fin n, (i : ℕ) < j → w i = w' i).card =
      4 ^ (n - j) := by
  classical
  have hset : (univ.filter fun w' : SqCode n => ∀ i : Fin n, (i : ℕ) < j → w i = w' i) =
      Fintype.piFinset fun i : Fin n => if (i : ℕ) < j then {w i} else univ := by
    ext w'
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    split_ifs with hi
    · simp [hi, eq_comm]
    · simp [hi]
  rw [hset, Fintype.card_piFinset]
  have hprod : ∀ i : Fin n,
      (if (i : ℕ) < j then ({w i} : Finset (Bool × Bool)) else univ).card =
        (fun m : ℕ => if m < j then 1 else 4) i := by
    intro i
    by_cases hi : (i : ℕ) < j
    · simp [hi]
    · simp [hi]
  rw [Finset.prod_congr rfl fun i _ => hprod i, Fin.prod_univ_eq_prod_range
    (fun m : ℕ => if m < j then 1 else 4) n, ← Finset.prod_range_mul_prod_Ico _ hj]
  rw [Finset.prod_eq_one fun m hm => by simp [Finset.mem_range.1 hm], one_mul]
  rw [Finset.prod_congr rfl fun m hm => (by simp [not_lt.2 (Finset.mem_Ico.1 hm).1] :
    (if m < j then 1 else 4) = 4), Finset.prod_const, Nat.card_Ico]

end Favard.LowerBound
