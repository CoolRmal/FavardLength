import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The closed base-four grid on the real line

Used by the packing construction (G7–G9). The level-`k` grid intervals are
`gridIcc k j = [j 4^{-k}, (j + 1) 4^{-k}]`, `j ∈ ℤ`. For `k' ≤ k` the level-`k'` grid interval
containing `gridIcc k j` has index `gridAnc k k' j = j / 4^{k-k'}` (floor division). Two grid
intervals are either nested or meet in a null set, and an interval of length at least `4^{-k}`
meeting a level-`k` grid interval contains one of its endpoints.
-/

open MeasureTheory Set

namespace Favard.Comb

/-- The closed base-four grid interval `[j 4^{-k}, (j + 1) 4^{-k}]` of level `k`. -/
noncomputable def gridIcc (k : ℕ) (j : ℤ) : Set ℝ :=
  Icc (j / 4 ^ k) ((j + 1) / 4 ^ k)

/-- The index `j / 4^{k-k'}` of the level-`k'` grid interval containing the level-`k` grid
interval of index `j` (for `k' ≤ k`). -/
def gridAnc (k k' : ℕ) (j : ℤ) : ℤ :=
  j / 4 ^ (k - k')

theorem measurableSet_gridIcc (k : ℕ) (j : ℤ) : MeasurableSet (gridIcc k j) :=
  measurableSet_Icc

theorem volume_gridIcc (k : ℕ) (j : ℤ) : volume (gridIcc k j) = ENNReal.ofReal (1 / 4 ^ k) := by
  rw [gridIcc, Real.volume_Icc]
  congr 1
  ring

@[simp]
theorem gridAnc_self (k : ℕ) (j : ℤ) : gridAnc k k j = j := by
  simp [gridAnc]

theorem gridAnc_gridAnc {k k' k'' : ℕ} (h₁ : k'' ≤ k') (h₂ : k' ≤ k) (j : ℤ) :
    gridAnc k' k'' (gridAnc k k' j) = gridAnc k k'' j := by
  unfold gridAnc
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add]
  congr 2
  omega

/-- A grid interval lies in each of its grid ancestors. -/
theorem gridIcc_subset_gridAnc {k k' : ℕ} (h : k' ≤ k) (j : ℤ) :
    gridIcc k j ⊆ gridIcc k' (gridAnc k k' j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hd : k' + d - k' = d := by omega
  unfold gridAnc
  rw [hd]
  set a := j / 4 ^ d with ha
  have h4 : (0 : ℤ) < 4 ^ d := by positivity
  have h1 : a * 4 ^ d ≤ j := Int.ediv_mul_le j h4.ne'
  have h2 : j + 1 ≤ (a + 1) * 4 ^ d := Int.lt_ediv_add_one_mul_self j h4
  have h1' : (a : ℝ) * 4 ^ d ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) + 1 ≤ (a + 1) * 4 ^ d := by exact_mod_cast h2
  have hk : (0 : ℝ) < 4 ^ k' := by positivity
  have hd' : (0 : ℝ) < 4 ^ d := by positivity
  refine Icc_subset_Icc ?_ ?_
  · rw [pow_add, div_le_div_iff₀ hk (mul_pos hk hd')]
    nlinarith
  · rw [pow_add, div_le_div_iff₀ (mul_pos hk hd') hk]
    nlinarith

/-- Every point lies in the level-`k` grid interval of index `⌊x 4^k⌋`. -/
theorem mem_gridIcc_floor (k : ℕ) (x : ℝ) : x ∈ gridIcc k ⌊x * 4 ^ k⌋ := by
  have hk : (0 : ℝ) < 4 ^ k := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hk]
    exact Int.floor_le _
  · rw [le_div_iff₀ hk]
    exact (Int.lt_floor_add_one _).le

/-- Distinct grid intervals of the same level meet in a null set. -/
theorem volume_gridIcc_inter_of_ne {k : ℕ} {j j' : ℤ} (h : j ≠ j') :
    volume (gridIcc k j ∩ gridIcc k j') = 0 := by
  have hk : (0 : ℝ) < 4 ^ k := by positivity
  wlog hlt : j < j' generalizing j j'
  · rw [inter_comm]
    exact this (Ne.symm h) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h))
  refine measure_mono_null (t := Icc ((j' : ℝ) / 4 ^ k) ((j + 1) / 4 ^ k)) ?_ ?_
  · intro x hx
    exact ⟨hx.2.1, hx.1.2⟩
  · rw [Real.volume_Icc, ENNReal.ofReal_eq_zero, sub_nonpos,
      div_le_div_iff_of_pos_right hk]
    exact_mod_cast hlt

/-- Two grid intervals are nested or meet in a null set. -/
theorem gridAnc_eq_or_volume_inter_eq_zero {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (j₁ j₂ : ℤ) :
    gridAnc k₂ k₁ j₂ = j₁ ∨ volume (gridIcc k₁ j₁ ∩ gridIcc k₂ j₂) = 0 := by
  by_cases ha : gridAnc k₂ k₁ j₂ = j₁
  · exact Or.inl ha
  · refine Or.inr (measure_mono_null ?_ (volume_gridIcc_inter_of_ne (k := k₁) (Ne.symm ha)))
    exact inter_subset_inter_right _ (gridIcc_subset_gridAnc h j₂)

/-- An interval of length at least `4^{-k}` meeting a level-`k` grid interval contains one of the
two endpoints of the grid interval. -/
theorem endpoint_mem_of_inter_nonempty {k : ℕ} {j : ℤ} {a L : ℝ} (hL : 1 / 4 ^ k ≤ L)
    (hmeet : (Icc a (a + L) ∩ gridIcc k j).Nonempty) :
    (j : ℝ) / 4 ^ k ∈ Icc a (a + L) ∨ ((j : ℝ) + 1) / 4 ^ k ∈ Icc a (a + L) := by
  obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := hmeet
  have e : ((j : ℝ) + 1) / 4 ^ k = j / 4 ^ k + 1 / 4 ^ k := by ring
  by_cases hp : a ≤ (j : ℝ) / 4 ^ k
  · exact Or.inl ⟨hp, by linarith⟩
  · push Not at hp
    refine Or.inr ⟨by linarith, ?_⟩
    rw [e]
    linarith

end Favard.Comb
