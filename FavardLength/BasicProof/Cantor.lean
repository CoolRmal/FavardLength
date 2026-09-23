import FavardLength.Squares
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Cantor approximants and their square decomposition

Proofs of the combinatorial and topological facts of `FavardLength/Basic.lean` about the
approximants `C_n` and `K_n = C_n × C_n`:

* the sanity checks `C_0 = [0,1]`, `C_1 = [0,1/4] ∪ [3/4,1]`, `K_0 = [0,1]²`;
* the decomposition of `C_n` into the `2^n` intervals `[leftEnd b, leftEnd b + 4^{-n}]` and of
  `K_n` into the `4^n` squares `square w`;
* nesting, compactness, and the reflection symmetry `x ↦ 1 - x` of `C_n`;
* the projection of a square in a direction `θ ∈ [0, π/2]`.
-/

open MeasureTheory Set Real

namespace Favard.BasicProof

/-! ### Left endpoints -/

/-- The geometric sum `∑_{j<n} 3 · 4^{-(j+1)} = 1 - 4^{-n}`. -/
theorem sum_three_div_four_pow (n : ℕ) :
    ∑ j : Fin n, (3 : ℝ) / 4 ^ ((j : ℕ) + 1) = 1 - 1 / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    field_simp
    ring

/-- Splitting off the last digit of a left endpoint. -/
theorem leftEnd_succ {n : ℕ} (b : Fin (n + 1) → Bool) :
    leftEnd b = leftEnd (Fin.init b) + (if b (Fin.last n) then (3 : ℝ) else 0) / 4 ^ (n + 1) := by
  rw [leftEnd, Fin.sum_univ_castSucc]
  simp only [leftEnd, Fin.init, Fin.val_castSucc, Fin.val_last]
  rfl

theorem leftEnd_nonneg {n : ℕ} (b : Fin n → Bool) : 0 ≤ leftEnd b := by
  refine Finset.sum_nonneg fun j _ => div_nonneg ?_ (by positivity)
  split_ifs <;> norm_num

/-- Complementing every digit reflects the interval: `leftEnd b + leftEnd (!b) = 1 - 4^{-n}`. -/
theorem leftEnd_add_leftEnd_not {n : ℕ} (b : Fin n → Bool) :
    leftEnd b + leftEnd (fun j => !b j) = 1 - 1 / 4 ^ n := by
  rw [leftEnd, leftEnd, ← Finset.sum_add_distrib, ← sum_three_div_four_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases b j <;> simp

/-! ### Square decomposition -/

theorem cantorApprox_eq_iUnion (n : ℕ) :
    cantorApprox n = ⋃ b : Fin n → Bool, Icc (leftEnd b) (leftEnd b + 1 / 4 ^ n) := by
  ext x
  simp only [cantorApprox, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨w, hw, hx⟩
    refine ⟨fun j => decide (w j = 3), ?_⟩
    have hw' : w = fun j => if decide (w j = 3) then (3 : ℝ) else 0 := by
      funext j
      rcases hw j with h | h <;> simp [h]
    rw [hw'] at hx
    exact hx
  · rintro ⟨b, hx⟩
    exact ⟨fun j => if b j then 3 else 0, fun j => by by_cases h : b j <;> simp [h], hx⟩

theorem cantorApprox_zero : cantorApprox 0 = Icc 0 1 := by
  rw [cantorApprox_eq_iUnion]
  simp only [leftEnd, Finset.univ_eq_empty, Finset.sum_empty, pow_zero, zero_add, div_one]
  exact iUnion_const (ι := Fin 0 → Bool) (Icc (0 : ℝ) 1)

theorem cantorApprox_one : cantorApprox 1 = Icc 0 (1 / 4) ∪ Icc (3 / 4) 1 := by
  rw [cantorApprox_eq_iUnion]
  ext x
  simp only [mem_iUnion, mem_union, leftEnd, Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one]
  constructor
  · rintro ⟨b, hx⟩
    cases h : b 0 <;> simp only [h] at hx <;> norm_num at hx ⊢
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨fun _ => false, by norm_num; exact hx⟩
    · exact ⟨fun _ => true, by norm_num; exact hx⟩

theorem fourCorner_zero : fourCorner 0 = Icc 0 1 ×ˢ Icc 0 1 := by
  rw [fourCorner, cantorApprox_zero]

theorem fourCorner_eq_iUnion (n : ℕ) : fourCorner n = ⋃ w : SqCode n, square w := by
  ext ⟨x, y⟩
  simp only [fourCorner, cantorApprox_eq_iUnion, mem_prod, mem_iUnion, square, corner]
  constructor
  · rintro ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    exact ⟨fun j => (b j, b' j), hb, hb'⟩
  · rintro ⟨w, hx, hy⟩
    exact ⟨⟨_, hx⟩, ⟨_, hy⟩⟩

/-! ### Nesting and compactness -/

theorem cantorApprox_succ_subset (n : ℕ) : cantorApprox (n + 1) ⊆ cantorApprox n := by
  rw [cantorApprox_eq_iUnion, cantorApprox_eq_iUnion]
  refine iUnion_subset fun b => Subset.trans ?_ (subset_iUnion _ (Fin.init b))
  rw [leftEnd_succ]
  have h4 : (4 : ℝ) ^ (n + 1) = 4 ^ n * 4 := pow_succ _ _
  have hpos : (0 : ℝ) < 4 ^ n := by positivity
  have hd0 : 0 ≤ (if b (Fin.last n) then (3 : ℝ) else 0) / 4 ^ (n + 1) := by
    split_ifs <;> positivity
  have hd1 : (if b (Fin.last n) then (3 : ℝ) else 0) / 4 ^ (n + 1) + 1 / 4 ^ (n + 1) ≤
      1 / 4 ^ n := by
    rw [h4]
    split_ifs
    · rw [← add_div, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    · rw [zero_div, zero_add, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
  apply Icc_subset_Icc <;> linarith

theorem cantorApprox_antitone : Antitone cantorApprox :=
  antitone_nat_of_succ_le cantorApprox_succ_subset

/-- The approximants are nested. -/
theorem fourCorner_antitone {m n : ℕ} (h : m ≤ n) : fourCorner n ⊆ fourCorner m :=
  prod_mono (cantorApprox_antitone h) (cantorApprox_antitone h)

theorem fourCorner_subset (n : ℕ) : fourCorner n ⊆ Icc 0 1 ×ˢ Icc 0 1 :=
  fourCorner_zero ▸ fourCorner_antitone (Nat.zero_le n)

theorem isCompact_cantorApprox (n : ℕ) : IsCompact (cantorApprox n) := by
  rw [cantorApprox_eq_iUnion]
  exact isCompact_iUnion fun b => isCompact_Icc

theorem isCompact_fourCorner (n : ℕ) : IsCompact (fourCorner n) :=
  (isCompact_cantorApprox n).prod (isCompact_cantorApprox n)

/-! ### Reflection symmetry -/

/-- `C_n` is symmetric under `x ↦ 1 - x` (complement every digit). -/
theorem one_sub_mem_cantorApprox {n : ℕ} {x : ℝ} (hx : x ∈ cantorApprox n) :
    1 - x ∈ cantorApprox n := by
  rw [cantorApprox_eq_iUnion, mem_iUnion] at hx ⊢
  obtain ⟨b, h1, h2⟩ := hx
  have := leftEnd_add_leftEnd_not b
  exact ⟨fun j => !b j, by linarith, by linarith⟩

/-! ### Projections of squares -/

theorem continuous_proj (θ : ℝ) : Continuous (proj θ) := by
  unfold proj
  fun_prop

/-- For `cos θ, sin θ ≥ 0`, the projection of a box is the interval between the projections of
its lower-left and upper-right corners. -/
theorem proj_image_Icc_prod_Icc {θ : ℝ} (hc : 0 ≤ cos θ) (hs : 0 ≤ sin θ) {a a' b b' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') :
    proj θ '' (Icc a a' ×ˢ Icc b b') = Icc (proj θ (a, b)) (proj θ (a', b')) := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, rfl⟩
    simp only [proj]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hx1 hc, mul_le_mul_of_nonneg_right hy1 hs]
    · nlinarith [mul_le_mul_of_nonneg_right hx2 hc, mul_le_mul_of_nonneg_right hy2 hs]
  · apply IsPreconnected.Icc_subset
    · exact (isPreconnected_Icc.prod isPreconnected_Icc).image _ (continuous_proj θ).continuousOn
    · exact mem_image_of_mem _ ⟨⟨le_rfl, ha⟩, ⟨le_rfl, hb⟩⟩
    · exact mem_image_of_mem _ ⟨⟨ha, le_rfl⟩, ⟨hb, le_rfl⟩⟩

theorem cos_nonneg_of_mem_Icc_zero_pi_div_two {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) : 0 ≤ cos θ :=
  cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩

theorem sin_nonneg_of_mem_Icc_zero_pi_div_two {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) : 0 ≤ sin θ :=
  sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])

/-- For `θ ∈ [0, π/2]` the projection of a depth-`n` square is a closed interval of length
`(cos θ + sin θ) 4^{-n}` starting at the projection of the lower-left corner. -/
theorem proj_image_square {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) {n : ℕ} (w : SqCode n) :
    proj θ '' square w =
      Icc (proj θ (corner w)) (proj θ (corner w) + (cos θ + sin θ) / 4 ^ n) := by
  have h4 : (0 : ℝ) ≤ 1 / 4 ^ n := by positivity
  rw [square, proj_image_Icc_prod_Icc (cos_nonneg_of_mem_Icc_zero_pi_div_two hθ)
    (sin_nonneg_of_mem_Icc_zero_pi_div_two hθ) (le_add_of_nonneg_right h4)
    (le_add_of_nonneg_right h4)]
  congr 1
  simp only [proj]
  ring

theorem proj_image_fourCorner (θ : ℝ) (n : ℕ) :
    proj θ '' fourCorner n = ⋃ w : SqCode n, proj θ '' square w := by
  rw [fourCorner_eq_iUnion, image_iUnion]

theorem isCompact_square {n : ℕ} (w : SqCode n) : IsCompact (square w) :=
  isCompact_Icc.prod isCompact_Icc

theorem isCompact_proj_image_square (θ : ℝ) {n : ℕ} (w : SqCode n) :
    IsCompact (proj θ '' square w) :=
  (isCompact_square w).image (continuous_proj θ)

theorem isCompact_proj_image_fourCorner (θ : ℝ) (n : ℕ) : IsCompact (proj θ '' fourCorner n) :=
  (isCompact_fourCorner n).image (continuous_proj θ)

end Favard.BasicProof
