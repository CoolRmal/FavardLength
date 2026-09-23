import FavardLength.Squares
import FavardLength.Combinatorics.Words
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Projected intervals of construction squares

Fix a direction `θ ∈ [0, π/2]` and write `σ = cos θ + sin θ ∈ [1, √2]` (`Favard.Comb.sig`).
The square coded by a word `w` projects to the closed interval
`wordIval θ w = [wordPos θ w, wordPos θ w + σ 4^{-|w|}]`. The left endpoint satisfies the
self-similarity relation `wordPos θ (u ++ v) = wordPos θ u + 4^{-|u|} wordPos θ v`, which gives

* nesting: the projection of a descendant lies in the projection of its ancestor;
* the scaling rule `x ∈ wordIval θ (u ++ v) ↔ 4^{|u|} (x - wordPos θ u) ∈ wordIval θ v`, used for
  the self-similarity of subtrees (G10, G17).

We also bridge to the frozen definitions: `proj θ (corner w) = wordPos θ (List.ofFn w)`, the
multiplicity `count n θ x` is the number of words of length `n` whose interval contains `x`, and
`projLength n θ` is the length of the union of these intervals.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

/-! ### The projection factor `σ = cos θ + sin θ` -/

/-- The length factor `σ = cos θ + sin θ` of projected squares. -/
noncomputable def sig (θ : ℝ) : ℝ := cos θ + sin θ

variable {θ : ℝ}

theorem cos_nonneg_of_mem_Icc (hθ : θ ∈ Icc 0 (π / 2)) : 0 ≤ cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩

theorem sin_nonneg_of_mem_Icc (hθ : θ ∈ Icc 0 (π / 2)) : 0 ≤ sin θ :=
  sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])

theorem one_le_sig (hθ : θ ∈ Icc 0 (π / 2)) : 1 ≤ sig θ := by
  have hc := cos_nonneg_of_mem_Icc hθ
  have hs := sin_nonneg_of_mem_Icc hθ
  have hc1 := cos_le_one θ
  have hs1 := sin_le_one θ
  have h := cos_sq_add_sin_sq θ
  unfold sig
  nlinarith

theorem sig_pos (hθ : θ ∈ Icc 0 (π / 2)) : 0 < sig θ :=
  lt_of_lt_of_le one_pos (one_le_sig hθ)

theorem sig_nonneg (hθ : θ ∈ Icc 0 (π / 2)) : 0 ≤ sig θ :=
  (sig_pos hθ).le

theorem sig_le_sqrt_two (θ : ℝ) : sig θ ≤ √2 := by
  have h := cos_sq_add_sin_sq θ
  refine Real.le_sqrt_of_sq_le ?_
  unfold sig
  nlinarith [sq_nonneg (cos θ - sin θ)]

theorem sig_le_two (θ : ℝ) : sig θ ≤ 2 := by
  have := sig_le_sqrt_two θ
  have : √2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

/-! ### Left endpoints -/

/-- The projection `3([d.1] cos θ + [d.2] sin θ)` of the corner offset of the digit `d`,
before scaling by `1/4`. -/
noncomputable def digitShift (θ : ℝ) (d : Bool × Bool) : ℝ :=
  3 * ((if d.1 then cos θ else 0) + (if d.2 then sin θ else 0))

theorem digitShift_nonneg (hθ : θ ∈ Icc 0 (π / 2)) (d : Bool × Bool) : 0 ≤ digitShift θ d := by
  have hc := cos_nonneg_of_mem_Icc hθ
  have hs := sin_nonneg_of_mem_Icc hθ
  unfold digitShift
  split_ifs <;> linarith

theorem digitShift_le (hθ : θ ∈ Icc 0 (π / 2)) (d : Bool × Bool) :
    digitShift θ d ≤ 3 * sig θ := by
  have hc := cos_nonneg_of_mem_Icc hθ
  have hs := sin_nonneg_of_mem_Icc hθ
  unfold digitShift sig
  split_ifs <;> linarith

/-- The left endpoint `π_θ(corner w)` of the projection of the square coded by `w`. -/
noncomputable def wordPos (θ : ℝ) : Word → ℝ
  | [] => 0
  | d :: w => (digitShift θ d + wordPos θ w) / 4

@[simp]
theorem wordPos_nil : wordPos θ [] = 0 := rfl

@[simp]
theorem wordPos_cons (d : Bool × Bool) (w : Word) :
    wordPos θ (d :: w) = (digitShift θ d + wordPos θ w) / 4 := rfl

/-- Self-similarity of the left endpoints. -/
theorem wordPos_append (u v : Word) :
    wordPos θ (u ++ v) = wordPos θ u + wordPos θ v / 4 ^ u.length := by
  induction u with
  | nil => simp
  | cons d u ih =>
    simp only [List.cons_append, wordPos_cons, ih, List.length_cons, pow_succ]
    field_simp
    ring

theorem wordPos_nonneg (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) : 0 ≤ wordPos θ w := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have := digitShift_nonneg hθ d
    simp only [wordPos_cons]
    positivity

/-- The projection of a construction square lies in `[0, σ]`. -/
theorem wordPos_add_le (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) :
    wordPos θ w + sig θ / 4 ^ w.length ≤ sig θ := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have := digitShift_le hθ d
    simp only [wordPos_cons, List.length_cons, pow_succ]
    have h4 : (0 : ℝ) < 4 ^ w.length := by positivity
    have : sig θ / (4 ^ w.length * 4) = sig θ / 4 ^ w.length / 4 := by
      rw [div_div]
    rw [this]
    linarith

theorem wordPos_le (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) : wordPos θ w ≤ sig θ := by
  have := wordPos_add_le hθ w
  have : 0 ≤ sig θ / 4 ^ w.length := div_nonneg (sig_nonneg hθ) (by positivity)
  linarith

/-! ### Projected intervals -/

/-- The projection `[wordPos θ w, wordPos θ w + σ 4^{-|w|}]` of the square coded by `w`. -/
noncomputable def wordIval (θ : ℝ) (w : Word) : Set ℝ :=
  Icc (wordPos θ w) (wordPos θ w + sig θ / 4 ^ w.length)

theorem measurableSet_wordIval (θ : ℝ) (w : Word) : MeasurableSet (wordIval θ w) :=
  measurableSet_Icc

theorem isClosed_wordIval (θ : ℝ) (w : Word) : IsClosed (wordIval θ w) :=
  isClosed_Icc

theorem volume_wordIval (θ : ℝ) (w : Word) :
    volume (wordIval θ w) = ENNReal.ofReal (sig θ / 4 ^ w.length) := by
  simp [wordIval]

theorem wordPos_mem_wordIval (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) :
    wordPos θ w ∈ wordIval θ w :=
  ⟨le_rfl, le_add_of_nonneg_right (div_nonneg (sig_nonneg hθ) (by positivity))⟩

theorem wordIval_nonempty (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) : (wordIval θ w).Nonempty :=
  ⟨_, wordPos_mem_wordIval hθ w⟩

theorem wordIval_subset_Icc (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) :
    wordIval θ w ⊆ Icc 0 (sig θ) := by
  intro x hx
  exact ⟨(wordPos_nonneg hθ w).trans hx.1, hx.2.trans (wordPos_add_le hθ w)⟩

/-- The scaling rule: `x` lies in the projection of `u ++ v` iff its rescaled position relative
to `u` lies in the projection of `v`. -/
theorem mem_wordIval_append {x : ℝ} (u v : Word) :
    x ∈ wordIval θ (u ++ v) ↔ 4 ^ u.length * (x - wordPos θ u) ∈ wordIval θ v := by
  have ha : (0 : ℝ) < 4 ^ u.length := by positivity
  set y := 4 ^ u.length * (x - wordPos θ u) with hy
  have hx : x = wordPos θ u + y / 4 ^ u.length := by
    rw [hy]
    field_simp
    ring
  rw [hx]
  simp only [wordIval, wordPos_append, List.length_append, pow_add]
  have e1 : wordPos θ u + wordPos θ v / 4 ^ u.length + sig θ / (4 ^ u.length * 4 ^ v.length) =
      wordPos θ u + (wordPos θ v + sig θ / 4 ^ v.length) / 4 ^ u.length := by
    field_simp
    ring
  rw [e1, Set.mem_Icc, Set.mem_Icc, add_le_add_iff_left, add_le_add_iff_left,
    div_le_div_iff_of_pos_right ha, div_le_div_iff_of_pos_right ha]

theorem wordIval_append_subset (hθ : θ ∈ Icc 0 (π / 2)) (u v : Word) :
    wordIval θ (u ++ v) ⊆ wordIval θ u := by
  intro x hx
  rw [mem_wordIval_append] at hx
  have h := wordIval_subset_Icc hθ v hx
  have ha : (0 : ℝ) < 4 ^ u.length := by positivity
  set y := 4 ^ u.length * (x - wordPos θ u) with hy
  have hx : x = wordPos θ u + y / 4 ^ u.length := by
    rw [hy]
    field_simp
    ring
  rw [hx]
  refine ⟨le_add_of_nonneg_right (div_nonneg h.1 ha.le), ?_⟩
  have := div_le_div_of_nonneg_right h.2 ha.le
  linarith

/-- **Nesting**: the projection of a descendant lies in the projection of its ancestor. -/
theorem wordIval_subset_of_prefix (hθ : θ ∈ Icc 0 (π / 2)) {u w : Word} (h : u <+: w) :
    wordIval θ w ⊆ wordIval θ u := by
  obtain ⟨t, rfl⟩ := h
  exact wordIval_append_subset hθ u t

/-! ### Enlargements -/

/-- The concentric triple `[p - ℓ, p + 2ℓ]` of the projected interval `[p, p + ℓ]` of `w`. -/
noncomputable def tripleIval (θ : ℝ) (w : Word) : Set ℝ :=
  Icc (wordPos θ w - sig θ / 4 ^ w.length) (wordPos θ w + 2 * (sig θ / 4 ^ w.length))

theorem volume_tripleIval (θ : ℝ) (w : Word) :
    volume (tripleIval θ w) = ENNReal.ofReal (3 * (sig θ / 4 ^ w.length)) := by
  simp only [tripleIval, Real.volume_Icc]
  ring_nf

theorem measurableSet_tripleIval (θ : ℝ) (w : Word) : MeasurableSet (tripleIval θ w) :=
  measurableSet_Icc

theorem wordIval_subset_tripleIval_self (hθ : θ ∈ Icc 0 (π / 2)) (w : Word) :
    wordIval θ w ⊆ tripleIval θ w := by
  have : 0 ≤ sig θ / 4 ^ w.length := div_nonneg (sig_nonneg hθ) (by positivity)
  exact Icc_subset_Icc (by linarith) (by linarith)

/-- Two projected intervals of the same length with a common point: the first lies in the
concentric triple of the second. -/
theorem wordIval_subset_tripleIval {w w' : Word} (hl : w.length = w'.length) {y : ℝ}
    (hy : y ∈ wordIval θ w) (hy' : y ∈ wordIval θ w') : wordIval θ w ⊆ tripleIval θ w' := by
  simp only [wordIval, tripleIval, Set.mem_Icc, hl] at *
  exact Icc_subset_Icc (by linarith) (by linarith)

/-! ### Bridge to the frozen square codes -/

theorem leftEnd_succ {n : ℕ} (b : Fin (n + 1) → Bool) :
    leftEnd b = ((if b 0 then (3 : ℝ) else 0) + leftEnd fun i => b i.succ) / 4 := by
  simp only [leftEnd, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, zero_add, pow_one]
  rw [add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ, div_div]

@[simp]
theorem leftEnd_zero (b : Fin 0 → Bool) : leftEnd b = 0 := by
  simp [leftEnd]

/-- The projection of the corner of a square code is the left endpoint of its word. -/
theorem proj_corner {n : ℕ} (w : SqCode n) : proj θ (corner w) = wordPos θ (List.ofFn w) := by
  induction n with
  | zero => simp [proj, corner]
  | succ n ih =>
    rw [List.ofFn_succ, wordPos_cons, ← ih]
    simp only [proj, corner, leftEnd_succ, digitShift]
    split_ifs <;> ring

/-- The projection of an axis-parallel square `[a, a + s] × [b, b + s]` in a direction
`θ ∈ [0, π/2]` is `[π_θ(a, b), π_θ(a, b) + σ s]`. -/
theorem proj_image_Icc_prod (hθ : θ ∈ Icc 0 (π / 2)) (a b s : ℝ) :
    proj θ '' (Icc a (a + s) ×ˢ Icc b (b + s)) =
      Icc (proj θ (a, b)) (proj θ (a, b) + sig θ * s) := by
  have hc := cos_nonneg_of_mem_Icc hθ
  have hsn := sin_nonneg_of_mem_Icc hθ
  have hσ := sig_pos hθ
  ext z
  simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc, proj, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨hx1, hx2⟩, hy1, hy2⟩, rfl⟩
    have e1 := mul_le_mul_of_nonneg_right hx1 hc
    have e2 := mul_le_mul_of_nonneg_right hx2 hc
    have e3 := mul_le_mul_of_nonneg_right hy1 hsn
    have e4 := mul_le_mul_of_nonneg_right hy2 hsn
    unfold sig
    constructor <;> nlinarith
  · rintro ⟨hz1, hz2⟩
    set t := (z - (a * cos θ + b * sin θ)) / sig θ with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hσ.le
    have hts : t ≤ s := by
      rw [ht, div_le_iff₀ hσ]
      linarith
    refine ⟨a + t, b + t, ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    have : t * sig θ = z - (a * cos θ + b * sin θ) := by
      rw [ht]
      field_simp
    unfold sig at this
    linarith

theorem proj_image_square_eq (hθ : θ ∈ Icc 0 (π / 2)) {n : ℕ} (w : SqCode n) :
    proj θ '' square w = wordIval θ (List.ofFn w) := by
  rw [square, proj_image_Icc_prod hθ _ _ _, Prod.mk.eta, proj_corner, wordIval,
    List.length_ofFn, mul_one_div]

open Classical in
/-- The number of words of the finite family `S` whose projected interval contains `x`. -/
noncomputable def wcount (θ : ℝ) (S : Finset Word) (x : ℝ) : ℕ :=
  #{w ∈ S | x ∈ wordIval θ w}

/-- The multiplicity `f_n(x)` counts the words of length `n` whose interval contains `x`. -/
theorem count_eq_wcount (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) (x : ℝ) :
    count n θ x = wcount θ (words n) x := by
  classical
  unfold count words wcount
  rw [Finset.filter_image, Finset.card_image_of_injective _ List.ofFn_injective]
  congr 1
  ext w
  simp [proj_image_square_eq hθ]

theorem mem_cantorApprox_iff {n : ℕ} {x : ℝ} :
    x ∈ cantorApprox n ↔ ∃ b : Fin n → Bool, x ∈ Icc (leftEnd b) (leftEnd b + 1 / 4 ^ n) := by
  simp only [cantorApprox, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨w, hw, hx⟩
    refine ⟨fun j => decide (w j = 3), ?_⟩
    have : leftEnd (fun j => decide (w j = 3)) = ∑ j : Fin n, w j / 4 ^ ((j : ℕ) + 1) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases hw j with h | h <;> simp [h]
    rwa [this]
  · rintro ⟨b, hx⟩
    exact ⟨fun j => if b j then 3 else 0, fun j => by by_cases h : b j <;> simp [h], hx⟩

theorem mem_fourCorner_iff {n : ℕ} {p : ℝ × ℝ} :
    p ∈ fourCorner n ↔ ∃ w : SqCode n, p ∈ square w := by
  simp only [fourCorner, Set.mem_prod, mem_cantorApprox_iff, square, corner]
  constructor
  · rintro ⟨⟨b, hb⟩, b', hb'⟩
    exact ⟨fun j => (b j, b' j), hb, hb'⟩
  · rintro ⟨w, hw1, hw2⟩
    exact ⟨⟨_, hw1⟩, _, hw2⟩

/-- The projection of `K_n` is the union of the projected intervals of the depth-`n` words. -/
theorem proj_image_fourCorner_eq (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    proj θ '' fourCorner n = ⋃ w ∈ words n, wordIval θ w := by
  ext z
  simp only [Set.mem_image, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨w, hw⟩ := mem_fourCorner_iff.mp hp
    refine ⟨List.ofFn w, ofFn_mem_words w, ?_⟩
    rw [← proj_image_square_eq hθ]
    exact ⟨p, hw, rfl⟩
  · rintro ⟨l, hl, hz⟩
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hl
    rw [← proj_image_square_eq hθ] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨p, mem_fourCorner_iff.mpr ⟨w, hp⟩, rfl⟩

theorem projLength_eq (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    projLength n θ = (volume (⋃ w ∈ words n, wordIval θ w)).toReal := by
  rw [projLength, proj_image_fourCorner_eq hθ]

end Favard.Comb
