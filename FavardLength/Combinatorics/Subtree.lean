import FavardLength.Combinatorics.Counting
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Self-similarity of subtrees (G10)

For a word `R` (a construction square), `subtreeMax N θ R x = h_R(x)` is the maximum over
generations `n ≤ N` of the number of depth-`n` descendants of `R` whose projection contains `x`.
The subtree below `R` is a translated copy of the whole construction scaled by `4^{-|R|}`:

* `wcount_desc_append`: the depth-`|R| + j` descendants of `R` containing `x` correspond to the
  depth-`j` words containing `4^{|R|}(x - wordPos θ R)`;
* `subtreeMax_eq`: `h_R(x) = F_{N-|R|}(4^{|R|}(x - wordPos θ R))` for `|R| ≤ N`;
* `integral_subtreeMax_sq_le` (G10): `∫ h_R² = 4^{-|R|} ∫ F_{N-|R|}² ≤ 4^{-|R|} ∫ F_N²`.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ}

/-- The subtree maximum `h_R(x) = max_{n ≤ N} #{depth-n descendants Q of R : x ∈ π_θ(Q)}`.
Generations `n < |R|` contribute nothing (there are no such descendants). -/
noncomputable def subtreeMax (N : ℕ) (θ : ℝ) (R : Word) (x : ℝ) : ℕ :=
  (Finset.range (N + 1)).sup fun n => wcount θ (desc R n) x

theorem wcount_desc_le_subtreeMax {N n : ℕ} (h : n ≤ N) (θ : ℝ) (R : Word) (x : ℝ) :
    wcount θ (desc R n) x ≤ subtreeMax N θ R x :=
  Finset.le_sup (f := fun n => wcount θ (desc R n) x)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

theorem subtreeMax_le_iff {N k : ℕ} {R : Word} {x : ℝ} :
    subtreeMax N θ R x ≤ k ↔ ∀ n ≤ N, wcount θ (desc R n) x ≤ k := by
  simp [subtreeMax, Finset.sup_le_iff]

theorem exists_wcount_eq_subtreeMax (N : ℕ) (θ : ℝ) (R : Word) (x : ℝ) :
    ∃ n ≤ N, wcount θ (desc R n) x = subtreeMax N θ R x := by
  obtain ⟨n, hn, h⟩ := Finset.exists_mem_eq_sup (Finset.range (N + 1))
    Finset.nonempty_range_add_one (fun n => wcount θ (desc R n) x)
  exact ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), h.symm⟩

theorem wcount_desc_le_count (hθ : θ ∈ Icc 0 (π / 2)) (R : Word) (n : ℕ) (x : ℝ) :
    wcount θ (desc R n) x ≤ count n θ x :=
  wcount_le_count hθ (desc_subset_words R n) x

/-- The subtree maximum is at most the full running maximum. -/
theorem subtreeMax_le_maxCount (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) (R : Word) (x : ℝ) :
    subtreeMax N θ R x ≤ maxCount N θ x :=
  subtreeMax_le_iff.mpr fun n hn =>
    (wcount_desc_le_count hθ R n x).trans (count_le_maxCount hn θ x)

theorem measurable_subtreeMax (N : ℕ) (θ : ℝ) (R : Word) : Measurable (subtreeMax N θ R) :=
  measurable_range_sup (fun n => measurable_wcount θ (desc R n)) N

theorem measurable_subtreeMax_real (N : ℕ) (θ : ℝ) (R : Word) :
    Measurable fun x => (subtreeMax N θ R x : ℝ) :=
  measurable_from_nat.comp (measurable_subtreeMax N θ R)

/-- **Self-similarity of the subtree counts**: the depth-`|R| + j` descendants of `R` containing
`x` correspond to the depth-`j` words containing `4^{|R|}(x - wordPos θ R)`. -/
theorem wcount_desc_append (hθ : θ ∈ Icc 0 (π / 2)) (R : Word) (j : ℕ) (x : ℝ) :
    wcount θ (desc R (R.length + j)) x = count j θ (4 ^ R.length * (x - wordPos θ R)) := by
  classical
  rw [count_eq_wcount hθ, desc_eq_image (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  unfold wcount
  rw [Finset.filter_image, Finset.card_image_of_injective _ fun _ _ h => List.append_cancel_left h]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  rw [mem_wordIval_append]

/-- **Self-similarity (G10)**, pointwise: `h_R(x) = F_{N-|R|}(4^{|R|}(x - wordPos θ R))`. -/
theorem subtreeMax_eq (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {R : Word} (hR : R.length ≤ N)
    (x : ℝ) :
    subtreeMax N θ R x = maxCount (N - R.length) θ (4 ^ R.length * (x - wordPos θ R)) := by
  refine le_antisymm (subtreeMax_le_iff.mpr fun n hn => ?_) (maxCount_le_iff.mpr fun j hj => ?_)
  · by_cases hnR : R.length ≤ n
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnR
      rw [wcount_desc_append hθ]
      exact count_le_maxCount (by omega) θ _
    · push Not at hnR
      have : desc R n = ∅ := by
        ext v
        simp only [mem_desc, Finset.notMem_empty, iff_false, not_and]
        intro hv hRv
        have := hRv.length_le
        omega
      rw [this, wcount_empty]
      exact Nat.zero_le _
  · rw [← wcount_desc_append hθ]
    exact wcount_desc_le_subtreeMax (by omega) θ R x

theorem integrable_subtreeMax_sq (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) (R : Word) :
    Integrable fun x => (subtreeMax N θ R x : ℝ) ^ 2 := by
  refine (integrable_maxCount_pow hθ N two_ne_zero).mono'
    ((measurable_subtreeMax_real N θ R).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact_mod_cast subtreeMax_le_maxCount hθ N R x

/-- **(G10)**, exact form: `∫ h_R² = 4^{-|R|} ∫ F_{N-|R|}²`. -/
theorem integral_subtreeMax_sq (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {R : Word}
    (hR : R.length ≤ N) :
    ∫ x, (subtreeMax N θ R x : ℝ) ^ 2 =
      1 / 4 ^ R.length * ∫ y, (maxCount (N - R.length) θ y : ℝ) ^ 2 := by
  set a : ℝ := 4 ^ R.length with ha
  have ha0 : 0 < a := by positivity
  set F : ℝ → ℝ := fun y => (maxCount (N - R.length) θ y : ℝ) ^ 2
  have h1 : (fun x => (subtreeMax N θ R x : ℝ) ^ 2) =
      fun x => (fun z => F (z - a * wordPos θ R)) (a * x) := by
    ext x
    simp only [F, subtreeMax_eq hθ hR x, ha, mul_sub]
  rw [h1, Measure.integral_comp_mul_left (fun z => F (z - a * wordPos θ R)) a,
    integral_sub_right_eq_self F (a * wordPos θ R), abs_of_pos (inv_pos.mpr ha0), smul_eq_mul,
    one_div]

/-- **(G10)**: `‖h_R‖₂² ≤ ℓ(R) ‖F_N‖₂²` with `ℓ(R) = 4^{-|R|}`. -/
theorem integral_subtreeMax_sq_le (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {R : Word}
    (hR : R.length ≤ N) :
    ∫ x, (subtreeMax N θ R x : ℝ) ^ 2 ≤ 1 / 4 ^ R.length * ∫ y, (maxCount N θ y : ℝ) ^ 2 := by
  rw [integral_subtreeMax_sq hθ hR]
  gcongr
  · exact integrable_maxCount_pow hθ _ two_ne_zero
  · exact integrable_maxCount_pow hθ _ two_ne_zero
  · intro y
    dsimp only
    gcongr
    exact_mod_cast maxCount_mono (Nat.sub_le N R.length) θ y

end Favard.Comb
