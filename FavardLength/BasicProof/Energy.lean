import FavardLength.BasicProof.Cantor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Projected multiplicity and energy

The multiplicity `count n θ x` is the finite sum of the indicators of the projected squares
`π_θ(Q_w)`; its square is the double sum of the indicators of the pairwise intersections. This
gives measurability and integrability, the total mass `∫ f_n = cos θ + sin θ`, and the overlap
formula for the energy.
-/

open MeasureTheory Set Real

namespace Favard.BasicProof

theorem measurableSet_proj_image_square (θ : ℝ) {n : ℕ} (w : SqCode n) :
    MeasurableSet (proj θ '' square w) :=
  (isCompact_proj_image_square θ w).isClosed.measurableSet

theorem volume_proj_image_square_ne_top (θ : ℝ) {n : ℕ} (w : SqCode n) :
    volume (proj θ '' square w) ≠ ⊤ :=
  (isCompact_proj_image_square θ w).measure_lt_top.ne

theorem count_le (n : ℕ) (θ x : ℝ) : count n θ x ≤ 4 ^ n := by
  unfold count
  refine (Finset.card_le_univ _).trans ?_
  simp

/-- The multiplicity is the sum of the indicators of the projected squares. -/
theorem count_eq_sum (n : ℕ) (θ x : ℝ) :
    (count n θ x : ℝ) = ∑ w : SqCode n, (proj θ '' square w).indicator 1 x := by
  classical
  rw [count, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Set.indicator_apply, Pi.one_apply]

/-- The squared multiplicity is the sum over ordered pairs of squares of the indicators of the
intersections of their projections. -/
theorem count_sq_eq (n : ℕ) (θ x : ℝ) :
    (count n θ x : ℝ) ^ 2 = ∑ w : SqCode n, ∑ w' : SqCode n,
      (proj θ '' square w ∩ proj θ '' square w').indicator 1 x := by
  rw [count_eq_sum, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [Set.inter_indicator_one]
  rfl

theorem measurable_count (n : ℕ) (θ : ℝ) : Measurable (fun x => (count n θ x : ℝ)) := by
  simp_rw [count_eq_sum]
  exact Finset.measurable_sum _ fun w _ =>
    measurable_one.indicator (measurableSet_proj_image_square θ w)

theorem integrable_indicator_one_of_ne_top {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ⊤) : Integrable (s.indicator (1 : ℝ → ℝ)) :=
  (integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator hs

theorem integrable_indicator_proj_image_square (θ : ℝ) {n : ℕ} (w : SqCode n) :
    Integrable ((proj θ '' square w).indicator (1 : ℝ → ℝ)) :=
  integrable_indicator_one_of_ne_top (measurableSet_proj_image_square θ w)
    (volume_proj_image_square_ne_top θ w)

theorem integrable_indicator_proj_image_square_inter (θ : ℝ) {n : ℕ} (w w' : SqCode n) :
    Integrable ((proj θ '' square w ∩ proj θ '' square w').indicator (1 : ℝ → ℝ)) :=
  integrable_indicator_one_of_ne_top
    ((measurableSet_proj_image_square θ w).inter (measurableSet_proj_image_square θ w'))
    (measure_ne_top_of_subset inter_subset_left (volume_proj_image_square_ne_top θ w))

theorem integrable_count_sq (n : ℕ) (θ : ℝ) :
    Integrable (fun x => (count n θ x : ℝ) ^ 2) := by
  simp_rw [count_sq_eq]
  exact integrable_finsetSum _ fun w _ => integrable_finsetSum _ fun w' _ =>
    integrable_indicator_proj_image_square_inter θ w w'

/-- For `θ ∈ [0, π/2]`, the total multiplicity mass is `σ = cos θ + sin θ`. -/
theorem integral_count {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    ∫ x, (count n θ x : ℝ) = cos θ + sin θ := by
  have hσ : 0 ≤ cos θ + sin θ := add_nonneg (cos_nonneg_of_mem_Icc_zero_pi_div_two hθ)
    (sin_nonneg_of_mem_Icc_zero_pi_div_two hθ)
  simp_rw [count_eq_sum]
  rw [integral_finsetSum _ fun w _ => integrable_indicator_proj_image_square θ w]
  have h : ∀ w : SqCode n,
      ∫ x, (proj θ '' square w).indicator 1 x = (cos θ + sin θ) / 4 ^ n := by
    intro w
    rw [integral_indicator_one (measurableSet_proj_image_square θ w), proj_image_square hθ,
      Real.volume_real_Icc_of_le (le_add_of_nonneg_right (div_nonneg hσ (by positivity))),
      add_sub_cancel_left]
  rw [Finset.sum_congr rfl fun w _ => h w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  push_cast
  field_simp

/-- The overlap of two intervals of the same length `ℓ ≥ 0`. -/
theorem min_add_sub_max (a b ℓ : ℝ) : min (a + ℓ) (b + ℓ) - max a b = ℓ - |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left (by linarith), max_eq_right h, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonneg (by linarith)]
    ring

/-- The energy is the sum over ordered pairs of squares of the overlaps of their projections. -/
theorem energy_eq_sum_overlap {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    energy n θ = ∑ w : SqCode n, ∑ w' : SqCode n,
      max 0 ((cos θ + sin θ) / 4 ^ n - |proj θ (corner w) - proj θ (corner w')|) := by
  unfold energy
  simp_rw [count_sq_eq]
  rw [integral_finsetSum _ fun w _ => integrable_finsetSum _ fun w' _ =>
    integrable_indicator_proj_image_square_inter θ w w']
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [integral_finsetSum _ fun w' _ => integrable_indicator_proj_image_square_inter θ w w']
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [integral_indicator_one
      ((measurableSet_proj_image_square θ w).inter (measurableSet_proj_image_square θ w')),
    proj_image_square hθ, proj_image_square hθ, Icc_inter_Icc, Real.volume_real_Icc,
    min_add_sub_max, max_comm]

theorem energy_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ energy n θ :=
  integral_nonneg fun _ => sq_nonneg _

end Favard.BasicProof
