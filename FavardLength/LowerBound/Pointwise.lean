import FavardLength.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The pointwise inequality `λ(π_θ(K_n)) · E_n(θ) ≥ 1` (L1)

For `θ ∈ [0, π/2]` the multiplicity function `f = count n θ` has integral
`σ = cos θ + sin θ ≥ 1` and is supported on `S = π_θ(K_n)`. The Cauchy–Schwarz inequality
`σ² ≤ λ(S) ∫ f²` is proved through the pointwise AM–GM bound `2f ≤ f²/E + E 1_S`, where
`E = ∫ f²` is the energy; integrating gives `2σ ≤ 1 + E λ(S)`, hence `λ(S) E ≥ 1`.
-/

open MeasureTheory Set Real

namespace Favard.LowerBound

/-- On `[0, π/2]`, `σ = cos θ + sin θ ≥ 1`. -/
theorem one_le_cos_add_sin {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) : 1 ≤ cos θ + sin θ := by
  have hc := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  have hs := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
  nlinarith [sin_sq_add_cos_sq θ, cos_le_one θ, sin_le_one θ]

theorem continuous_proj (θ : ℝ) : Continuous (proj θ) := by
  unfold proj
  fun_prop

theorem measurableSet_proj_image_fourCorner (n : ℕ) (θ : ℝ) :
    MeasurableSet (proj θ '' fourCorner n) :=
  ((isCompact_fourCorner n).image (continuous_proj θ)).isClosed.measurableSet

/-- The multiplicity function is supported on the projection of `K_n`. -/
theorem mem_proj_image_of_count_ne_zero {n : ℕ} {θ x : ℝ} (h : count n θ x ≠ 0) :
    x ∈ proj θ '' fourCorner n := by
  classical
  unfold count at h
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.1 h
  have hx : x ∈ proj θ '' square w := (Finset.mem_filter.1 hw).2
  rw [fourCorner_eq_iUnion]
  exact image_mono (subset_iUnion _ w) hx

/-- The multiplicity function is integrable. -/
theorem integrable_count (n : ℕ) (θ : ℝ) : Integrable fun x => (count n θ x : ℝ) := by
  refine (integrable_count_sq n θ).mono' (measurable_count n θ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rcases Nat.eq_zero_or_pos (count n θ x) with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ count n θ x := by exact_mod_cast h
    nlinarith

/-- For `θ ∈ [0, π/2]`, the energy is at least `σ ≥ 1`. -/
theorem one_le_energy {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) : 1 ≤ energy n θ := by
  have hff : ∀ x, (count n θ x : ℝ) ≤ (count n θ x : ℝ) ^ 2 := by
    intro x
    rcases Nat.eq_zero_or_pos (count n θ x) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ count n θ x := by exact_mod_cast h
      nlinarith
  calc (1 : ℝ) ≤ cos θ + sin θ := one_le_cos_add_sin hθ
    _ = ∫ x, (count n θ x : ℝ) := (integral_count hθ n).symm
    _ ≤ ∫ x, (count n θ x : ℝ) ^ 2 :=
        integral_mono (integrable_count n θ) (integrable_count_sq n θ) hff
    _ = energy n θ := rfl

/-- **(L1)**: for `θ ∈ [0, π/2]`, `λ(π_θ(K_n)) · E_n(θ) ≥ 1`. -/
theorem one_le_projLength_mul_energy {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    1 ≤ projLength n θ * energy n θ := by
  set f : ℝ → ℝ := fun x => (count n θ x : ℝ) with hf_def
  set S := proj θ '' fourCorner n with hS
  set E := energy n θ with hE_def
  have hE1 : 1 ≤ E := one_le_energy hθ n
  have hEpos : 0 < E := by linarith
  have hSm : MeasurableSet S := measurableSet_proj_image_fourCorner n θ
  have hSfin : volume S ≠ ⊤ := volume_proj_image_fourCorner_ne_top n θ
  have hf : Integrable f := integrable_count n θ
  have hf2 : Integrable fun x => f x ^ 2 := integrable_count_sq n θ
  have hind : Integrable (S.indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
  -- pointwise AM–GM
  have hpt : ∀ x, 2 * f x ≤ f x ^ 2 / E + E * S.indicator 1 x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one, div_add' _ _ _ hEpos.ne',
        le_div_iff₀ hEpos]
      nlinarith [sq_nonneg (f x - E)]
    · have h0 : f x = 0 := by
        by_contra h0
        exact hx (mem_proj_image_of_count_ne_zero fun hc => h0 (by simp [hf_def, hc]))
      rw [indicator_of_notMem hx, h0]
      simp
  have hint := integral_mono (hf.const_mul 2) ((hf2.div_const E).add (hind.const_mul E)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, integral_add (hf2.div_const E) (hind.const_mul E), integral_div,
    integral_const_mul, integral_indicator_one hSm] at hint
  have hσ : ∫ x, f x = cos θ + sin θ := integral_count hθ n
  have hσ1 := one_le_cos_add_sin hθ
  have hE : ∫ x, f x ^ 2 = E := rfl
  have hlen : volume.real S = projLength n θ := rfl
  rw [hσ, hE, hlen, div_self hEpos.ne'] at hint
  linarith

end Favard.LowerBound
