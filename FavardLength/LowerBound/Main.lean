import FavardLength.LowerBound.Overlap
import FavardLength.LowerBound.Pointwise
import FavardLength.Statements

/-!
# The elementary lower bound `Fav(K_n) ≥ c/n`

This proves `LowerBoundStatement` (manuscript, "An elementary proof of the upper bound on the
exponent"). By the symmetry reduction, `Fav(K_n) = (4/π) ∫_0^{π/4} λ(π_θ(K_n)) dθ`. For
`θ ∈ [0, π/4]` the pointwise bound (L1) `λ E ≥ 1` with `E ≥ 1` gives
`λ ≥ 1/E ≥ 2t - t² E` for every real `t`. Integrating and using the angular energy bound
`∫_0^{π/4} E ≤ M = 80 (n + 1)` (L2) with `t = 1/(2M)` yields
`Fav(K_n) ≥ (π - 1)/(π M) ≥ 1/(2M) ≥ 1/(320 n)`.
-/

open MeasureTheory Set Real

namespace Favard

namespace LowerBound

theorem intervalIntegrable_projLength (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (projLength n) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := √2) measure_Ioc_lt_top.ne
    (measurable_projLength n).aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (projLength_nonneg n θ)]
  exact projLength_le_sqrt_two n θ

/-- The finite-sum form of the energy. -/
noncomputable def pairEnergy (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ w : SqCode n, ∑ w' : SqCode n, overlap w w' θ

theorem continuous_pairEnergy (n : ℕ) : Continuous (pairEnergy n) :=
  continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun w' _ => continuous_overlap w w'

theorem energy_eq_pairEnergy {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    energy n θ = pairEnergy n θ :=
  energy_eq_sum_overlap hθ n

/-- The tangent-line bound `λ ≥ 1/E ≥ 2t - t² E` on `[0, π/2]`. -/
theorem two_mul_sub_le_projLength {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) (t : ℝ) :
    2 * t - t ^ 2 * pairEnergy n θ ≤ projLength n θ := by
  have h1 := one_le_projLength_mul_energy hθ n
  have h2 := one_le_energy hθ n
  rw [energy_eq_pairEnergy hθ n] at h1 h2
  set E := pairEnergy n θ
  set l := projLength n θ
  by_contra hlt
  push Not at hlt
  have hE : 0 < E := by linarith
  have : l * E < (2 * t - t ^ 2 * E) * E := mul_lt_mul_of_pos_right hlt hE
  nlinarith [sq_nonneg (t * E - 1)]

/-- The integral of the projection length over `[0, π/4]` is at least `(π - 1)/(4M)`. -/
theorem integral_projLength_ge (n : ℕ) :
    (π - 1) / (4 * (80 * (n + 1))) ≤ ∫ θ in (0)..(π / 4), projLength n θ := by
  set M : ℝ := 80 * (n + 1) with hM_def
  have hM : 0 < M := by positivity
  set t : ℝ := 1 / (2 * M) with ht
  have hpi : 0 ≤ π / 4 := by positivity
  have hmono : ∫ θ in (0)..(π / 4), (2 * t - t ^ 2 * pairEnergy n θ) ≤
      ∫ θ in (0)..(π / 4), projLength n θ :=
    intervalIntegral.integral_mono_on hpi
      ((continuous_const.sub (continuous_const.mul (continuous_pairEnergy n))).intervalIntegrable
        _ _)
      (intervalIntegrable_projLength n _ _) fun θ hθ =>
        two_mul_sub_le_projLength ⟨hθ.1, by linarith [hθ.2, pi_pos]⟩ n t
  have hval : ∫ θ in (0)..(π / 4), (2 * t - t ^ 2 * pairEnergy n θ) =
      π / 4 * (2 * t) - t ^ 2 * ∫ θ in (0)..(π / 4), pairEnergy n θ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (((continuous_pairEnergy n).intervalIntegrable _ _).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, sub_zero,
      smul_eq_mul]
  have hE : ∫ θ in (0)..(π / 4), pairEnergy n θ ≤ M := integral_sum_overlap_le n
  have hlow :
      (π - 1) / (4 * M) ≤ π / 4 * (2 * t) - t ^ 2 * ∫ θ in (0)..(π / 4), pairEnergy n θ := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hstep : π / 4 * (2 * t) - t ^ 2 * M ≤
        π / 4 * (2 * t) - t ^ 2 * ∫ θ in (0)..(π / 4), pairEnergy n θ := by
      nlinarith [mul_le_mul_of_nonneg_left hE ht2]
    refine le_trans (le_of_eq ?_) hstep
    rw [ht]
    field_simp
    ring
  linarith

end LowerBound

open LowerBound in
/-- **Elementary lower bound** (L1–L2): `Fav(K_n) ≥ 1/(320 n)` for `n ≥ 1`. -/
theorem lowerBound : LowerBoundStatement := by
  refine ⟨1 / 320, by norm_num, fun n hn => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := pi_pos
  have hpi2 := two_le_pi
  have hI := integral_projLength_ge n
  rw [favardLength_eq_quarter]
  have hM : (0 : ℝ) < 80 * (n + 1) := by positivity
  calc 1 / 320 / (n : ℝ) ≤ 1 / (2 * (80 * (n + 1))) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
    _ ≤ 4 / π * ((π - 1) / (4 * (80 * (n + 1)))) := by
        rw [show 4 / π * ((π - 1) / (4 * (80 * (n + 1)))) = (π - 1) / π / (80 * (n + 1)) by
          field_simp]
        rw [div_le_div_iff₀ (by positivity) hM]
        have hq : (1 : ℝ) / 2 ≤ (π - 1) / π := by
          rw [div_le_div_iff₀ (by norm_num) hpi]
          linarith
        nlinarith
    _ ≤ 4 / π * ∫ θ in (0)..(π / 4), projLength n θ := by gcongr

end Favard
