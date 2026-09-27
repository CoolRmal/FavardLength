import FavardLength.Beyond.Exclusion.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The smooth cutoff

Properties of `χ(x) = s(8x - 2) s(6 - 8x)` (Appendix G (9)): smoothness, `0 ≤ χ ≤ 1`,
`supp χ ⊆ (1/4, 3/4)`, `χ = 1` on `[3/8, 5/8]`, every derivative supported in `[1/4, 3/4]`,
continuous, integrable, and uniformly bounded up to any fixed order.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

lemma contDiff_cutoff {n : ℕ∞} : ContDiff ℝ n cutoff := by
  unfold cutoff
  have h1 : ContDiff ℝ n fun x : ℝ => Real.smoothTransition (8 * x - 2) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have h2 : ContDiff ℝ n fun x : ℝ => Real.smoothTransition (6 - 8 * x) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact h1.mul h2

lemma continuous_cutoff : Continuous cutoff :=
  (contDiff_cutoff (n := 0)).continuous

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 :=
  calc cutoff x ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma cutoff_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 4) : cutoff x = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma cutoff_eq_zero_of_ge {x : ℝ} (hx : 3 / 4 ≤ x) : cutoff x = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (x := 6 - 8 * x) (by linarith), mul_zero]

/-- The plateau: `χ = 1` on `[3/8, 5/8]`. -/
lemma cutoff_eq_one {x : ℝ} (hx : x ∈ Icc (3 / 8 : ℝ) (5 / 8)) : cutoff x = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le (by linarith [hx.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2]), one_mul]

lemma support_cutoff_subset : Function.support cutoff ⊆ Ioo (1 / 4 : ℝ) (3 / 4) := by
  intro x hx
  by_contra h
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact hx (cutoff_eq_zero_of_le h)
  · exact hx (cutoff_eq_zero_of_ge h)

/-- Every derivative of `χ` is supported in `[1/4, 3/4]`. -/
lemma support_iteratedDeriv_cutoff_subset (j : ℕ) :
    Function.support (iteratedDeriv j cutoff) ⊆ Icc (1 / 4 : ℝ) (3 / 4) := by
  induction j with
  | zero => rw [iteratedDeriv_zero]; exact support_cutoff_subset.trans Ioo_subset_Icc_self
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (support_deriv_subset).trans (closure_minimal ih isClosed_Icc)

lemma iteratedDeriv_cutoff_eq_zero (j : ℕ) {x : ℝ} (hx : x ∉ Icc (1 / 4 : ℝ) (3 / 4)) :
    iteratedDeriv j cutoff x = 0 :=
  Function.notMem_support.mp fun h => hx (support_iteratedDeriv_cutoff_subset j h)

lemma hasCompactSupport_iteratedDeriv_cutoff (j : ℕ) :
    HasCompactSupport (iteratedDeriv j cutoff) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => iteratedDeriv_cutoff_eq_zero j hx

lemma hasCompactSupport_cutoff : HasCompactSupport cutoff := by
  simpa using hasCompactSupport_iteratedDeriv_cutoff 0

lemma continuous_iteratedDeriv_cutoff (j : ℕ) : Continuous (iteratedDeriv j cutoff) :=
  (contDiff_cutoff (n := ⊤)).continuous_iteratedDeriv j (by exact_mod_cast le_top)

lemma integrable_iteratedDeriv_cutoff (j : ℕ) : Integrable (iteratedDeriv j cutoff) :=
  (continuous_iteratedDeriv_cutoff j).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_cutoff j)

/-- Uniform bounds for the derivatives of `χ` up to a fixed order. -/
lemma exists_bound_iteratedDeriv_cutoff (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ J, ∀ x, |iteratedDeriv j cutoff x| ≤ C := by
  have h : ∀ j, ∃ C : ℝ, ∀ x, ‖iteratedDeriv j cutoff x‖ ≤ C := fun j =>
    (continuous_iteratedDeriv_cutoff j).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv_cutoff j)
  choose C hC using h
  refine ⟨1 + ∑ j ∈ Finset.range (J + 1), |C j|, by positivity, fun j hj x => ?_⟩
  calc |iteratedDeriv j cutoff x| ≤ |C j| := (hC j x).trans (le_abs_self _)
    _ ≤ ∑ j ∈ Finset.range (J + 1), |C j| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_range.2 (by omega))
    _ ≤ 1 + ∑ j ∈ Finset.range (J + 1), |C j| := le_add_of_nonneg_left zero_le_one

end Favard.Exclusion
