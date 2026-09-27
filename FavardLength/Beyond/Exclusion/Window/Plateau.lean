import FavardLength.Beyond.Exclusion.Cutoff
import FavardLength.Beyond.Exclusion.Density
import FavardLength.Beyond.Exclusion.Window.Cells

/-!
# Copies on the plateau of the cutoff

The lower bound (12) of Appendix G §4. Let `g = ∑_i f_{n,t}(· - β_i)` be flat on the middle half
of `[0, T]` at resolution `h = T/4^L`, `L ≥ 2`, with squared error `e`. The window
`W = [7T/16, 9T/16]` is the union of the `2·4^{L-2}` cells `7·4^{L-2} ≤ c < 9·4^{L-2}`, so by
Cauchy–Schwarz `∫_W g ≥ αT/8 - √(2·4^{L-2} e α² T h) ≥ αT(1/8 - √e)`. For `T ≥ 64/3` a copy
(of support radius `4/3 ≤ T/16`) meeting `W` has its centre `β_i` in `[3T/8, 5T/8]`, where
`χ(β_i/T) = 1`; as each copy has mass one, `∫_W g ≤ ∑_i χ(β_i/T)²`.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

/-- A copy meets the window `[7T/16, 9T/16]` only if its centre lies on the plateau of the
cutoff; hence its mass in the window is at most `χ(β/T)²`. -/
lemma integral_window_tailDensity_le {n : ℕ} {t T : ℝ} (ht : |t| ≤ 1) (hT : 64 / 3 ≤ T)
    (β : ℝ) : ∫ x in 7 * T / 16..9 * T / 16, tailDensity n t (x - β) ≤ cutoff (β / T) ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hint : Integrable fun x => tailDensity n t (x - β) :=
    (integrable_tailDensity n t).comp_sub_right β
  by_cases hβ : β / T ∈ Icc (3 / 8 : ℝ) (5 / 8)
  · rw [cutoff_eq_one hβ, one_pow, intervalIntegral.integral_of_le (by linarith)]
    calc ∫ x in Ioc (7 * T / 16) (9 * T / 16), tailDensity n t (x - β)
        ≤ ∫ x, tailDensity n t (x - β) :=
          setIntegral_le_integral hint
            (Filter.Eventually.of_forall fun x => tailDensity_nonneg n t _)
      _ = 1 := by
          rw [integral_sub_right_eq_self (fun x => tailDensity n t x), integral_tailDensity]
  · have hzero : EqOn (fun x => tailDensity n t (x - β)) (fun _ => (0 : ℝ))
        (uIcc (7 * T / 16) (9 * T / 16)) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      refine tailDensity_eq_zero ht n ?_
      rw [mem_Icc, not_and_or, not_le, not_le] at hβ
      rcases hβ with hβ | hβ
      · rw [div_lt_iff₀ hT0] at hβ
        rw [abs_of_pos (by linarith [hx.1])]
        linarith [hx.1]
      · rw [lt_div_iff₀ hT0] at hβ
        rw [abs_of_neg (by linarith [hx.2])]
        linarith [hx.2]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
    positivity

/-- **Copies on the plateau** (Appendix G (12)): for copies flat on the middle half of `[0, T]`
at resolution `T/4^L`, `L ≥ 2`, with squared error `e ≥ 0`, and `T ≥ 64/3`,
`αT(1/8 - √e) ≤ ∑_i χ(β_i/T)²`. -/
theorem plateau_count {n L m : ℕ} {t T α e : ℝ} (β : Fin m → ℝ) (ht : |t| ≤ 1)
    (hT : 64 / 3 ≤ T) (hL : 2 ≤ L) (hα : 0 ≤ α) (he : 0 ≤ e)
    (hflat : MiddleFlat (copySum n t β) T α e L) :
    α * T * (1 / 8 - √e) ≤ ∑ i, cutoff (β i / T) ^ 2 := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 4 ^ (L - 2) := ⟨_, rfl⟩
  have hN0 : 0 < (N : ℝ) := by rw [hN]; positivity
  have h4L : (4 : ℝ) ^ L = 16 * N := by
    rw [hN, show L = (L - 2) + 2 by omega, pow_add, Nat.add_sub_cancel]
    push_cast
    ring
  have h4L1 : 4 ^ (L - 1) = 4 * N := by
    rw [hN, show L - 1 = (L - 2) + 1 by omega, pow_succ]
    ring
  have hNh : (N : ℝ) * (T / 4 ^ L) = T / 16 := by
    rw [h4L]
    field_simp
  -- the deviations of the cell masses from the mean
  set d : ℕ → ℝ := fun c =>
    (∫ x in (c : ℝ) * (T / 4 ^ L)..((c : ℝ) + 1) * (T / 4 ^ L), copySum n t β x) -
      α * (T / 4 ^ L) with hd
  have hsub : Finset.Ico (7 * N) (9 * N) ⊆ Finset.Ico (4 ^ (L - 1)) (3 * 4 ^ (L - 1)) := by
    rw [h4L1]
    intro c
    simp only [Finset.mem_Ico]
    omega
  have hsq : ∑ c ∈ Finset.Ico (7 * N) (9 * N), d c ^ 2 ≤ e * α ^ 2 * T * (T / 4 ^ L) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => sq_nonneg _).trans hflat
  have hcard : ((Finset.Ico (7 * N) (9 * N)).card : ℝ) = 2 * N := by
    rw [Nat.card_Ico, show 9 * N - 7 * N = 2 * N by omega]
    push_cast
    ring
  have habs : ∑ c ∈ Finset.Ico (7 * N) (9 * N), |d c| ≤ α * T * √e := by
    refine sum_abs_le_of_card_mul_sum_sq_le _ _ (by positivity) ?_
    rw [hcard, mul_pow, mul_pow, Real.sq_sqrt he]
    have h0 : 0 ≤ e * α ^ 2 * T ^ 2 := by positivity
    calc 2 * (N : ℝ) * ∑ c ∈ Finset.Ico (7 * N) (9 * N), d c ^ 2
        ≤ 2 * N * (e * α ^ 2 * T * (T / 4 ^ L)) := by gcongr
      _ = e * α ^ 2 * T ^ 2 / 8 := by linear_combination (2 * e * α ^ 2 * T) * hNh
      _ ≤ α ^ 2 * T ^ 2 * e := by linarith
  -- the window as a union of cells
  have hcells := sum_integral_cells (f := copySum n t β)
    (fun a b => (integrable_copySum n t β).intervalIntegrable) (T / 4 ^ L)
    (show 7 * N ≤ 9 * N by omega)
  have e7 : ((7 * N : ℕ) : ℝ) * (T / 4 ^ L) = 7 * T / 16 := by
    push_cast
    linear_combination 7 * hNh
  have e9 : ((9 * N : ℕ) : ℝ) * (T / 4 ^ L) = 9 * T / 16 := by
    push_cast
    linear_combination 9 * hNh
  rw [e7, e9] at hcells
  have hlower : α * T / 8 - α * T * √e ≤ ∫ x in 7 * T / 16..9 * T / 16, copySum n t β x := by
    rw [← hcells]
    have hcell : ∀ c : ℕ, (∫ x in (c : ℝ) * (T / 4 ^ L)..((c : ℝ) + 1) * (T / 4 ^ L),
        copySum n t β x) = α * (T / 4 ^ L) + d c := fun c => by rw [hd]; ring
    simp_rw [hcell]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hneg : -∑ c ∈ Finset.Ico (7 * N) (9 * N), |d c| ≤
        ∑ c ∈ Finset.Ico (7 * N) (9 * N), d c := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun c _ => neg_abs_le _
    have h2N : 2 * (N : ℝ) * (α * (T / 4 ^ L)) = α * T / 8 := by
      rw [mul_comm α, ← mul_assoc, mul_assoc 2, hNh]
      ring
    linarith
  have hupper : ∫ x in 7 * T / 16..9 * T / 16, copySum n t β x ≤
      ∑ i, cutoff (β i / T) ^ 2 := by
    simp only [copySum]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      ((integrable_tailDensity n t).comp_sub_right (β i)).intervalIntegrable]
    exact Finset.sum_le_sum fun i _ => integral_window_tailDensity_le ht hT (β i)
  linarith

end Favard.Exclusion
