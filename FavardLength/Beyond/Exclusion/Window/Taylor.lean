import FavardLength.Beyond.Exclusion.Window.Basic

/-!
# The Taylor expansion of the window transform

Appendix G (14)–(15). Writing the window transform of `g = ∑_i f_{n,t}(· - β_i)` copy by copy,
`I(ξ) = ∑_i ∫ χ((β_i + y)/T) e^{-2πiξ(β_i + y)} f_{n,t}(y) dy`, and expanding
`χ(β_i/T + y/T)` by Taylor's theorem to order `J` (`Exclusion.cutoff_taylor`), the polynomial
part integrates to the expanded window transform `expandedWindow J n t T ξ β`, whose `j`-th
term is `M_j(ξ)/(j! T^j) ∑_i χ^{(j)}(β_i/T) e^{-2πiξβ_i}`. Since each copy is a probability
density supported in `|y| ≤ 4/3`, the remainder is at most `C (4/(3T))^{J+1}` per copy, so
`‖I(ξ) - expandedWindow‖ ≤ C' m / T^{J+1}`.
-/

open MeasureTheory Set Real
open scoped Nat

namespace Favard.Exclusion

/-- The transform of one copy, recentred at its centre. -/
lemma integral_windowTest_mul_tailDensity_sub (n : ℕ) (t T ξ β : ℝ) :
    ∫ x, windowTest T ξ x * (tailDensity n t (x - β) : ℂ) =
      ∫ y, windowTest T ξ (y + β) * (tailDensity n t y : ℂ) := by
  have := integral_sub_right_eq_self (μ := volume)
    (fun y => windowTest T ξ (y + β) * (tailDensity n t y : ℂ)) β
  simpa only [sub_add_cancel] using this

/-- The window transform as a sum over the copies. -/
lemma windowTransform_eq_sum {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) (T ξ : ℝ) {m : ℕ}
    (β : Fin m → ℝ) :
    windowTransform n t T ξ β =
      ∑ i, ∫ y, windowTest T ξ (y + β i) * (tailDensity n t y : ℂ) := by
  rw [windowTransform]
  simp_rw [copySum, Complex.ofReal_sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => ?_]
  · exact Finset.sum_congr rfl fun i _ => integral_windowTest_mul_tailDensity_sub n t T ξ (β i)
  · have := (integrable_mul_tailDensity ht n ((continuous_windowTest T ξ).comp
      (show Continuous fun y : ℝ => y + β i by fun_prop))).comp_sub_right (β i)
    simpa only [Function.comp_apply, sub_add_cancel] using this

/-- **Taylor remainder for one copy** (Appendix G (15)): if the Taylor polynomial of order `J`
approximates `χ` with remainder `C|s|^{J+1}`, then the transform of one copy differs from its
expansion by at most `C (4/(3T))^{J+1}`. -/
lemma norm_copy_sub_taylor_le {J n : ℕ} {t T C : ℝ} (ht : |t| ≤ 1) (hT : 0 < T)
    (hC : ∀ u s : ℝ, |cutoff (u + s) -
      ∑ j ∈ Finset.range (J + 1), iteratedDeriv j cutoff u * s ^ j / j !| ≤ C * |s| ^ (J + 1))
    (ξ β : ℝ) :
    ‖(∫ y, windowTest T ξ (y + β) * (tailDensity n t y : ℂ)) -
      ∑ j ∈ Finset.range (J + 1), tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) *
        (((iteratedDeriv j cutoff (β / T) : ℝ) : ℂ) *
          Complex.exp (↑(-2 * π * ξ * β) * Complex.I))‖ ≤
      C * (4 / 3 / T) ^ (J + 1) := by
  set eβ := Complex.exp (↑(-2 * π * ξ * β) * Complex.I)
  set e : ℝ → ℂ := fun y => Complex.exp (↑(-2 * π * ξ * y) * Complex.I) with he_def
  set k : ℕ → ℂ := fun j =>
    ((iteratedDeriv j cutoff (β / T) : ℝ) : ℂ) * eβ / ((j ! : ℂ) * (T : ℂ) ^ j) with hk
  set G : ℕ → ℝ → ℂ := fun j y => (y : ℂ) ^ j * e y * (tailDensity n t y : ℂ) * k j with hG
  have hGi : ∀ j, Integrable (G j) := fun j =>
    (integrable_mul_tailDensity ht n (g := fun y => (y : ℂ) ^ j * e y)
      (by simp only [he_def]; fun_prop)).mul_const _
  have hterm : ∀ j, tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) *
      (((iteratedDeriv j cutoff (β / T) : ℝ) : ℂ) * eβ) = ∫ y, G j y := by
    intro j
    simp only [hG, hk, he_def]
    rw [integral_mul_const, tailMoment]
    ring
  have hφi : Integrable fun y => windowTest T ξ (y + β) * (tailDensity n t y : ℂ) :=
    integrable_mul_tailDensity ht n ((continuous_windowTest T ξ).comp
      (show Continuous fun y : ℝ => y + β by fun_prop))
  simp_rw [hterm]
  rw [← integral_finsetSum _ fun j _ => hGi j, ← integral_sub hφi (integrable_finsetSum _
    fun j _ => hGi j)]
  -- the pointwise Taylor remainder
  set D : ℝ → ℝ := fun y => cutoff (β / T + y / T) -
    ∑ j ∈ Finset.range (J + 1), iteratedDeriv j cutoff (β / T) * (y / T) ^ j / j ! with hD
  have hpt : ∀ y, windowTest T ξ (y + β) * (tailDensity n t y : ℂ) -
      ∑ j ∈ Finset.range (J + 1), G j y = (D y : ℂ) * e (y + β) * (tailDensity n t y : ℂ) := by
    intro y
    have he : e (y + β) = e y * eβ := by
      simp only [he_def, eβ]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hw : windowTest T ξ (y + β) = (cutoff (β / T + y / T) : ℂ) * (e y * eβ) := by
      rw [← he, show β / T + y / T = (y + β) / T by ring]
      rfl
    rw [hw, he]
    simp only [hD, hG, hk]
    push_cast
    rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  have hbd : ∀ y, ‖(D y : ℂ) * e (y + β) * (tailDensity n t y : ℂ)‖ ≤
      C * (4 / 3 / T) ^ (J + 1) * tailDensity n t y := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (tailDensity_nonneg n t y)]
    have hey : ‖e (y + β)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [hey, mul_one]
    by_cases hy : |y| ≤ 4 / 3
    · refine mul_le_mul_of_nonneg_right ((hC _ _).trans ?_) (tailDensity_nonneg n t y)
      have hC0 : 0 ≤ C := by
        have := (abs_nonneg _).trans (hC 0 1)
        simpa using this
      gcongr
      rw [abs_div, abs_of_pos hT]
      gcongr
    · rw [tailDensity_eq_zero ht n (not_le.1 hy), mul_zero, mul_zero]
  refine (norm_integral_le_of_norm_le ((integrable_tailDensity n t).const_mul _)
    (Filter.Eventually.of_forall hbd)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_tailDensity, mul_one]

/-- **The window expansion** (Appendix G (14)–(15)): for every Taylor order `J` there is `C`
with `‖I(ξ) - expandedWindow J n t T ξ β‖ ≤ C m / T^{J+1}` for `|t| ≤ 1` and `T > 0`. -/
theorem exists_norm_windowTransform_sub_expandedWindow_le (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (t T ξ : ℝ) (β : Fin m → ℝ), |t| ≤ 1 → 0 < T →
      ‖windowTransform n t T ξ β - expandedWindow J n t T ξ β‖ ≤ C * m / T ^ (J + 1) := by
  obtain ⟨C, hC, htay⟩ := cutoff_taylor J
  refine ⟨C * (4 / 3) ^ (J + 1), by positivity, fun n m t T ξ β ht hT => ?_⟩
  have hEW : expandedWindow J n t T ξ β = ∑ i, ∑ j ∈ Finset.range (J + 1),
      tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) *
        (((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
          Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)) := by
    rw [expandedWindow, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [windowTransform_eq_sum ht, hEW, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i, ‖(∫ y, windowTest T ξ (y + β i) * (tailDensity n t y : ℂ)) -
        ∑ j ∈ Finset.range (J + 1), tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) *
          (((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
            Complex.exp (↑(-2 * π * ξ * β i) * Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, C * (4 / 3 / T) ^ (J + 1) :=
        Finset.sum_le_sum fun i _ => norm_copy_sub_taylor_le ht hT htay ξ (β i)
    _ = C * (4 / 3) ^ (J + 1) * m / T ^ (J + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
        ring

end Favard.Exclusion
