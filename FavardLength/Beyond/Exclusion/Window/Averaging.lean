import FavardLength.Beyond.Exclusion.Window.Basic
import FavardLength.Beyond.Exclusion.Window.Cells

/-!
# The flat-block upper bound for the window transform

Appendix G (18)–(19). Let `g = ∑_i f_{n,t}(· - β_i)` be flat on the middle half of `[0, T]` at
resolution `h = T/4^L` with squared error `e ≤ 1`, and let `φ(x) = χ(x/T) e^{-2πiξx}`, which is
supported in `[T/4, 3T/4]`, bounded by one, and `(C/T + 2πξ)`-Lipschitz. On each of the
`2·4^{L-1}` cells `[c h, (c + 1) h]` of the middle half, replacing `g` by the constant `α` costs
at most `M (∫_c g + α h) + |∫_c g - α h|` with `M = (C/T + 2πξ) h`
(`Exclusion.norm_integral_mul_sub_le`); by Cauchy–Schwarz the cell deviations sum to at most
`αT√e`. Hence `|I(ξ) - α ∫ φ| ≤ M αT + (M + 1) αT√e`, and `α ∫ φ = αT χ̂(Tξ)` is at most
`C αT (Tξ)^{-J}`. For `ξ ≥ 1/4` and `T ≥ 64/3`, `M ≤ C' h ξ`, so
`|I(ξ)| ≤ C αT (√e + hξ + (Tξ)^{-J})`.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace Favard.Exclusion

/-- **Flat-block upper bound** (Appendix G (18)–(19)): for copies flat on the middle half of
`[0, T]` at resolution `T/4^L` with squared error `0 ≤ e ≤ 1`, `T ≥ 64/3` and `ξ ≥ 1/4`,
`|I(ξ)| ≤ C αT (√e + (T/4^L) ξ + (Tξ)^{-J})`. -/
theorem exists_norm_windowTransform_le (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n L m : ℕ) (t T α e ξ : ℝ) (β : Fin m → ℝ),
      64 / 3 ≤ T → 1 ≤ L → 0 ≤ α → 0 ≤ e → e ≤ 1 → 1 / 4 ≤ ξ →
      MiddleFlat (copySum n t β) T α e L →
        ‖windowTransform n t T ξ β‖ ≤ C * α * T * (√e + T / 4 ^ L * ξ + 1 / (T * ξ) ^ J) := by
  obtain ⟨C₁, hC₁, hlip⟩ := exists_norm_windowTest_sub_le
  obtain ⟨C₂, hC₂, hF⟩ := norm_fourier_cutoff_le J
  refine ⟨1 + 2 * (C₁ + 8) + C₂, by positivity,
    fun n L m t T α e ξ β hT hL hα he he1 hξ hflat => ?_⟩
  have hT0 : 0 < T := by linarith
  have hξ0 : 0 < ξ := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 4 ^ (L - 1) := ⟨_, rfl⟩
  have ha0 : 0 < (a : ℝ) := by rw [ha]; positivity
  have h4L : (4 : ℝ) ^ L = 4 * a := by
    rw [ha, show L = (L - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel]
    push_cast
    ring
  set h : ℝ := T / 4 ^ L with hh
  have hh0 : 0 < h := by positivity
  have hah : (a : ℝ) * h = T / 4 := by
    rw [hh, h4L]
    field_simp
  set g := copySum n t β with hg
  set φ := windowTest T ξ with hφ
  set M : ℝ := (C₁ / T + 2 * π * ξ) * h with hM
  have hM0 : 0 ≤ M := by positivity
  set d : ℕ → ℝ := fun c => (∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, g x) - α * h with hd
  have hgi : Integrable g := integrable_copySum n t β
  have hφg_int : ∀ u v : ℝ, IntervalIntegrable (fun x => φ x * (g x : ℂ)) volume u v :=
    fun u v => hgi.ofReal.intervalIntegrable.continuousOn_mul
      (continuous_windowTest T ξ).continuousOn
  have hφ_int : ∀ u v : ℝ, IntervalIntegrable φ volume u v :=
    fun u v => (continuous_windowTest T ξ).intervalIntegrable u v
  have e3 : ((3 * a : ℕ) : ℝ) * h = 3 * T / 4 := by
    push_cast
    linear_combination 3 * hah
  -- localization to the cells of the middle half
  have hI : windowTransform n t T ξ β = ∑ c ∈ Finset.Ico a (3 * a),
      ∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, φ x * (g x : ℂ) := by
    rw [sum_integral_cells hφg_int h (by omega), hah, e3]
    exact integral_eq_intervalIntegral_of_eq_zero (by linarith) fun x hx => by
      rw [windowTest_eq_zero hT0 hx, zero_mul]
  have hΦ : ∫ x, φ x = ∑ c ∈ Finset.Ico a (3 * a),
      ∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, φ x := by
    rw [sum_integral_cells hφ_int h (by omega), hah, e3]
    exact integral_eq_intervalIntegral_of_eq_zero (by linarith) fun x hx =>
      windowTest_eq_zero hT0 hx
  -- averaging on each cell
  have hcell : ∀ c ∈ Finset.Ico a (3 * a),
      ‖(∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, φ x * (g x : ℂ)) -
        (α : ℂ) * ∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, φ x‖ ≤
      M * (2 * α * h + |d c|) + |d c| := by
    intro c _
    have hab : (c : ℝ) * h ≤ ((c : ℝ) + 1) * h := by nlinarith
    have hosc : ∀ x ∈ Icc ((c : ℝ) * h) (((c : ℝ) + 1) * h), ‖φ x - φ (c * h)‖ ≤ M := by
      intro x hx
      refine (hlip T ξ x _ hT0 hξ0.le).trans ?_
      rw [hM]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    have := norm_integral_mul_sub_le hab (continuous_windowTest T ξ)
      (norm_windowTest_le_one _ _ _) hosc hgi (copySum_nonneg n t β) hα
    rw [show ((c : ℝ) + 1) * h - c * h = h by ring] at this
    refine this.trans ?_
    have hdc : (∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, g x) = α * h + d c := by
      rw [hd]
      ring
    rw [hdc, show α * h + d c - α * h = d c by ring]
    refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hM0) _
    linarith [le_abs_self (d c)]
  -- Cauchy–Schwarz for the cell deviations
  have hsq : ∑ c ∈ Finset.Ico a (3 * a), d c ^ 2 ≤ e * α ^ 2 * T * h := by
    rw [ha]
    exact hflat
  have hcard : ((Finset.Ico a (3 * a)).card : ℝ) = 2 * a := by
    rw [Nat.card_Ico, show 3 * a - a = 2 * a by omega]
    push_cast
    ring
  have habs : ∑ c ∈ Finset.Ico a (3 * a), |d c| ≤ α * T * √e := by
    refine sum_abs_le_of_card_mul_sum_sq_le _ _ (by positivity) ?_
    rw [hcard, mul_pow, mul_pow, Real.sq_sqrt he]
    have h0 : 0 ≤ e * α ^ 2 * T ^ 2 := by positivity
    calc 2 * (a : ℝ) * ∑ c ∈ Finset.Ico a (3 * a), d c ^ 2
        ≤ 2 * a * (e * α ^ 2 * T * h) := by gcongr
      _ = e * α ^ 2 * T ^ 2 / 2 := by linear_combination (2 * e * α ^ 2 * T) * hah
      _ ≤ α ^ 2 * T ^ 2 * e := by linarith
  -- the averaging and flatness errors
  have hdiff : ‖windowTransform n t T ξ β - (α : ℂ) * ∫ x, φ x‖ ≤
      M * (α * T) + (M + 1) * (α * T * √e) := by
    rw [hI, hΦ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hcell).trans ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, hcard]
    have h2 : 2 * (a : ℝ) * (2 * α * h) = α * T := by linear_combination (4 * α) * hah
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left habs hM0]
  -- the constant mode
  have hconst : ‖(α : ℂ) * ∫ x, φ x‖ ≤ α * T * (C₂ * (1 / (T * ξ) ^ J)) := by
    rw [hφ, integral_windowTest hT0, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα, abs_of_pos hT0, ← mul_assoc,
      mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := hF (T * ξ) (by positivity)
    rwa [abs_of_pos (by positivity)] at this
  -- the resolution term
  have hMle : M ≤ (C₁ + 8) * (h * ξ) := by
    have hξT : 16 / 3 ≤ ξ * T := by nlinarith
    have h1 : C₁ / T ≤ C₁ * ξ := by
      rw [div_le_iff₀ hT0]
      nlinarith [mul_le_mul_of_nonneg_left hξT hC₁.le]
    have h2 : 2 * π * ξ ≤ 8 * ξ := by nlinarith [Real.pi_le_four]
    calc M = (C₁ / T + 2 * π * ξ) * h := rfl
      _ ≤ ((C₁ + 8) * ξ) * h := by gcongr; linarith
      _ = (C₁ + 8) * (h * ξ) := by ring
  -- assembly
  have hA : 0 ≤ α * T := by positivity
  have hX : 0 ≤ √e := Real.sqrt_nonneg e
  have hX1 : √e ≤ 1 := Real.sqrt_le_one.2 he1
  have hY : 0 ≤ h * ξ := by positivity
  have hZ : 0 ≤ 1 / (T * ξ) ^ J := by positivity
  have hMe : M * (α * T * √e) ≤ M * (α * T) :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA hX1) hM0
  have hMA : M * (α * T) ≤ (C₁ + 8) * (h * ξ) * (α * T) := mul_le_mul_of_nonneg_right hMle hA
  have htri : ‖windowTransform n t T ξ β‖ ≤ ‖windowTransform n t T ξ β - (α : ℂ) * ∫ x, φ x‖ +
      ‖(α : ℂ) * ∫ x, φ x‖ := by
    have := norm_add_le (windowTransform n t T ξ β - (α : ℂ) * ∫ x, φ x) ((α : ℂ) * ∫ x, φ x)
    rwa [sub_add_cancel] at this
  have hfin : (1 + 2 * (C₁ + 8) + C₂) * α * T * (√e + h * ξ + 1 / (T * ξ) ^ J) =
      α * T * √e + 2 * ((C₁ + 8) * (h * ξ) * (α * T)) + α * T * (C₂ * (1 / (T * ξ) ^ J)) +
        ((2 * (C₁ + 8) + C₂) * (α * T * √e) + (1 + C₂) * (α * T * (h * ξ)) +
          (1 + 2 * (C₁ + 8)) * (α * T * (1 / (T * ξ) ^ J))) := by ring
  have hrest : 0 ≤ (2 * (C₁ + 8) + C₂) * (α * T * √e) + (1 + C₂) * (α * T * (h * ξ)) +
      (1 + 2 * (C₁ + 8)) * (α * T * (1 / (T * ξ) ^ J)) := by positivity
  rw [hfin]
  linarith

end Favard.Exclusion
