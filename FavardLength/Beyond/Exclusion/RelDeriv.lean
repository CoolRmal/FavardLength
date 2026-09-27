import FavardLength.Beyond.Exclusion.RelDeriv.Ratio
import FavardLength.Beyond.Exclusion.Statements
import Mathlib.Analysis.Complex.Liouville

/-!
# Relative derivatives at the useful harmonics (Appendix G §2)

We prove the sub-contract `Favard.Exclusion.RelDerivStatement`. Let `p, q` be odd, `Q = p + q`,
`t₀ = (q - p)/Q`, let `k` have even two-adic valuation and `ξ = Qk/8`, so that the real product
arguments `x = 4(1 - t)ξ`, `y = 4(1 + t)ξ` of `ψ_{n,t}(ξ) = A_n(x) A_n(y) sinc(πρ4^{-n}ξ)` lie
within `Δ = 4|t - t₀|ξ` of the integers `x₀ = pk`, `y₀ = qk` of even two-adic valuation. Put
`L = log(2 + Qk)`.

* **Comparison with the rational point.** Near `x₀` no factor of `A_n` vanishes and
  `tanSum n x ≤ 10 L` (`Exclusion.tanSum_le_of_isFourPowOdd`), so the real ratio bound gives
  `|A_n(x₀)| ≤ e^{10ΔL} |A_n(x)|`. With `ΔL ≤ 1/4` and `sinc ≥ 1/2` this is
  `|ψ_{n,t}(ξ)| ≥ (e^{-5}/2) |A_n(pk) A_n(qk)|`.
* **Moments.** On the circle of radius `1/L` around `ξ`, the complex ratio bounds for both
  cosine products (with displacements of modulus at most `8/L`) and the box bound give
  `|Ψ| ≤ 2e^{171} |ψ_{n,t}(ξ)|`. Cauchy's estimate for the entire function `Ψ_{n,t}` and
  `Ψ^{(j)}(ξ) = (-2πi)^j M_j(ξ)` give `|M_j(ξ)| ≤ 2e^{171} j!/(2π)^j · L^j |ψ_{n,t}(ξ)|`.
-/

open Real Set Metric
open scoped Nat

namespace Favard.Exclusion

/-! ### The local estimate near two integers of even valuation -/

/-- The constants `C_j = 2e^{171} j!/(2π)^j` of the moment bound. -/
noncomputable def relDerivConst (j : ℕ) : ℝ :=
  2 * Real.exp 171 * j ! / (2 * π) ^ j

lemma relDerivConst_nonneg (j : ℕ) : 0 ≤ relDerivConst j := by
  unfold relDerivConst
  positivity

/-- The product formula at a real frequency in absolute value, with `sinc ≥ 1/2`. -/
lemma abs_tailFT_eq {n : ℕ} {t ξ : ℝ} (hξ : 0 ≤ ξ) (hbox : 8 / 3 / 4 ^ n * ξ ≤ 1 / 4) :
    |tailFT n t ξ| = |cosProd n (4 * (1 - t) * ξ)| * |cosProd n (4 * (1 + t) * ξ)| *
      Real.sinc (8 / 3 * π / 4 ^ n * ξ) ∧ 1 / 2 ≤ Real.sinc (8 / 3 * π / 4 ^ n * ξ) := by
  have hθ : 8 / 3 * π / 4 ^ n * ξ = π * (8 / 3 / 4 ^ n * ξ) := by ring
  have hs : 1 / 2 ≤ Real.sinc (8 / 3 * π / 4 ^ n * ξ) := by
    refine half_le_sinc (by positivity) ?_
    rw [hθ]
    nlinarith [pi_pos]
  refine ⟨?_, hs⟩
  rw [tailFT_eq, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sinc _)]

/-- **Relative derivatives near two integers of even valuation.** Let `x₀, y₀` be integers of
even two-adic valuation, `L ≥ max(1, log(2 + x₀), log(2 + y₀))`, and let the real product
arguments satisfy `|4(1 - t)ξ - x₀| L ≤ 1/4`, `|4(1 + t)ξ - y₀| L ≤ 1/4`. If
`ρ4^{-n}ξ ≤ 1/4`, then `|ψ_{n,t}(ξ)| ≥ (e^{-5}/2)|A_n(x₀) A_n(y₀)|` and
`|M_j(ξ)| ≤ C_j L^j |ψ_{n,t}(ξ)|`. -/
theorem relDeriv_local {n : ℕ} {t ξ : ℝ} {x₀ y₀ : ℕ} (hx₀ : IsFourPowOdd x₀)
    (hy₀ : IsFourPowOdd y₀) {L : ℝ} (hL : 1 ≤ L) (hLx : Real.log (2 + x₀) ≤ L)
    (hLy : Real.log (2 + y₀) ≤ L) (hx : |4 * (1 - t) * ξ - x₀| * L ≤ 1 / 4)
    (hy : |4 * (1 + t) * ξ - y₀| * L ≤ 1 / 4) (ht : t ∈ Icc (0 : ℝ) 1) (hξ : 0 ≤ ξ)
    (hbox : 8 / 3 / 4 ^ n * ξ ≤ 1 / 4) :
    Real.exp (-5) / 2 * |cosProd n x₀ * cosProd n y₀| ≤ |tailFT n t ξ| ∧
      ∀ j : ℕ, ‖tailMoment n t j ξ‖ ≤ relDerivConst j * L ^ j * |tailFT n t ξ| := by
  obtain ⟨hψ, hsinc⟩ := abs_tailFT_eq (t := t) hξ hbox
  set x : ℝ := 4 * (1 - t) * ξ with hxdef
  set y : ℝ := 4 * (1 + t) * ξ with hydef
  have hL0 : 0 < L := by linarith
  -- the real points are within `1/4` of the integers
  have hxn : |x - x₀| ≤ 1 / 4 := by nlinarith [abs_nonneg (x - x₀)]
  have hyn : |y - y₀| ≤ 1 / 4 := by nlinarith [abs_nonneg (y - y₀)]
  have hcx := cos_ne_zero_of_isFourPowOdd hx₀ hxn
  have hcy := cos_ne_zero_of_isFourPowOdd hy₀ hyn
  have hSx : tanSum n x ≤ 10 * L := (tanSum_le_of_isFourPowOdd n hx₀ hxn).trans (by linarith)
  have hSy : tanSum n y ≤ 10 * L := (tanSum_le_of_isFourPowOdd n hy₀ hyn).trans (by linarith)
  set s : ℝ := Real.sinc (8 / 3 * π / 4 ^ n * ξ)
  have hAx0 : 0 ≤ |cosProd n x| := abs_nonneg _
  have hAy0 : 0 ≤ |cosProd n y| := abs_nonneg _
  refine ⟨?_, fun j => ?_⟩
  · -- comparison with the rational point
    have hx' : |cosProd n x₀| ≤ |cosProd n x| * Real.exp (5 / 2) := by
      refine (abs_cosProd_le_mul_exp n x x₀ hcx).trans ?_
      gcongr
      rw [abs_sub_comm]
      nlinarith [tanSum_nonneg n x, abs_nonneg (x - x₀)]
    have hy' : |cosProd n y₀| ≤ |cosProd n y| * Real.exp (5 / 2) := by
      refine (abs_cosProd_le_mul_exp n y y₀ hcy).trans ?_
      gcongr
      rw [abs_sub_comm]
      nlinarith [tanSum_nonneg n y, abs_nonneg (y - y₀)]
    have he : Real.exp (-5) * Real.exp (5 / 2) * Real.exp (5 / 2) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [hψ, abs_mul]
    calc Real.exp (-5) / 2 * (|cosProd n x₀| * |cosProd n y₀|)
        ≤ Real.exp (-5) / 2 * ((|cosProd n x| * Real.exp (5 / 2)) *
            (|cosProd n y| * Real.exp (5 / 2))) := by gcongr
      _ = 1 / 2 * (|cosProd n x| * |cosProd n y|) *
            (Real.exp (-5) * Real.exp (5 / 2) * Real.exp (5 / 2)) := by ring
      _ ≤ s * (|cosProd n x| * |cosProd n y|) * 1 := by
          rw [he]
          gcongr
      _ = |cosProd n x| * |cosProd n y| * s := by ring
  · -- Cauchy's estimate on the circle of radius `1/L`
    have ht1 : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    have hdiff := differentiable_tailFTC ht1 n
    set r : ℝ := 1 / L with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by rw [hr, div_le_one hL0]; exact hL
    have hrL : r * L = 1 := by rw [hr]; field_simp
    have hbound : ∀ w ∈ sphere (ξ : ℂ) r,
        ‖tailFTC n t w‖ ≤ 2 * Real.exp 171 * |tailFT n t ξ| := by
      intro w hw
      rw [mem_sphere_iff_norm] at hw
      set u : ℂ := w - ξ with hu
      have hwu : w = ξ + u := by rw [hu]; ring
      have h1t : 0 ≤ 1 - t := by linarith [ht.2]
      have hux : ‖4 * (1 - (t : ℂ)) * u‖ ≤ 8 * r := by
        rw [norm_mul, norm_mul, hw, show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1t, Complex.norm_ofNat]
        nlinarith [ht.1]
      have huy : ‖4 * (1 + (t : ℂ)) * u‖ ≤ 8 * r := by
        rw [norm_mul, norm_mul, hw, show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]),
          Complex.norm_ofNat]
        nlinarith [ht.2]
      have hA : ‖cosProdC n (4 * (1 - t) * w)‖ ≤ |cosProd n x| * Real.exp 80 := by
        have e : 4 * (1 - (t : ℂ)) * w = (x : ℂ) + 4 * (1 - (t : ℂ)) * u := by
          rw [hwu, hxdef]; push_cast; ring
        rw [e]
        refine (norm_cosProdC_add_le n x hcx _).trans ?_
        gcongr
        calc ‖4 * (1 - (t : ℂ)) * u‖ * tanSum n x ≤ 8 * r * (10 * L) :=
              mul_le_mul hux hSx (tanSum_nonneg n x) (by positivity)
          _ = 80 := by rw [show 8 * r * (10 * L) = 80 * (r * L) by ring, hrL, mul_one]
      have hB : ‖cosProdC n (4 * (1 + t) * w)‖ ≤ |cosProd n y| * Real.exp 80 := by
        have e : 4 * (1 + (t : ℂ)) * w = (y : ℂ) + 4 * (1 + (t : ℂ)) * u := by
          rw [hwu, hydef]; push_cast; ring
        rw [e]
        refine (norm_cosProdC_add_le n y hcy _).trans ?_
        gcongr
        calc ‖4 * (1 + (t : ℂ)) * u‖ * tanSum n y ≤ 8 * r * (10 * L) :=
              mul_le_mul huy hSy (tanSum_nonneg n y) (by positivity)
          _ = 80 := by rw [show 8 * r * (10 * L) = 80 * (r * L) by ring, hrL, mul_one]
      have hC : ‖boxFTC n w‖ ≤ Real.exp 11 := by
        refine (norm_boxFTC_le n w).trans (Real.exp_le_exp.2 ?_)
        have him : |w.im| ≤ r := by
          have : w.im = u.im := by rw [hwu]; simp
          rw [this, ← hw]
          exact Complex.abs_im_le_norm u
        have : π * |w.im| ≤ 4 * 1 :=
          mul_le_mul pi_le_four (him.trans hr1) (abs_nonneg _) (by norm_num)
        linarith
      have he : Real.exp 80 * Real.exp 80 * Real.exp 11 = Real.exp 171 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      rw [tailFTC_eq, norm_mul, norm_mul]
      calc ‖cosProdC n (4 * (1 - t) * w)‖ * ‖cosProdC n (4 * (1 + t) * w)‖ * ‖boxFTC n w‖
          ≤ (|cosProd n x| * Real.exp 80) * (|cosProd n y| * Real.exp 80) * Real.exp 11 := by
            gcongr
        _ = |cosProd n x| * |cosProd n y| * Real.exp 171 := by rw [← he]; ring
        _ = 2 * Real.exp 171 * (|cosProd n x| * |cosProd n y| * (1 / 2)) := by ring
        _ ≤ 2 * Real.exp 171 * |tailFT n t ξ| := by
            rw [hψ]
            gcongr
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr0
      hdiff.diffContOnCl hbound
    rw [iteratedDeriv_tailFTC_ofReal ht1, norm_mul, norm_pow] at hcauchy
    have hn : ‖-2 * (π : ℂ) * Complex.I‖ = 2 * π := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos pi_pos, Complex.norm_two, mul_one]
    rw [hn] at hcauchy
    have h2π : 0 < (2 * π) ^ j := by positivity
    have hrj : r ^ j = (L ^ j)⁻¹ := by rw [hr, one_div, inv_pow]
    rw [← le_div_iff₀' h2π] at hcauchy
    rw [relDerivConst]
    refine hcauchy.trans (le_of_eq ?_)
    rw [hrj, div_inv_eq_mul]
    ring

/-! ### The rational parameter -/

lemma isFourPowOdd_mul {p k : ℕ} (hp : Odd p) (hk : IsFourPowOdd k) : IsFourPowOdd (p * k) := by
  obtain ⟨v, h, hh, rfl⟩ := hk
  exact ⟨v, p * h, hp.mul hh, by ring⟩

lemma one_le_of_isFourPowOdd {k : ℕ} (hk : IsFourPowOdd k) : 1 ≤ k := by
  obtain ⟨v, h, hh, rfl⟩ := hk
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by positivity) (by rintro rfl; simp at hh))

/-- **Relative derivatives at the useful harmonics** (Appendix G (6)–(7)), with `c₀ = 1/4`,
`c₁ = e^{-5}/2` and `C_j = 2e^{171} j!/(2π)^j`. -/
theorem relDeriv : RelDerivStatement := by
  refine ⟨1 / 4, Real.exp (-5) / 2, by norm_num, by positivity, relDerivConst,
    relDerivConst_nonneg, ?_⟩
  intro p q k n t hp hq hk ht hΔ hbox
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast one_le_of_isFourPowOdd hk
  have hQ : (0 : ℝ) < (p : ℝ) + q := by linarith
  set ξ : ℝ := ((p : ℝ) + q) * k / 8 with hξ
  set L : ℝ := Real.log (2 + ((p : ℝ) + q) * k) with hLdef
  set t₀ : ℝ := ((q : ℝ) - p) / ((p : ℝ) + q) with ht₀
  have hξ0 : 0 ≤ ξ := by positivity
  have hL : 1 ≤ L := one_le_log_two_add (by nlinarith)
  have hLp : Real.log (2 + ((p * k : ℕ) : ℝ)) ≤ L := by
    push_cast
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hLq : Real.log (2 + ((q * k : ℕ) : ℝ)) ≤ L := by
    push_cast
    exact Real.log_le_log (by positivity) (by nlinarith)
  have ex : 4 * (1 - t) * ξ - ((p * k : ℕ) : ℝ) = -(4 * (t - t₀) * ξ) := by
    rw [ht₀, hξ]
    push_cast
    field_simp
    ring
  have ey : 4 * (1 + t) * ξ - ((q * k : ℕ) : ℝ) = 4 * (t - t₀) * ξ := by
    rw [ht₀, hξ]
    push_cast
    field_simp
    ring
  have hΔ' : |4 * (t - t₀) * ξ| * L ≤ 1 / 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg hξ0]
    exact hΔ
  have hx : |4 * (1 - t) * ξ - ((p * k : ℕ) : ℝ)| * L ≤ 1 / 4 := by rw [ex, abs_neg]; exact hΔ'
  have hy : |4 * (1 + t) * ξ - ((q * k : ℕ) : ℝ)| * L ≤ 1 / 4 := by rw [ey]; exact hΔ'
  obtain ⟨h1, h2⟩ := relDeriv_local (isFourPowOdd_mul hp hk) (isFourPowOdd_mul hq hk) hL hLp hLq
    hx hy ht hξ0 hbox
  push_cast at h1
  exact ⟨h1, h2⟩

end Favard.Exclusion
