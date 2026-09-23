import FavardLength.Fourier.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pointwise bounds for the frequency window

Elementary estimates used in the frequency-window selection (manuscript P2):

* `|φ_t| ≤ 1`, hence `|ν̂_{r,t}| ≤ 1`;
* `sinc² x ≤ 2 / (1 + x²)`, so the normalized-energy integrand is integrable and
  `normEnergy r t ≤ H` bounds the Lebesgue integral of `sinc² ν̂²` by `2πH`;
* `sinc² x ≥ 1/2` for `0 < x ≤ 1`;
* after the substitution `ξ = 4^n y`, the terminal transform splits as
  `ν̂_{N,t}(4^n y) = P₁(t,y) P₂(t,y) T(t,y)` with a tail `T ≥ 2/3` for `t, y ∈ [0,1]`, whence
  `(P₁ P₂)² ≤ (9/4) ν̂_{N,t}(4^n y)²`.
-/

open MeasureTheory Set Real Finset

namespace Favard

namespace Window

/-- `|φ_t(z)| ≤ 1`. -/
lemma abs_phi_le_one (t z : ℝ) : |phi t z| ≤ 1 := by
  unfold phi
  rw [abs_div, abs_two, div_le_one (by norm_num : (0 : ℝ) < 2)]
  have h1 := abs_cos_le_one z
  have h2 := abs_cos_le_one (t * z)
  have := abs_add_le (cos z) (cos (t * z))
  linarith

/-- `|ν̂_{r,t}(ξ)| ≤ 1`. -/
lemma abs_nuHat_le_one (r : ℕ) (t ξ : ℝ) : |nuHat r t ξ| ≤ 1 := by
  unfold nuHat
  rw [Finset.abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_phi_le_one _ _)

lemma nuHat_sq_le_one (r : ℕ) (t ξ : ℝ) : nuHat r t ξ ^ 2 ≤ 1 := by
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_nuHat_le_one r t ξ)

/-- `(t, ξ) ↦ ν̂_{r,t}(ξ)` is jointly continuous. -/
lemma continuous_nuHat (r : ℕ) : Continuous fun p : ℝ × ℝ => nuHat r p.1 p.2 := by
  unfold nuHat phi
  fun_prop

lemma continuous_nuHat_right (r : ℕ) (t : ℝ) : Continuous fun ξ => nuHat r t ξ := by
  unfold nuHat phi
  fun_prop

lemma sinc_sq_le_one (x : ℝ) : sinc x ^ 2 ≤ 1 := by
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_sinc_le_one x)

/-- `sinc² x ≤ 2 / (1 + x²)`: use `|sinc| ≤ 1` for `x² ≤ 1` and `|sinc x| ≤ 1/|x|` otherwise. -/
lemma sinc_sq_le (x : ℝ) : sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rcases le_or_gt (x ^ 2) 1 with h | h
  · have := sinc_sq_le_one x
    have h0 : 0 ≤ sinc x ^ 2 := sq_nonneg _
    nlinarith
  · have hx : x ≠ 0 := by rintro rfl; norm_num at h
    have hs := sin_sq_le_one x
    have hx2 : 0 < x ^ 2 := by positivity
    rw [sinc_of_ne_zero hx, div_pow]
    have key : sin x ^ 2 / x ^ 2 * x ^ 2 = sin x ^ 2 := div_mul_cancel₀ _ hx2.ne'
    have h0 : 0 ≤ sin x ^ 2 / x ^ 2 := by positivity
    have h1 : sin x ^ 2 / x ^ 2 ≤ 1 := by rw [div_le_one hx2]; linarith
    nlinarith

/-- `ξ ↦ sinc (a ξ)²` is integrable for `a ≠ 0`. -/
lemma integrable_sinc_sq {a : ℝ} (ha : a ≠ 0) : Integrable fun ξ : ℝ => sinc (a * ξ) ^ 2 := by
  have hint : Integrable fun ξ : ℝ => 2 * (1 + (a * ξ) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq.const_mul 2).comp_mul_left' ha)
  refine hint.mono' ?_ (ae_of_all _ fun ξ => ?_)
  · exact (continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2 |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le _

/-- The normalized-energy integrand is integrable. -/
lemma integrable_energy (r : ℕ) (t : ℝ) :
    Integrable fun ξ : ℝ => sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2 := by
  have ha : (4 / 3 / 4 ^ r : ℝ) ≠ 0 := by positivity
  refine (integrable_sinc_sq ha).mono' ?_ (ae_of_all _ fun ξ => ?_)
  · exact ((continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2).mul
      ((continuous_nuHat_right r t).pow 2) |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := nuHat_sq_le_one r t ξ
    have h0 : 0 ≤ sinc (4 / 3 / 4 ^ r * ξ) ^ 2 := sq_nonneg _
    nlinarith

/-- An energy bound `normEnergy r t ≤ H` controls the Lebesgue integral of `sinc² ν̂²`. -/
lemma lintegral_energy_le {r : ℕ} {t H : ℝ} (h : normEnergy r t ≤ H) :
    ∫⁻ ξ, ENNReal.ofReal (sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2) ≤
      ENNReal.ofReal (2 * π * H) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_energy r t)
    (ae_of_all _ fun ξ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold normEnergy at h
  rwa [inv_mul_le_iff₀ (by positivity)] at h

/-- `sinc² x ≥ 1/2` for `0 < x ≤ 1`. -/
lemma half_le_sinc_sq {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 / 2 ≤ sinc x ^ 2 := by
  have h := sin_gt_sub_cube hx
  rw [sinc_of_ne_zero hx.ne']
  have h2 : 3 / 4 ≤ sin x / x := by
    rw [le_div_iff₀ hx]
    nlinarith [mul_pos hx hx, mul_le_mul_of_nonneg_left hx1 (mul_pos hx hx).le]
  nlinarith

/-- `φ_t(z) ≥ 1 - z²/2` for `|t| ≤ 1`. -/
lemma one_sub_sq_div_two_le_phi {t : ℝ} (ht : |t| ≤ 1) (z : ℝ) : 1 - z ^ 2 / 2 ≤ phi t z := by
  unfold phi
  have h1 := one_sub_sq_div_two_le_cos (x := z)
  have h2 := one_sub_sq_div_two_le_cos (x := t * z)
  have ht2 : t ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) ht
  have : (t * z) ^ 2 ≤ z ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg z]
  linarith

/-- The lacunary product `∏_{i<K} (1 - 4^{-(i+1)})` is at least `2/3 + 4^{-K}/3`. -/
lemma prod_one_sub_inv_four_pow_ge (K : ℕ) :
    2 / 3 + ((4 : ℝ) ^ K)⁻¹ / 3 ≤ ∏ i ∈ range K, (1 - ((4 : ℝ) ^ (i + 1))⁻¹) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [prod_range_succ]
    set u : ℝ := ((4 : ℝ) ^ K)⁻¹ with hu
    have hu0 : 0 < u := by positivity
    have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h4 : ((4 : ℝ) ^ (K + 1))⁻¹ = u / 4 := by
      rw [pow_succ, mul_inv, hu, div_eq_mul_inv]
    rw [h4]
    have hfac : 0 ≤ 1 - u / 4 := by linarith
    calc 2 / 3 + u / 4 / 3 ≤ (2 / 3 + u / 3) * (1 - u / 4) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hfac

/-- The tail factors `φ_t(y 4^{-(i+1)})`, `t, y ∈ [0,1]`, have product at least `2/3`. -/
lemma two_thirds_le_tail {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (K : ℕ) : 2 / 3 ≤ ∏ i ∈ range K, phi t (y / 4 ^ (i + 1)) := by
  have hK := prod_one_sub_inv_four_pow_ge K
  have hpos : 0 ≤ ((4 : ℝ) ^ K)⁻¹ / 3 := by positivity
  refine le_trans (by linarith) (hK.trans (prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_))
  · have : ((4 : ℝ) ^ (i + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith
  · have ht : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
    refine le_trans ?_ (one_sub_sq_div_two_le_phi ht _)
    have h4 : (0 : ℝ) < 4 ^ (i + 1) := by positivity
    have hz0 : 0 ≤ y / 4 ^ (i + 1) := by positivity
    have hz : y / 4 ^ (i + 1) ≤ ((4 : ℝ) ^ (i + 1))⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (by positivity) hy1
    have hz1 : ((4 : ℝ) ^ (i + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith

/-- Splitting of the terminal transform at frequency `4^n y`:
`ν̂_{N,t}(4^n y) = P₁(t,y) P₂(t,y) ∏_{i < N-n-1} φ_t(y 4^{-(i+1)})`. -/
lemma nuHat_four_pow_mul {m n N : ℕ} (hmn : m ≤ n) (hnN : n < N) (t y : ℝ) :
    nuHat N t (4 ^ n * y) = lowProd m t y * highProd m n t y *
      ∏ i ∈ range (N - (n + 1)), phi t (y / 4 ^ (i + 1)) := by
  unfold nuHat lowProd highProd
  rw [← prod_range_mul_prod_Ico _ (Nat.succ_le_of_lt hnN), prod_Ico_eq_prod_range]
  congr 1
  · have hI : Finset.Ioc m n = Finset.Ico (m + 1) (n + 1) := by
      ext; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, prod_range_mul_prod_Ico _ (Nat.succ_le_succ hmn), ← prod_range_reflect]
    refine prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    have : n + 1 - 1 - j = n - j := by omega
    rw [this]
    have h4 : (4 : ℝ) ^ n = 4 ^ (n - j) * 4 ^ j := by rw [← pow_add]; congr 1; omega
    rw [h4]
    field_simp
  · refine prod_congr rfl fun i _ => ?_
    congr 1
    rw [show (4 : ℝ) ^ (n + 1 + i) = 4 ^ n * 4 ^ (i + 1) by rw [← pow_add]; congr 1; omega,
      mul_div_mul_left _ _ (by positivity)]

/-- For `t, y ∈ [0,1]` and `m ≤ n < N`: `(P₁ P₂)² ≤ (9/4) ν̂_{N,t}(4^n y)²`. -/
lemma lowProd_mul_highProd_sq_le {m n N : ℕ} (hmn : m ≤ n) (hnN : n < N) {t y : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (lowProd m t y * highProd m n t y) ^ 2 ≤ 9 / 4 * nuHat N t (4 ^ n * y) ^ 2 := by
  rw [nuHat_four_pow_mul hmn hnN]
  have hT := two_thirds_le_tail ht0 ht1 hy0 hy1 (N - (n + 1))
  set T := ∏ i ∈ range (N - (n + 1)), phi t (y / 4 ^ (i + 1))
  set P := lowProd m t y * highProd m n t y
  have hT2 : 4 / 9 ≤ T ^ 2 := by nlinarith
  have hP : 0 ≤ P ^ 2 := sq_nonneg _
  rw [mul_pow]
  nlinarith

end Window

end Favard
