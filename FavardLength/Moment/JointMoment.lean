import FavardLength.Moment.JointMoment.Identities
import FavardLength.Moment.JointMoment.ChangeOfVariables
import FavardLength.Moment.JointMoment.Cells
import FavardLength.Moment.JointMoment.Sums

/-!
# The joint negative-moment estimate (J1)

We prove `SineCellStatement → LowCellStatement → HilbertStatement → JointMomentStatement`,
following the manuscript (section "The joint negative-moment estimate", steps 5, J7–J8):

1. the integrand factors through `(u, v) = (y(1+t), y(1-t))` (`integrand_eq_uvIntegrand`), and the
   change of variables `dy dt = du dv / (u + v)` moves the integral to `[y₀, 2] × [0, 1]`;
2. on each pair of cells `I_i × I_j`, the telescoping identity, the low-cell majorants `b_i` and
   the weight bound (J7) dominate the integrand by `κ_{ij} φ(u) φ(v)`, where
   `φ(w) = |sin(Lw)|^{-s} R(w)` (`uv_pointwise_le`);
3. the product integrals are bounded by the sine-cell estimate, the double sum by the Hilbert
   inequality, and `∑ b_i^s` by concavity and the low-cell total `∑ b_i ≤ C 2^m`.

To avoid zero majorants we use `β_i = b_i + 4^{-m} > 0`, which keeps `∑ β_i ≤ (C + 1) 2^m`.
-/

open MeasureTheory Set Real

open Finset (range mem_range sum_congr mul_sum)

open scoped ENNReal

namespace Favard

namespace JointMoment

/-- The one-coordinate sine–Riesz weight `φ(w) = |sin(4^m w)|^{-s} R(w)`. -/
noncomputable def sineWeight (m n : ℕ) (s w : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |sin (4 ^ m * w)| ^ (-s) * ENNReal.ofReal (riesz m n w)

/-- The integrand of (J1) in the variables `(u, v)`:
`|A_m(u) A_m(v)|^{-s} R(u) R(v) / 4^(n-m)`. -/
noncomputable def uvIntegrand (m n : ℕ) (s : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |halfProd m p.1 * halfProd m p.2| ^ (-s) *
    ENNReal.ofReal (riesz m n p.1 * riesz m n p.2 / 4 ^ (n - m))

lemma continuous_halfProd (m : ℕ) : Continuous (halfProd m) := by
  unfold halfProd
  fun_prop

lemma continuous_riesz (m n : ℕ) : Continuous (riesz m n) := by
  unfold riesz
  fun_prop

lemma measurable_sineWeight (m n : ℕ) (s : ℝ) : Measurable (sineWeight m n s) := by
  have h := continuous_riesz m n
  unfold sineWeight
  refine Measurable.mul ?_ ?_
  · exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop)))
  · exact ENNReal.measurable_ofReal.comp h.measurable

lemma measurable_uvIntegrand (m n : ℕ) (s : ℝ) : Measurable (uvIntegrand m n s) := by
  have h1 := continuous_halfProd m
  have h2 := continuous_riesz m n
  unfold uvIntegrand
  refine Measurable.mul ?_ ?_
  · exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop)))
  · exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))

/-- The integrand of (J1) is `uvIntegrand` at `(y(1+t), y(1-t))`. -/
lemma integrand_eq_uvIntegrand (m n : ℕ) (s t y : ℝ) :
    ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2) =
      uvIntegrand m n s (y * (1 + t), y * (1 - t)) := by
  rw [uvIntegrand, lowProd_eq_halfProd_mul, highProd_sq]

/-- The pointwise bound on a pair of cells: on `(I_i × I_j) ∩ ([y₀, 2] × [0, 1])`,
`(u+v)⁻¹ |A_m(u) A_m(v)|^{-s} R(u) R(v)/M ≤ κ_{ij} φ(u) φ(v)` with
`κ_{ij} = 12 L/(π(i+j+1)) · (2L√β_i)^s (2L√β_j)^s / M`. -/
lemma uv_pointwise_le {m n : ℕ} {s : ℝ} (hs : 0 < s) {β : ℕ → ℝ} (hβ : ∀ i, 0 < β i)
    (hD : ∀ i < 4 ^ m, ∀ w ∈ cell m i, lowD m w ^ 2 ≤ β i) {i j : ℕ} (hi : i < 4 ^ m)
    (hj : j < 4 ^ m) {p : ℝ × ℝ} (hp : p ∈ Icc (3 / 8 / 4 ^ m : ℝ) 2 ×ˢ Icc 0 1)
    (hpij : p ∈ cell m i ×ˢ cell m j) :
    ENNReal.ofReal (1 / (p.1 + p.2)) * uvIntegrand m n s p ≤
      ENNReal.ofReal (12 * 4 ^ m / (π * ((i : ℝ) + j + 1)) * (2 * 4 ^ m * √(β i)) ^ s *
          (2 * 4 ^ m * √(β j)) ^ s * (1 / 4 ^ (n - m))) *
        (sineWeight m n s p.1 * sineWeight m n s p.2) := by
  obtain ⟨⟨hu0, -⟩, ⟨hv0, -⟩⟩ := hp
  have hw := one_div_add_le hpij.1 hpij.2 hu0 hv0
  have hAu := ofReal_abs_halfProd_rpow_neg_le hs (hβ i) (hD i hi p.1 hpij.1)
  have hAv := ofReal_abs_halfProd_rpow_neg_le hs (hβ j) (hD j hj p.2 hpij.2)
  have hRu := riesz_nonneg m n p.1
  have hRv := riesz_nonneg m n p.2
  rw [uvIntegrand, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    div_eq_mul_one_div (riesz m n p.1 * riesz m n p.2), ENNReal.ofReal_mul (mul_nonneg hRu hRv),
    ENNReal.ofReal_mul hRu, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (1 / (p.1 + p.2)) *
        (ENNReal.ofReal |halfProd m p.1| ^ (-s) * ENNReal.ofReal |halfProd m p.2| ^ (-s) *
          (ENNReal.ofReal (riesz m n p.1) * ENNReal.ofReal (riesz m n p.2) *
            ENNReal.ofReal (1 / 4 ^ (n - m))))
      ≤ ENNReal.ofReal (12 * 4 ^ m / (π * ((i : ℝ) + j + 1))) *
        (ENNReal.ofReal ((2 * 4 ^ m * √(β i)) ^ s) * ENNReal.ofReal |sin (4 ^ m * p.1)| ^ (-s) *
          (ENNReal.ofReal ((2 * 4 ^ m * √(β j)) ^ s) *
            ENNReal.ofReal |sin (4 ^ m * p.2)| ^ (-s)) *
          (ENNReal.ofReal (riesz m n p.1) * ENNReal.ofReal (riesz m n p.2) *
            ENNReal.ofReal (1 / 4 ^ (n - m)))) := by
        gcongr
    _ = _ := by
        unfold sineWeight
        ring

end JointMoment

open JointMoment

/-- **Joint negative moment** (J1): the sine-cell estimate, the low-cell majorants and the
Hilbert inequality imply `JointMomentStatement`. -/
theorem jointMoment_of (hS : SineCellStatement) (hL : LowCellStatement)
    (hH : HilbertStatement) : JointMomentStatement := by
  intro s hs1 hs2
  have hs0 : 0 < s := by linarith
  obtain ⟨CS, hCS, hSine⟩ := hS s hs0 hs2
  obtain ⟨CL, hCL, hLow⟩ := hL
  obtain ⟨CH, hCH, hHil⟩ := hH
  refine ⟨12 * CS ^ 2 * π * CH * 4 ^ s * (CL + 1) ^ s, by positivity, fun m n hmn => ?_⟩
  obtain ⟨b, hb0, hbD, hbsum⟩ := hLow m
  have hL0 : (0 : ℝ) < 4 ^ m := by positivity
  set β : ℕ → ℝ := fun i => b i + 1 / 4 ^ m with hβdef
  have hβ : ∀ i, 0 < β i := fun i => add_pos_of_nonneg_of_pos (hb0 i) (by positivity)
  have hD : ∀ i < 4 ^ m, ∀ w ∈ cell m i, lowD m w ^ 2 ≤ β i := fun i hi w hw =>
    (hbD i hi w hw).trans (le_add_of_nonneg_right (by positivity))
  set a : ℕ → ℝ := fun i => (2 * 4 ^ m * √(β i)) ^ s with hadef
  set κ : ℕ → ℕ → ℝ := fun i j =>
    12 * 4 ^ m / (π * ((i : ℝ) + j + 1)) * a i * a j * (1 / 4 ^ (n - m)) with hκdef
  have hy₀ : (0 : ℝ) < 3 / 8 / 4 ^ m := by positivity
  set c : ℝ := CS * π / 4 ^ m with hcdef
  have hreal : ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), κ i j * (c * c) ≤
      12 * CS ^ 2 * π * CH * 4 ^ s * (CL + 1) ^ s * ((4 : ℝ) ^ m) ^ (3 * s / 2) /
        4 ^ (n - m) := by
    have hM : (0 : ℝ) < 4 ^ (n - m) := by positivity
    have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
    have hsq : ∀ i, a i ^ 2 = ((2 * 4 ^ m) ^ s) ^ 2 * β i ^ s := fun i => by
      simp only [hadef]
      rw [mul_rpow (by positivity) (sqrt_nonneg _), mul_pow, rpow_pow_comm (sqrt_nonneg _),
        sq_sqrt (hβ i).le]
    have hsumβ : ∑ i ∈ range (4 ^ m), β i ≤ (CL + 1) * 2 ^ m := by
      simp only [hβdef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      rw [mul_one_div_cancel hL0.ne']
      have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith [hbsum]
    have hconc := sum_rpow_le_card_rpow_mul (range (4 ^ m)) (fun i _ => (hβ i).le) hs0.le
      (by linarith)
    rw [Finset.card_range] at hconc
    push_cast at hconc
    have hpow : (∑ i ∈ range (4 ^ m), β i) ^ s ≤ (CL + 1) ^ s * (2 ^ m) ^ s := by
      rw [← mul_rpow (by positivity) (by positivity)]
      exact rpow_le_rpow (Finset.sum_nonneg fun i _ => (hβ i).le) hsumβ hs0.le
    have hexp := exponent_identity m s
    calc ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), κ i j * (c * c)
        = 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) *
            ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), a i * a j / ((i : ℝ) + j + 1) := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          simp only [hκdef]
          field_simp
      _ ≤ 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) *
            (CH * ∑ i ∈ range (4 ^ m), a i ^ 2) := by
          gcongr
          exact hHil _ a ha0
      _ = 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) *
            (CH * (((2 * 4 ^ m) ^ s) ^ 2 * ∑ i ∈ range (4 ^ m), β i ^ s)) := by
          simp_rw [hsq, ← mul_sum]
      _ ≤ 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) *
            (CH * (((2 * 4 ^ m) ^ s) ^ 2 * (((4 : ℝ) ^ m) ^ (1 - s) *
              ((CL + 1) ^ s * (2 ^ m) ^ s)))) := by
          gcongr
          exact hconc.trans (by gcongr)
      _ = 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) * CH * (CL + 1) ^ s *
            (((2 * 4 ^ m) ^ s) ^ 2 * ((4 : ℝ) ^ m) ^ (1 - s) * ((2 : ℝ) ^ m) ^ s) := by
          ring
      _ = _ := by
          rw [hexp, hcdef]
          field_simp
  calc ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
        ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2)
      = ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
          uvIntegrand m n s (y * (1 + t), y * (1 - t)) := by
        simp_rw [integrand_eq_uvIntegrand]
    _ = ∫⁻ p in uvMap '' (Icc 0 1 ×ˢ Icc (3 / 8 / 4 ^ m) 1),
          ENNReal.ofReal (1 / (p.1 + p.2)) * uvIntegrand m n s p :=
        lintegral_comp_uvMap hy₀ _ (measurable_uvIntegrand m n s)
    _ ≤ ∫⁻ p in Icc (3 / 8 / 4 ^ m) 2 ×ˢ Icc 0 1,
          ENNReal.ofReal (1 / (p.1 + p.2)) * uvIntegrand m n s p :=
        lintegral_mono_set (uvMap_image_subset hy₀)
    _ ≤ ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), ∫⁻ p in cell m i ×ˢ cell m j,
          ENNReal.ofReal (κ i j) * (sineWeight m n s p.1 * sineWeight m n s p.2) := by
        refine setLIntegral_le_sum_cells m ?_ _ _ (fun i j => ?_)
          fun i hi j hj p hp hpij => uv_pointwise_le hs0 hβ hD hi hj hp hpij
        · exact prod_mono (Icc_subset_Icc hy₀.le (by linarith [two_le_pi]))
            (Icc_subset_Icc le_rfl (by linarith [two_le_pi]))
        · have := measurable_sineWeight m n s
          fun_prop
    _ = ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), ENNReal.ofReal (κ i j) *
          ((∫⁻ u in cell m i, sineWeight m n s u) * ∫⁻ v in cell m j, sineWeight m n s v) := by
        simp_rw [setLIntegral_cell_prod_mul m _ _ (measurable_sineWeight m n s)]
    _ ≤ ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m),
          ENNReal.ofReal (κ i j) * (ENNReal.ofReal c * ENNReal.ofReal c) := by
        gcongr with i hi j hj
        · exact hSine m n i (mem_range.1 hi)
        · exact hSine m n j (mem_range.1 hj)
    _ = ENNReal.ofReal (∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), κ i j * (c * c)) := by
        have hκ : ∀ i j, 0 ≤ κ i j := fun i j => by positivity
        have hc : 0 ≤ c := by positivity
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hκ i j) (mul_nonneg hc hc)]
        refine sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hκ i j) (mul_nonneg hc hc)]
        refine sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (hκ i j), ENNReal.ofReal_mul hc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end Favard
