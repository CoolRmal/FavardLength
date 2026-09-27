import FavardLength.Moment.JointMoment
import FavardLength.Beyond.Statements

/-!
# The improved joint negative-moment estimate (Appendix B.2, (7))

We prove `SineCellStatement → HilbertStatement → CellPowerSumStatement s β →
JointMomentImprovedStatement s β` for `1/4 ≤ s < 1/2`.

The proof is that of `jointMoment_of` (J1) with one change. There, the low-cell majorants
enter only through the concavity bound `∑_i β_i^s ≤ L^{1-s} (∑_i β_i)^s ≤ C L^{1-s/2}`, which
gives the prefactor `L^{3s/2}`. Here we use the positive majorants `b_i` of the improved
cell-power sum directly (no shift is needed since `b_i > 0`):
`(2L)^{2s} · (1/L) · ∑_i b_i^s ≤ C (2L)^{2s} L^{-β} = C 4^s L^{2s-β}`.

All the analytic steps (the change of variables to `(u, v)`, the cellwise pointwise bound, the
sine-cell integrals and the Hilbert inequality) are reused from `FavardLength.Moment.JointMoment`.
-/

open MeasureTheory Set Real

open Finset (range mem_range sum_congr mul_sum)

open scoped ENNReal

namespace Favard

namespace JointMoment

/-- Exponent bookkeeping: `((2L)^s)² L^{1-β} = 4^s L^{2s-β} L` for `L = 4^m`. -/
lemma exponent_identity_improved (m : ℕ) (s β : ℝ) :
    ((2 * (4 : ℝ) ^ m) ^ s) ^ 2 * ((4 : ℝ) ^ m) ^ (1 - β) =
      4 ^ s * ((4 : ℝ) ^ m) ^ (2 * s - β) * 4 ^ m := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have e4 : (4 : ℝ) ^ m = 2 ^ (2 * (m : ℝ)) := by
    rw [rpow_mul h2.le, rpow_natCast]
    norm_num
  have e24 : 2 * (4 : ℝ) ^ m = 2 ^ (1 + 2 * (m : ℝ)) := by rw [rpow_add h2, rpow_one, e4]
  have e4s : (4 : ℝ) ^ s = 2 ^ (2 * s) := by
    rw [rpow_mul h2.le]
    norm_num
  rw [e24, e4, e4s, ← rpow_mul h2.le, ← rpow_mul h2.le, ← rpow_mul h2.le,
    ← rpow_mul_natCast h2.le, ← rpow_add h2, ← rpow_add h2, ← rpow_add h2]
  congr 1
  push_cast
  ring

end JointMoment

open JointMoment

/-- **Improved joint negative moment** (Appendix B.2, (7)): the sine-cell estimate, the Hilbert
inequality and the improved cell-power sum imply `JointMomentImprovedStatement s β`. The
hypotheses `0 < β ≤ s` are not needed by the argument. -/
theorem jointMomentImproved_of (hS : SineCellStatement) (hH : HilbertStatement) {s β : ℝ}
    (hs1 : 1 / 4 ≤ s) (hs2 : s < 1 / 2) (hβ0 : 0 < β) (hβs : β ≤ s)
    (hC : CellPowerSumStatement s β) : JointMomentImprovedStatement s β := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  obtain ⟨CS, hCS, hSine⟩ := hS s hs0 hs2
  obtain ⟨CC, hCC, hCell⟩ := hC
  obtain ⟨CH, hCH, hHil⟩ := hH
  refine ⟨12 * CS ^ 2 * π * CH * 4 ^ s * CC, by positivity, fun m n hmn => ?_⟩
  obtain ⟨b, hb, hD, hbsum⟩ := hCell m
  have hL0 : (0 : ℝ) < 4 ^ m := by positivity
  set a : ℕ → ℝ := fun i => (2 * 4 ^ m * √(b i)) ^ s with hadef
  set κ : ℕ → ℕ → ℝ := fun i j =>
    12 * 4 ^ m / (π * ((i : ℝ) + j + 1)) * a i * a j * (1 / 4 ^ (n - m)) with hκdef
  have hy₀ : (0 : ℝ) < 3 / 8 / 4 ^ m := by positivity
  set c : ℝ := CS * π / 4 ^ m with hcdef
  have hreal : ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), κ i j * (c * c) ≤
      12 * CS ^ 2 * π * CH * 4 ^ s * CC * ((4 : ℝ) ^ m) ^ (2 * s - β) / 4 ^ (n - m) := by
    have hM : (0 : ℝ) < 4 ^ (n - m) := by positivity
    have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
    have hsq : ∀ i, a i ^ 2 = ((2 * 4 ^ m) ^ s) ^ 2 * b i ^ s := fun i => by
      simp only [hadef]
      rw [mul_rpow (by positivity) (sqrt_nonneg _), mul_pow, rpow_pow_comm (sqrt_nonneg _),
        sq_sqrt (hb i).le]
    have hexp := exponent_identity_improved m s β
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
            (CH * (((2 * 4 ^ m) ^ s) ^ 2 * ∑ i ∈ range (4 ^ m), b i ^ s)) := by
          simp_rw [hsq, ← mul_sum]
      _ ≤ 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) *
            (CH * (((2 * 4 ^ m) ^ s) ^ 2 * (CC * ((4 : ℝ) ^ m) ^ (1 - β)))) := by
          gcongr
      _ = 12 * 4 ^ m * c * c / (π * 4 ^ (n - m)) * CH * CC *
            (((2 * 4 ^ m) ^ s) ^ 2 * ((4 : ℝ) ^ m) ^ (1 - β)) := by
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
          fun i hi j hj p hp hpij => uv_pointwise_le hs0 hb hD hi hj hp hpij
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
