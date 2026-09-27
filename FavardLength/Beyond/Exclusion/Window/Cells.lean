import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Averaging cells

Elementary facts about the averaging cells `[c h, (c + 1) h]` of Appendix G §4:

* Cauchy–Schwarz for the absolute cell deviations, `∑_{c ∈ s} |d_c| ≤ √(#s ∑_{c ∈ s} d_c²)`;
* the cell integrals over a range of cells add up to the integral over their union;
* an integral over the line of a function vanishing outside `(a, b)` is the integral over
  `[a, b]`;
* the **averaging estimate on one cell**: replacing a nonnegative density by the constant `α`
  against a test function `φ` costs at most the oscillation of `φ` times the total mass, plus
  the cell deviation `|∫ g - α|cell||`.
-/

open MeasureTheory Set

namespace Favard.Exclusion

/-- **Cauchy–Schwarz for absolute deviations**: `∑_{i ∈ s} |d_i| ≤ B` whenever
`#s ∑_{i ∈ s} d_i² ≤ B²` and `0 ≤ B`. -/
lemma sum_abs_le_of_card_mul_sum_sq_le {ι : Type*} (s : Finset ι) (d : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (h : (s.card : ℝ) * ∑ i ∈ s, d i ^ 2 ≤ B ^ 2) : ∑ i ∈ s, |d i| ≤ B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) fun i => |d i|
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  exact (sq_le_sq₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) hB).1 (hcs.trans h)

/-- The integrals over the consecutive cells `[c h, (c + 1) h]`, `m ≤ c < n`, add up to the
integral over `[m h, n h]`. -/
lemma sum_integral_cells {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (h : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ c ∈ Finset.Ico m n, ∫ x in (c : ℝ) * h..((c : ℝ) + 1) * h, f x =
      ∫ x in (m : ℝ) * h..(n : ℝ) * h, f x := by
  have := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * h) hmn fun k _ => hf _ _
  push_cast at this
  exact this

/-- The integral of a function vanishing outside `(a, b)` is its integral over `[a, b]`. -/
lemma integral_eq_intervalIntegral_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∉ Ioo a b, f x = 0) :
    ∫ x, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hf x fun h => hx (Ioo_subset_Ioc_self h)).symm

/-- **Averaging on one cell**: for a nonnegative integrable `g`, a continuous test function `φ`
with `‖φ(a)‖ ≤ 1` and oscillation at most `M` on `[a, b]`, and `α ≥ 0`,
`‖∫_a^b φ g - α ∫_a^b φ‖ ≤ M (∫_a^b g + α(b - a)) + |∫_a^b g - α(b - a)|`. -/
lemma norm_integral_mul_sub_le {φ : ℝ → ℂ} {g : ℝ → ℝ} {a b M α : ℝ} (hab : a ≤ b)
    (hφ : Continuous φ) (hφa : ‖φ a‖ ≤ 1) (hφM : ∀ x ∈ Icc a b, ‖φ x - φ a‖ ≤ M)
    (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (hα : 0 ≤ α) :
    ‖(∫ x in a..b, φ x * (g x : ℂ)) - (α : ℂ) * ∫ x in a..b, φ x‖ ≤
      M * ((∫ x in a..b, g x) + α * (b - a)) + |(∫ x in a..b, g x) - α * (b - a)| := by
  have hM : 0 ≤ M := by simpa using hφM a (left_mem_Icc.2 hab)
  have hgc : IntervalIntegrable (fun x => (g x : ℂ)) volume a b :=
    hg.ofReal.intervalIntegrable
  have hφi : IntervalIntegrable φ volume a b := hφ.intervalIntegrable a b
  have hφg : IntervalIntegrable (fun x => φ x * (g x : ℂ)) volume a b :=
    hgc.continuousOn_mul hφ.continuousOn
  have hid : (∫ x in a..b, φ x * (g x : ℂ)) - (α : ℂ) * ∫ x in a..b, φ x =
      (∫ x in a..b, (φ x - φ a) * ((g x : ℂ) - α)) +
        φ a * (((∫ x in a..b, g x : ℝ) : ℂ) - α * (b - a)) := by
    have hpt : ∀ x, (φ x - φ a) * ((g x : ℂ) - α) =
        φ x * (g x : ℂ) - (α : ℂ) * φ x - φ a * (g x : ℂ) + φ a * α := fun x => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add ((hφg.sub (hφi.const_mul _)).sub (hgc.const_mul _))
        intervalIntegrable_const, intervalIntegral.integral_sub (hφg.sub (hφi.const_mul _))
        (hgc.const_mul _), intervalIntegral.integral_sub hφg (hφi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, intervalIntegral.integral_ofReal, Complex.real_smul]
    push_cast
    ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hb : IntervalIntegrable (fun x => M * (g x + α)) volume a b :=
      (hg.intervalIntegrable.add intervalIntegrable_const).const_mul M
    refine (intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall
      fun x hx => ?_) hb).trans (le_of_eq ?_)
    · rw [norm_mul]
      refine mul_le_mul (hφM x (Ioc_subset_Icc_self hx)) ?_ (norm_nonneg _) hM
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hg0 x), abs_of_nonneg hα])
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        hg.intervalIntegrable intervalIntegrable_const, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
  · have : ((∫ x in a..b, g x : ℝ) : ℂ) - α * (b - a) =
        (((∫ x in a..b, g x) - α * (b - a) : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, this, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) hφa

end Favard.Exclusion
