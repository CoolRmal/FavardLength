import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The change of variables `u = y(1+t)`, `v = y(1-t)`

For the joint negative moment (manuscript J8) we pass from the variables `(t, y)` to
`(u, v) = (y(1+t), y(1-t))`. The Jacobian determinant of `(t, y) ↦ (u, v)` is `2y = u + v`, so
`dy dt = du dv / (u + v)`. We prove the resulting `lintegral` identity on the rectangle
`[0, 1] × [y₀, 1]` (`y₀ > 0`), and locate the image in `[y₀, 2] × [0, 1]`.
-/

open MeasureTheory Set

open scoped ENNReal

namespace Favard

namespace JointMoment

/-- The map `(t, y) ↦ (y(1+t), y(1-t))`. -/
def uvMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2 * (1 + p.1), p.2 * (1 - p.1))

/-- The derivative of `uvMap` at `p = (t, y)`: the matrix `[[y, 1 + t], [-y, 1 - t]]`. -/
noncomputable def uvDeriv (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, 1 + p.1; -p.2, 1 - p.1]).toContinuousLinearMap

lemma hasFDerivAt_uvMap (p : ℝ × ℝ) : HasFDerivAt uvMap (uvDeriv p) p := by
  unfold uvDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.2 * (1 + q.1))
      (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 + p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hasFDerivAt_snd (p := p)).mul ((hasFDerivAt_fst (p := p)).const_add 1)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2 * (1 - q.1))
      (-p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd
    have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hasFDerivAt_fst
    convert hs.mul (hf.const_sub 1) using 1
    ext <;> simp
  exact h1.prodMk h2

/-- The Jacobian determinant of `uvMap` is `2y`. -/
lemma det_uvDeriv (p : ℝ × ℝ) : (uvDeriv p).det = 2 * p.2 := by
  unfold uvDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

lemma injOn_uvMap {y₀ : ℝ} (hy₀ : 0 < y₀) : InjOn uvMap (Icc 0 1 ×ˢ Icc y₀ 1) := by
  rintro ⟨t, y⟩ ⟨-, hy, -⟩ ⟨t', y'⟩ - h
  simp only [uvMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hyy : y = y' := by linarith
  subst hyy
  have : y * t = y * t' := by linarith
  exact Prod.ext (mul_left_cancel₀ (by linarith) this) rfl

lemma continuous_uvMap : Continuous uvMap := by
  unfold uvMap
  fun_prop

/-- The image of `[0, 1] × [y₀, 1]` under `uvMap` lies in `[y₀, 2] × [0, 1]`. -/
lemma uvMap_image_subset {y₀ : ℝ} (hy₀ : 0 < y₀) :
    uvMap '' (Icc 0 1 ×ˢ Icc y₀ 1) ⊆ Icc y₀ 2 ×ˢ Icc 0 1 := by
  rintro _ ⟨⟨t, y⟩, ⟨⟨ht0, ht1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
  simp only [uvMap, mem_prod, mem_Icc]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- **Change of variables** `u = y(1+t)`, `v = y(1-t)`, `dy dt = du dv / (u + v)`. -/
theorem lintegral_comp_uvMap {y₀ : ℝ} (hy₀ : 0 < y₀) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Icc y₀ 1, F (y * (1 + t), y * (1 - t)) =
      ∫⁻ p in uvMap '' (Icc 0 1 ×ˢ Icc y₀ 1), ENNReal.ofReal (1 / (p.1 + p.2)) * F p := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Icc.prod measurableSet_Icc)
    (fun p _ => (hasFDerivAt_uvMap p).hasFDerivWithinAt) (injOn_uvMap hy₀),
    Measure.volume_eq_prod, setLIntegral_prod]
  · refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
    have hy' : 0 < y := hy₀.trans_le hy.1
    simp only [det_uvDeriv, uvMap]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity),
      show y * (1 + t) + y * (1 - t) = 2 * y by ring, mul_one_div_cancel (by positivity),
      ENNReal.ofReal_one, one_mul]
  · simp only [det_uvDeriv]
    refine Measurable.aemeasurable ?_
    refine Measurable.mul ?_ (Measurable.mul ?_ (hF.comp continuous_uvMap.measurable))
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · refine ENNReal.measurable_ofReal.comp ?_
      have := continuous_uvMap.measurable
      fun_prop

end JointMoment

end Favard
