import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# A layer-cake bound for bounded functions on an interval

For a measurable function `0 ≤ f ≤ U` on `[0, b]` whose superlevel sets satisfy
`|{θ ∈ [0, b] : f θ > t}| ≤ M t^{-σ}` for `T₀ ≤ t < U` (with `σ < 1`), the layer-cake formula
`∫ f = ∫_0^∞ |{f > t}| dt` gives
`∫_0^b f ≤ b T₀ + M ∫_0^U t^{-σ} dt`:
the levels `t < T₀` contribute at most `b T₀`, the levels `T₀ ≤ t < U` contribute at most the
integral of the tail bound, and the levels `t ≥ U` contribute nothing.

This is the integration step of manuscript (J11).
-/

open MeasureTheory Set Real

namespace Favard.Decay

/-- **Layer-cake bound.** If `0 ≤ f ≤ U` is measurable and its superlevel sets in `[0, b]` have
measure at most `M t^{-σ}` for `T₀ ≤ t < U`, where `σ < 1`, then
`∫_0^b f ≤ b T₀ + M ∫_0^U t^{-σ} dt`. -/
theorem intervalIntegral_le_of_meas_lt_le {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    {b T₀ U M σ : ℝ} (hb : 0 ≤ b) (hT₀ : 0 ≤ T₀) (hU : 0 ≤ U) (hM : 0 ≤ M) (hσ : σ < 1)
    (hfU : ∀ θ, f θ ≤ U)
    (h : ∀ t, T₀ ≤ t → t < U →
      volume {θ ∈ Icc 0 b | t < f θ} ≤ ENNReal.ofReal (M * t ^ (-σ))) :
    ∫ θ in (0)..b, f θ ≤ b * T₀ + M * ∫ t in (0)..U, t ^ (-σ) := by
  have hI : 0 ≤ ∫ t in (0)..U, t ^ (-σ) :=
    intervalIntegral.integral_nonneg hU fun t ht => rpow_nonneg ht.1 _
  have hint : IntegrableOn (fun t : ℝ => M * t ^ (-σ)) (Ioc 0 U) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := U)
      (show -1 < -σ by linarith)).const_mul M
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).1 this
  rw [intervalIntegral.integral_of_le hb,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall hf0) hf.aemeasurable]
  set G : ℝ → ENNReal := fun t => ENNReal.ofReal (M * t ^ (-σ)) with hG
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (volume.restrict (Ioc 0 b)) {θ | t < f θ} ≤
      (Iio T₀).indicator (fun _ => ENNReal.ofReal b) t + (Iio U).indicator G t := by
    intro t _
    rw [Measure.restrict_apply' measurableSet_Ioc]
    rcases lt_or_ge t T₀ with htT | htT
    · calc volume ({θ | t < f θ} ∩ Ioc 0 b) ≤ volume (Ioc 0 b) :=
            measure_mono inter_subset_right
        _ = ENNReal.ofReal b := by rw [Real.volume_Ioc, sub_zero]
        _ ≤ _ := by
            rw [indicator_of_mem (show t ∈ Iio T₀ from htT)]
            exact le_self_add
    rcases lt_or_ge t U with htU | htU
    · calc volume ({θ | t < f θ} ∩ Ioc 0 b) ≤ volume {θ ∈ Icc 0 b | t < f θ} := by
            refine measure_mono fun θ hθ => ⟨Ioc_subset_Icc_self hθ.2, hθ.1⟩
        _ ≤ G t := h t htT htU
        _ ≤ _ := by
            rw [indicator_of_mem (show t ∈ Iio U from htU)]
            exact le_add_self
    · have : {θ | t < f θ} ∩ Ioc 0 b = ∅ := by
        ext θ
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hθ
        linarith [hfU θ]
      rw [this, measure_empty]
      exact zero_le
  calc ∫⁻ t in Ioi 0, (volume.restrict (Ioc 0 b)) {θ | t < f θ}
      ≤ ∫⁻ t in Ioi 0,
          ((Iio T₀).indicator (fun _ => ENNReal.ofReal b) t + (Iio U).indicator G t) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ t in Ioi 0, (Iio T₀).indicator (fun _ => ENNReal.ofReal b) t) +
          ∫⁻ t in Ioi 0, (Iio U).indicator G t :=
        lintegral_add_left (μ := volume.restrict (Ioi 0))
          (f := (Iio T₀).indicator (fun _ => ENNReal.ofReal b))
          (measurable_const.indicator measurableSet_Iio) ((Iio U).indicator G)
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal T₀ + ENNReal.ofReal (M * ∫ t in (0)..U, t ^ (-σ)) := by
        refine add_le_add ?_ ?_
        · rw [lintegral_indicator measurableSet_Iio, setLIntegral_const,
            Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
        · rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
            Iio_inter_Ioi]
          calc ∫⁻ t in Ioo 0 U, G t ≤ ∫⁻ t in Ioc 0 U, G t := lintegral_mono_set Ioo_subset_Ioc_self
            _ = ENNReal.ofReal (∫ t in Ioc 0 U, M * t ^ (-σ)) := by
                rw [ofReal_integral_eq_lintegral_ofReal hint]
                refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
                intro t ht
                exact mul_nonneg hM (rpow_nonneg ht.1.le _)
            _ = ENNReal.ofReal (M * ∫ t in (0)..U, t ^ (-σ)) := by
                rw [← intervalIntegral.integral_of_le hU, intervalIntegral.integral_const_mul]
    _ = ENNReal.ofReal (b * T₀ + M * ∫ t in (0)..U, t ^ (-σ)) := by
        rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end Favard.Decay
