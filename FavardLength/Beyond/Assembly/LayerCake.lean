import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A layer-cake bound with two power tails

For a measurable function `0 ≤ f ≤ U` on `[0, b]`, suppose that the superlevel sets
`{θ ∈ [0, b] : f θ > t}` have measure at most `M₁ t^{-σ₁}` for levels `T₀ ≤ t < T₁` and at most
`M₂ t^{-σ₂}` for levels `t ≥ max T₀ T₁`, where `σ₁ < 1 < σ₂`. The layer-cake formula
`∫ f = ∫_0^∞ |{f > t}| dt` then gives
`∫_0^b f ≤ b T₀ + M₁ T₁^{1-σ₁}/(1-σ₁) + M₂ T₁^{1-σ₂}/(σ₂-1)`:
the levels below `T₀` contribute at most `b T₀`, the first tail is integrable at `0` and the
second at `∞`, and the levels `t ≥ U` contribute nothing.

This is the layer-cake step of the beyond note §5, with the old tail below the splitting level
`T₁ ≍ P^{-z}` and the new tail above it.
-/

open MeasureTheory Set Real

namespace Favard.Assembly

/-- `∫_{(0, T]} M t^{-σ} dt = M T^{1-σ}/(1-σ)` in `ℝ≥0∞`, for `σ < 1`. -/
lemma lintegral_Ioc_rpow {T M σ : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hσ : σ < 1) :
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal (M * t ^ (-σ)) =
      ENNReal.ofReal (M * (T ^ (1 - σ) / (1 - σ))) := by
  have hint : IntegrableOn (fun t : ℝ => M * t ^ (-σ)) (Ioc 0 T) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
      (show -1 < -σ by linarith)).const_mul M
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 this
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith)), zero_rpow (by linarith), sub_zero,
      show -σ + 1 = 1 - σ by ring]
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact mul_nonneg hM (rpow_nonneg ht.1.le _)

/-- `∫_{[T, ∞)} M t^{-σ} dt = M T^{1-σ}/(σ-1)` in `ℝ≥0∞`, for `σ > 1`. -/
lemma lintegral_Ici_rpow {T M σ : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hσ : 1 < σ) :
    ∫⁻ t in Ici T, ENNReal.ofReal (M * t ^ (-σ)) =
      ENNReal.ofReal (M * (T ^ (1 - σ) / (σ - 1))) := by
  have hint : IntegrableOn (fun t : ℝ => M * t ^ (-σ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (show -σ < -1 by linarith) hT).const_mul M
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (show -σ < -1 by linarith) hT,
      show -σ + 1 = 1 - σ by ring, neg_div, ← div_neg, neg_sub]
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact mul_nonneg hM (rpow_nonneg (hT.trans ht).le _)

/-- **Layer-cake bound with two power tails.** If `0 ≤ f ≤ U` is measurable and its superlevel
sets in `[0, b]` have measure at most `M₁ t^{-σ₁}` for `T₀ ≤ t < T₁` and at most `M₂ t^{-σ₂}`
for `T₀ ≤ t`, `T₁ ≤ t`, where `σ₁ < 1 < σ₂`, then
`∫_0^b f ≤ b T₀ + M₁ T₁^{1-σ₁}/(1-σ₁) + M₂ T₁^{1-σ₂}/(σ₂-1)`. -/
theorem intervalIntegral_le_of_two_tails {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    {b T₀ T₁ U M₁ M₂ σ₁ σ₂ : ℝ} (hb : 0 ≤ b) (hT₀ : 0 ≤ T₀) (hT₁ : 0 < T₁) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (hσ₁ : σ₁ < 1) (hσ₂ : 1 < σ₂) (hfU : ∀ θ, f θ ≤ U)
    (h₁ : ∀ t, T₀ ≤ t → t < T₁ → t < U →
      volume {θ ∈ Icc 0 b | t < f θ} ≤ ENNReal.ofReal (M₁ * t ^ (-σ₁)))
    (h₂ : ∀ t, T₀ ≤ t → T₁ ≤ t → t < U →
      volume {θ ∈ Icc 0 b | t < f θ} ≤ ENNReal.ofReal (M₂ * t ^ (-σ₂))) :
    ∫ θ in (0)..b, f θ ≤
      b * T₀ + M₁ * (T₁ ^ (1 - σ₁) / (1 - σ₁)) + M₂ * (T₁ ^ (1 - σ₂) / (σ₂ - 1)) := by
  have hI₁ : 0 ≤ M₁ * (T₁ ^ (1 - σ₁) / (1 - σ₁)) :=
    mul_nonneg hM₁ (div_nonneg (rpow_nonneg hT₁.le _) (by linarith))
  have hI₂ : 0 ≤ M₂ * (T₁ ^ (1 - σ₂) / (σ₂ - 1)) :=
    mul_nonneg hM₂ (div_nonneg (rpow_nonneg hT₁.le _) (by linarith))
  rw [intervalIntegral.integral_of_le hb,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall hf0) hf.aemeasurable]
  set G₁ : ℝ → ENNReal := fun t => ENNReal.ofReal (M₁ * t ^ (-σ₁)) with hG₁
  set G₂ : ℝ → ENNReal := fun t => ENNReal.ofReal (M₂ * t ^ (-σ₂)) with hG₂
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (volume.restrict (Ioc 0 b)) {θ | t < f θ} ≤
      (Iio T₀).indicator (fun _ => ENNReal.ofReal b) t +
        ((Iio T₁).indicator G₁ t + (Ici T₁).indicator G₂ t) := by
    intro t _
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub : {θ | t < f θ} ∩ Ioc 0 b ⊆ {θ ∈ Icc 0 b | t < f θ} :=
      fun θ hθ => ⟨Ioc_subset_Icc_self hθ.2, hθ.1⟩
    rcases lt_or_ge t T₀ with htT | htT
    · calc volume ({θ | t < f θ} ∩ Ioc 0 b) ≤ volume (Ioc 0 b) :=
            measure_mono inter_subset_right
        _ = ENNReal.ofReal b := by rw [Real.volume_Ioc, sub_zero]
        _ ≤ _ := by
            rw [indicator_of_mem (show t ∈ Iio T₀ from htT)]
            exact le_self_add
    rcases lt_or_ge t U with htU | htU
    · rcases lt_or_ge t T₁ with ht₁ | ht₁
      · calc volume ({θ | t < f θ} ∩ Ioc 0 b) ≤ G₁ t :=
              (measure_mono hsub).trans (h₁ t htT ht₁ htU)
          _ ≤ (Iio T₁).indicator G₁ t + (Ici T₁).indicator G₂ t := by
              rw [indicator_of_mem (show t ∈ Iio T₁ from ht₁)]
              exact le_self_add
          _ ≤ _ := le_add_self
      · calc volume ({θ | t < f θ} ∩ Ioc 0 b) ≤ G₂ t :=
              (measure_mono hsub).trans (h₂ t htT ht₁ htU)
          _ ≤ (Iio T₁).indicator G₁ t + (Ici T₁).indicator G₂ t := by
              rw [indicator_of_mem (show t ∈ Ici T₁ from ht₁)]
              exact le_add_self
          _ ≤ _ := le_add_self
    · have : {θ | t < f θ} ∩ Ioc 0 b = ∅ := by
        ext θ
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hθ
        linarith [hfU θ]
      rw [this, measure_empty]
      exact zero_le
  have hG₁m : Measurable G₁ :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  calc ∫⁻ t in Ioi 0, (volume.restrict (Ioc 0 b)) {θ | t < f θ}
      ≤ ∫⁻ t in Ioi 0, ((Iio T₀).indicator (fun _ => ENNReal.ofReal b) t +
          ((Iio T₁).indicator G₁ t + (Ici T₁).indicator G₂ t)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ t in Ioi 0, (Iio T₀).indicator (fun _ => ENNReal.ofReal b) t) +
          ((∫⁻ t in Ioi 0, (Iio T₁).indicator G₁ t) +
            ∫⁻ t in Ioi 0, (Ici T₁).indicator G₂ t) := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_Iio),
          lintegral_add_left (hG₁m.indicator measurableSet_Iio)]
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal T₀ +
          (ENNReal.ofReal (M₁ * (T₁ ^ (1 - σ₁) / (1 - σ₁))) +
            ENNReal.ofReal (M₂ * (T₁ ^ (1 - σ₂) / (σ₂ - 1)))) := by
        refine add_le_add ?_ (add_le_add ?_ ?_)
        · rw [lintegral_indicator measurableSet_Iio, setLIntegral_const,
            Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
        · rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
            Iio_inter_Ioi, ← lintegral_Ioc_rpow hT₁ hM₁ hσ₁]
          exact lintegral_mono_set Ioo_subset_Ioc_self
        · rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
            inter_eq_left.2 (Ici_subset_Ioi.2 hT₁), lintegral_Ici_rpow hT₁ hM₂ hσ₂]
    _ = ENNReal.ofReal (b * T₀ + M₁ * (T₁ ^ (1 - σ₁) / (1 - σ₁)) +
          M₂ * (T₁ ^ (1 - σ₂) / (σ₂ - 1))) := by
        rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add hI₁ hI₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity), add_assoc]

end Favard.Assembly
