import FavardLength.Beyond.Statements
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The new exceptional-energy estimate

We prove `NewExceptionalStatement γ ε` from the exclusion contract `ExclusionStatement γ ε` and
the coverage contract `CoverageStatement` (beyond note §4, (16)–(19), and Appendix I.5).

Fix `H ≥ 1`, `B ≥ 2` and put `ℓ = log(2 + HB) ≥ 1`. Apply coverage with denominator scale
`R = B` and slope radius `r = c' H⁻⁴ B^{-1-2ε} ℓ⁻⁵`, where `c' = min(c_X, 1)/2` and `c_X` is the
exclusion radius constant. Then `r ≤ 1/B` and the local population is
`M = rB² = c' B^{1-2ε} H⁻⁴ ℓ⁻⁵`. Since `1 - 2ε = μ + (2d + 6γ + 2ε)` with
`μ = redundancyExp γ ε`, the redundancy hypothesis `C H⁸ ℓ⁹ ≤ B^μ` makes `B ≥ R₀`, `M ≥ M₀`, and
`c_V M` strictly larger than the exclusion count `C_X H⁴ B^{2d+6γ+2ε} ℓ⁴`. Hence every covered
slope `x ∈ [0,1]` has a nearby candidate pair `(p, q)` outside the exclusion set.

The slope-to-parameter map `φ(x) = (1 - x)/(1 + x)` is an involution of `[0, 1]`, is
`2`-Lipschitz on `[0, ∞)`, and sends `p/q` to `(q - p)/(q + p)`. So if `t ∈ [0,1]` has
`φ(t)` covered, exclusion forces `normEnergy N t > H`. The low-energy set therefore lies in
`φ '' (U ∩ [0,1])`, of measure at most `2 |U| ≤ 2 C_V/M`.

## Main results

* `Favard.NewExceptional.slopeMap`: the involution `x ↦ (1 - x)/(1 + x)`.
* `Favard.NewExceptional.volume_slopeMap_image_le`: `|φ '' (s ∩ [0,1])| ≤ 2 |s|`.
* `Favard.newExceptional_of`: `ExclusionStatement γ ε → CoverageStatement →
  NewExceptionalStatement γ ε`.
-/

open MeasureTheory Set Real

namespace Favard

namespace NewExceptional

/-- The slope-to-parameter map `x ↦ (1 - x)/(1 + x)`, an involution of `[0, 1]`. -/
noncomputable def slopeMap (x : ℝ) : ℝ :=
  (1 - x) / (1 + x)

/-- `φ` maps `[0, 1]` into itself. -/
lemma slopeMap_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : slopeMap x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [slopeMap, div_le_one (by linarith)]
  linarith

/-- `φ` is an involution of `[0, ∞)`. -/
lemma slopeMap_slopeMap {x : ℝ} (hx : 0 ≤ x) : slopeMap (slopeMap x) = x := by
  have h : (1 + x) ≠ 0 := by positivity
  simp only [slopeMap]
  field_simp
  ring

/-- `φ(p/q) = (q - p)/(q + p)`. -/
lemma slopeMap_div (p : ℝ) {q : ℝ} (hq : q ≠ 0) : slopeMap (p / q) = (q - p) / (q + p) := by
  rw [slopeMap, one_sub_div hq, one_add_div hq, div_div_div_cancel_right₀ hq]

/-- `φ` is `2`-Lipschitz on `[0, ∞)`. -/
lemma abs_slopeMap_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |slopeMap x - slopeMap y| ≤ 2 * |x - y| := by
  have hden : 1 ≤ (1 + x) * (1 + y) := by nlinarith
  have hxy : slopeMap x - slopeMap y = 2 * (y - x) / ((1 + x) * (1 + y)) := by
    have h1 : (1 + x) ≠ 0 := by positivity
    have h2 : (1 + y) ≠ 0 := by positivity
    simp only [slopeMap]
    field_simp
    ring
  rw [hxy, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (1 + x) * (1 + y)), abs_mul,
    abs_two, abs_sub_comm y x]
  exact div_le_self (by positivity) hden

/-- The image of `s ∩ [0, 1]` under `φ` has measure at most `2 |s|`. -/
lemma volume_slopeMap_image_le (s : Set ℝ) :
    volume (slopeMap '' (s ∩ Icc 0 1)) ≤ 2 * volume s := by
  have h : LipschitzOnWith 2 slopeMap (s ∩ Icc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simpa [Real.dist_eq] using abs_slopeMap_sub_le hx.2.1 hy.2.1
  have := h.hausdorffMeasure_image_le zero_le_one
  rw [hausdorffMeasure_real] at this
  refine this.trans ?_
  simp only [ENNReal.rpow_one, ENNReal.coe_ofNat]
  gcongr
  exact inter_subset_left

/-- `ℓ = log(2 + HB) ≥ 1` for `H ≥ 1`, `B ≥ 2`, since `2 + HB ≥ 4 > e`. -/
lemma one_le_log {H B : ℝ} (hH : 1 ≤ H) (hB : 2 ≤ B) : 1 ≤ Real.log (2 + H * B) := by
  have h4 : 4 ≤ 2 + H * B := by nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three]

end NewExceptional

open NewExceptional in
/-- **The new exceptional-energy estimate** (beyond note (18)) from smooth-window exclusion and
redundant odd/odd rational coverage. -/
theorem newExceptional_of {γ ε : ℝ} (hγ0 : 0 < γ) (_hγ2 : γ < 2) (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (hμ : 0 < redundancyExp γ ε) (hX : ExclusionStatement γ ε) (hC : CoverageStatement) :
    NewExceptionalStatement γ ε := by
  obtain ⟨CX, cX, hCX, hcX, hXprop⟩ := hX
  obtain ⟨R₀, M₀, CV, cV, hCV, hcV, hCov⟩ := hC
  set c' : ℝ := min cX 1 / 2 with hc'
  have hc'0 : 0 < c' := by positivity
  have hc'1 : c' ≤ 1 / 2 := by
    rw [hc']; linarith [min_le_right cX 1]
  have hc'X : 2 * c' ≤ cX := by
    rw [hc']; linarith [min_le_left cX 1]
  set C : ℝ := max (max CX (2 * CX / (cV * c'))) (max (max (M₀ / c') R₀) (2 * CV / c')) with hCdef
  have hCX_le : CX ≤ C := le_max_of_le_left (le_max_left _ _)
  have hCX'_le : 2 * CX / (cV * c') ≤ C := le_max_of_le_left (le_max_right _ _)
  have hM₀_le : M₀ / c' ≤ C := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hR₀_le : R₀ ≤ C := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hCV_le : 2 * CV / c' ≤ C := le_max_of_le_right (le_max_right _ _)
  have hC0 : 0 < C := hCX.trans_le hCX_le
  refine ⟨C, hC0, fun H hH B hB hred N hN => ?_⟩
  obtain ⟨X, hXcard, hXexcl⟩ := hXprop H hH B hB
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hH0 : 0 < H := by linarith
  have hℓ1 : 1 ≤ Real.log (2 + H * B) := one_le_log hH hB
  set ℓ : ℝ := Real.log (2 + H * B) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hd : 0 ≤ sixthMomentDim := Real.logb_nonneg (by norm_num) (by norm_num)
  set a : ℝ := 2 * sixthMomentDim + 6 * γ + 2 * ε with ha
  have ha0 : 0 ≤ a := by linarith
  set μ : ℝ := redundancyExp γ ε with hμdef
  have hμa : μ + a = 1 - 2 * ε := by rw [hμdef, ha, redundancyExp]; ring
  have hμ1 : μ ≤ 1 := by linarith
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
  have hℓ4 : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
  have hBa : 1 ≤ B ^ a := Real.one_le_rpow hB1 ha0
  have hBμa : B ^ (1 - 2 * ε) = B ^ μ * B ^ a := by rw [← hμa, Real.rpow_add hB0]
  have hBμ : B ^ μ ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 hμ1
  have hCB : C ≤ B ^ μ := by
    calc C = C * 1 * 1 := by ring
      _ ≤ C * H ^ 8 * ℓ ^ 9 := by gcongr <;> exact one_le_pow₀ (by assumption)
      _ ≤ B ^ μ := hred
  have hkey : C * H ^ 8 * ℓ ^ 9 * B ^ a ≤ B ^ (1 - 2 * ε) := by
    rw [hBμa]; gcongr
  -- the slope radius `r = c' / den` and the population `M = r B²`
  set den : ℝ := H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5 with hden
  have hden0 : 0 < den := by positivity
  set r : ℝ := c' / den with hr
  have hr0 : 0 < r := div_pos hc'0 hden0
  have hBden : B ≤ den := by
    have : B ≤ B ^ (1 + 2 * ε) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : (1 : ℝ) ≤ 1 + 2 * ε)
    calc B = 1 * B * 1 := by ring
      _ ≤ H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5 := by gcongr; exact one_le_pow₀ hℓ1
  have hrB : r ≤ B⁻¹ := by
    calc r = c' / den := rfl
      _ ≤ 1 / den := by gcongr; linarith
      _ ≤ 1 / B := by gcongr
      _ = B⁻¹ := one_div B
  have hM : r * B ^ 2 * (H ^ 4 * ℓ ^ 5) = c' * B ^ (1 - 2 * ε) := by
    have hsplit : B ^ 2 = B ^ (1 + 2 * ε) * B ^ (1 - 2 * ε) := by
      rw [← Real.rpow_add hB0, show 1 + 2 * ε + (1 - 2 * ε) = (2 : ℝ) by ring, Real.rpow_two]
    have : B ^ (1 + 2 * ε) ≠ 0 := by positivity
    rw [hsplit, hr, hden]
    field_simp
  have hMlow : c' * C ≤ r * B ^ 2 := by
    have hpos : 0 < H ^ 4 * ℓ ^ 5 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hpos, hM]
    have h1 : 1 ≤ H ^ 4 * ℓ ^ 4 * B ^ a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH4 hℓ4) hBa
    calc c' * C * (H ^ 4 * ℓ ^ 5) = c' * C * (H ^ 4 * ℓ ^ 5) * 1 := by ring
      _ ≤ c' * C * (H ^ 4 * ℓ ^ 5) * (H ^ 4 * ℓ ^ 4 * B ^ a) := by gcongr
      _ = c' * (C * H ^ 8 * ℓ ^ 9 * B ^ a) := by ring
      _ ≤ c' * B ^ (1 - 2 * ε) := by gcongr
  have hM₀ : M₀ ≤ r * B ^ 2 := by
    calc M₀ = c' * (M₀ / c') := by field_simp
      _ ≤ c' * C := by gcongr
      _ ≤ r * B ^ 2 := hMlow
  have hR₀ : R₀ ≤ B := hR₀_le.trans (hCB.trans hBμ)
  obtain ⟨U, hUvol, hUcov⟩ := hCov B r hR₀ hr0 hrB hM₀
  -- the exclusion count is smaller than the coverage population
  have hXlt : (X.card : ℝ) < cV * (r * B ^ 2) := by
    have h2 : 2 * CX ≤ cV * c' * C := by
      have := hCX'_le
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hP : 0 < H ^ 8 * ℓ ^ 9 * B ^ a := by positivity
    have hlt : (X.card : ℝ) * (H ^ 4 * ℓ ^ 5) < cV * (r * B ^ 2) * (H ^ 4 * ℓ ^ 5) := by
      calc (X.card : ℝ) * (H ^ 4 * ℓ ^ 5)
          ≤ CX * H ^ 4 * B ^ a * ℓ ^ 4 * (H ^ 4 * ℓ ^ 5) := by gcongr
        _ = CX * (H ^ 8 * ℓ ^ 9 * B ^ a) := by ring
        _ < 2 * CX * (H ^ 8 * ℓ ^ 9 * B ^ a) := by nlinarith
        _ ≤ cV * c' * C * (H ^ 8 * ℓ ^ 9 * B ^ a) := by gcongr
        _ = cV * c' * (C * H ^ 8 * ℓ ^ 9 * B ^ a) := by ring
        _ ≤ cV * c' * B ^ (1 - 2 * ε) := by gcongr
        _ = cV * (r * B ^ 2) * (H ^ 4 * ℓ ^ 5) := by rw [mul_assoc cV c', ← hM]; ring
    exact lt_of_mul_lt_mul_right hlt (by positivity)
  -- low-energy parameters come from covered slopes
  have hsub : {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} ⊆ slopeMap '' (U ∩ Icc 0 1) := by
    rintro t ⟨ht, hE⟩
    refine ⟨slopeMap t, ⟨?_, slopeMap_mem_Icc ht⟩, slopeMap_slopeMap ht.1⟩
    by_contra hU
    have hcard := hUcov (slopeMap t) ⟨slopeMap_mem_Icc ht, hU⟩
    obtain ⟨⟨p, q⟩, hpq, hpqX⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card ((Nat.cast_lt (α := ℝ)).mp (hXlt.trans_le hcard))
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
    obtain ⟨⟨-, hq⟩, hpodd, hqodd, hcop, hpq_le, -, hdist⟩ := hpq
    have hqB : (q : ℝ) ≤ B :=
      (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hq)).trans (Nat.floor_le hB0.le)
    have hq0 : (q : ℝ) ≠ 0 := by have := hqodd.pos; positivity
    refine hE.not_gt (hXexcl p q hpodd hqodd hcop hpq_le hqB hpqX N ?_ t ht ?_)
    · exact le_trans (by gcongr) hN
    · calc |t - ((q : ℝ) - p) / ((q : ℝ) + p)|
          = |slopeMap (slopeMap t) - slopeMap ((p : ℝ) / q)| := by
            rw [slopeMap_slopeMap ht.1, slopeMap_div _ hq0]
        _ ≤ 2 * |slopeMap t - (p : ℝ) / q| :=
            abs_slopeMap_sub_le (slopeMap_mem_Icc ht).1 (by positivity)
        _ ≤ 2 * r := by gcongr
        _ = 2 * c' / den := by rw [hr]; ring
        _ ≤ cX / den := by gcongr
  -- the measure bound
  have hBpos : 0 < B ^ (1 - 2 * ε) := by positivity
  have hMeq : r * B ^ 2 = c' * B ^ (1 - 2 * ε) / (H ^ 4 * ℓ ^ 5) := by
    rw [← hM]; field_simp
  have hCVc : 2 * CV ≤ C * c' := by
    have := hCV_le
    rw [div_le_iff₀ hc'0] at this
    linarith
  calc volume {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H}
      ≤ volume (slopeMap '' (U ∩ Icc 0 1)) := measure_mono hsub
    _ ≤ 2 * volume U := volume_slopeMap_image_le U
    _ ≤ 2 * ENNReal.ofReal (CV / (r * B ^ 2)) := by gcongr
    _ = ENNReal.ofReal (2 * (CV / (r * B ^ 2))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (C * H ^ 4 * ℓ ^ 5 / B ^ (1 - 2 * ε)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hMeq, show 2 * (CV / (c' * B ^ (1 - 2 * ε) / (H ^ 4 * ℓ ^ 5))) =
          2 * CV * (H ^ 4 * ℓ ^ 5) / (c' * B ^ (1 - 2 * ε)) by field_simp,
          div_le_div_iff₀ (by positivity) hBpos]
        calc 2 * CV * (H ^ 4 * ℓ ^ 5) * B ^ (1 - 2 * ε)
            ≤ C * c' * (H ^ 4 * ℓ ^ 5) * B ^ (1 - 2 * ε) := by gcongr
          _ = C * H ^ 4 * ℓ ^ 5 * (c' * B ^ (1 - 2 * ε)) := by ring

end Favard
