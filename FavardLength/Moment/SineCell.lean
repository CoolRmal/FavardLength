import FavardLength.Moment.SineCell.Mass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The sine-cell inverse moment weighted by the Riesz product (J2–J3)

We prove `Favard.sineCell_of : MeanOneStatement → SineCellStatement`: for `0 < s < 1/2` there is
`C` such that for all `m, n` and every cell `I_i = [iπ/L, (i+1)π/L]`, `L = 4^m`,
`∫_{I_i} |sin(Lw)|^{-s} R(w) dw ≤ C π / L`, where `R = riesz m n` (the reciprocal power is taken
in `ℝ≥0∞`).

Instead of the layer-cake identity of the manuscript we use a dyadic-type decomposition:

* Jordan's inequality gives `|sin(Lw)| ≥ min(κ|w - c₁|, κ|w - c₂|)` on `I_i`, with `κ = 2L/π` and
  `c₁, c₂` the endpoints of the cell, so the weight is at most the sum of the two endpoint
  weights `(κ|w - c|)^{-s}`;
* near one endpoint `c`, the layer `{4^{-k} < κ|w - c| ≤ 4^{1-k}}` carries weight at most
  `(4^s)^k` and, by the short-interval mass bound (P4) with `j = k`, Riesz mass at most
  `2^{-k} (8/κ + 2π/4^{m+1})`; the layers are summable because `4^s/2 < 1`, i.e. `s < 1/2`.
-/

open MeasureTheory Set Real

namespace Favard

namespace SineCell

/-- For a nonnegative exponent `s`, `x ↦ x ^ (-s)` is antitone on `ℝ≥0∞`. -/
lemma rpow_neg_le_rpow_neg {x y : ENNReal} {s : ℝ} (hs : 0 ≤ s) (h : x ≤ y) :
    y ^ (-s) ≤ x ^ (-s) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h hs)

/-- Every `x ∈ (0, 4]` lies in a layer `(4^{-k}, 4^{1-k}]`. -/
lemma exists_layer {x : ℝ} (hx0 : 0 < x) (hx4 : x ≤ 4) :
    ∃ k : ℕ, 1 / 4 ^ k < x ∧ x ≤ 4 / 4 ^ k := by
  classical
  have hex : ∃ k : ℕ, 1 / (4 : ℝ) ^ k < x := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hx0 (by norm_num : (1 / 4 : ℝ) < 1)
    exact ⟨k, by simpa [div_pow] using hk⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    simpa using hx4
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at hmin
    rw [hk]
    calc x ≤ 1 / 4 ^ k := hmin
      _ = 4 / 4 ^ (k + 1) := by rw [pow_succ]; field_simp

/-- The weight `x ^ (-s)` on the layer `x > 4^{-k}` is at most `(4^s)^k`. -/
lemma ofReal_rpow_neg_le_of_layer {x s : ℝ} (hs : 0 ≤ s) (k : ℕ) (hx : 1 / 4 ^ k < x) :
    ENNReal.ofReal x ^ (-s) ≤ ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) := by
  have hpos : (0 : ℝ) < 1 / 4 ^ k := by positivity
  calc ENNReal.ofReal x ^ (-s) ≤ ENNReal.ofReal (1 / 4 ^ k) ^ (-s) :=
        rpow_neg_le_rpow_neg hs (ENNReal.ofReal_le_ofReal hx.le)
    _ = ENNReal.ofReal ((1 / 4 ^ k) ^ (-s)) := ENNReal.ofReal_rpow_of_pos hpos
    _ = ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) := by
        congr 1
        rw [Real.rpow_neg hpos.le, one_div, Real.inv_rpow (by positivity), inv_inv,
          Real.rpow_pow_comm (by norm_num)]

/-- **Inverse moment near one point** (J3 at one endpoint): the Riesz product weighted by
`(κ|w - c|)^{-s}` has integral `O(1/κ + 4^{-m})` over `[c - 4/κ, c + 4/κ]`. -/
lemma lintegral_rpow_neg_dist_mul_riesz_le (hM : MeanOneStatement) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : (4 : ℝ) ^ s / 2 < 1) (m n : ℕ) {κ : ℝ} (hκ : 0 < κ) (c : ℝ) :
    ∫⁻ w in Icc (c - 4 / κ) (c + 4 / κ),
        ENNReal.ofReal (κ * |w - c|) ^ (-s) * ENNReal.ofReal (riesz m n w) ≤
      ENNReal.ofReal ((8 / κ + 2 * π / 4 ^ (m + 1)) / (1 - 4 ^ s / 2)) := by
  set f : ℝ → ENNReal := fun w =>
    ENNReal.ofReal (κ * |w - c|) ^ (-s) * ENNReal.ofReal (riesz m n w)
  set A : ℕ → Set ℝ := fun k => {w | 1 / 4 ^ k < κ * |w - c| ∧ κ * |w - c| ≤ 4 / 4 ^ k}
  set ρ : ℝ := 4 ^ s / 2 with hρ
  set K : ℝ := 8 / κ + 2 * π / 4 ^ (m + 1) with hK
  have hρ0 : 0 ≤ ρ := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hcover : Icc (c - 4 / κ) (c + 4 / κ) ⊆ {c} ∪ ⋃ k, A k := by
    intro w hw
    by_cases hwc : w = c
    · exact Or.inl hwc
    · right
      have hpos : 0 < κ * |w - c| := mul_pos hκ (abs_pos.2 (sub_ne_zero.2 hwc))
      have hle : κ * |w - c| ≤ 4 := by
        have : |w - c| ≤ 4 / κ := abs_sub_le_iff.2 ⟨by linarith [hw.2], by linarith [hw.1]⟩
        calc κ * |w - c| ≤ κ * (4 / κ) := by gcongr
          _ = 4 := by field_simp
      obtain ⟨k, hk⟩ := exists_layer hpos hle
      exact mem_iUnion.2 ⟨k, hk⟩
  have hlayer : ∀ k, ∫⁻ w in A k, f w ≤ ENNReal.ofReal (K * ρ ^ k) := by
    intro k
    have hr : 0 ≤ 4 / 4 ^ k / κ := by positivity
    have hmeas : Measurable fun w => ENNReal.ofReal (riesz m n w) :=
      (measurable_riesz m n).ennreal_ofReal
    calc ∫⁻ w in A k, f w
        ≤ ∫⁻ w in A k, ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) * ENNReal.ofReal (riesz m n w) := by
          refine setLIntegral_mono (measurable_const.mul hmeas) fun w hw => ?_
          exact mul_le_mul_left (ofReal_rpow_neg_le_of_layer hs0 k hw.1) _
      _ ≤ ∫⁻ w in Icc (c - 4 / 4 ^ k / κ) (c + 4 / 4 ^ k / κ),
            ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) * ENNReal.ofReal (riesz m n w) := by
          refine lintegral_mono_set fun w hw => ?_
          have h2 : |w - c| ≤ 4 / 4 ^ k / κ := by
            rw [le_div_iff₀ hκ, mul_comm]
            exact hw.2
          exact ⟨by linarith [(abs_sub_le_iff.1 h2).2], by linarith [(abs_sub_le_iff.1 h2).1]⟩
      _ = ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) *
            ∫⁻ w in Icc (c - 4 / 4 ^ k / κ) (c + 4 / 4 ^ k / κ), ENNReal.ofReal (riesz m n w) :=
          lintegral_const_mul _ hmeas
      _ ≤ ENNReal.ofReal (((4 : ℝ) ^ s) ^ k) * ENNReal.ofReal (2 ^ k *
            ((c + 4 / 4 ^ k / κ) - (c - 4 / 4 ^ k / κ) + 2 * π / 4 ^ (m + k + 1))) := by
          gcongr
          exact lintegral_riesz_Icc_le hM m n k (by linarith)
      _ = ENNReal.ofReal (K * ρ ^ k) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
          have h5 : (4 : ℝ) ^ (m + k + 1) = 4 ^ (m + 1) * 4 ^ k := by
            rw [← pow_add]; ring_nf
          rw [hK, hρ, h5, h4, div_pow]
          field_simp
          ring
  calc ∫⁻ w in Icc (c - 4 / κ) (c + 4 / κ), f w
      ≤ ∫⁻ w in {c} ∪ ⋃ k, A k, f w := lintegral_mono_set hcover
    _ ≤ (∫⁻ w in ({c} : Set ℝ), f w) + ∫⁻ w in ⋃ k, A k, f w := lintegral_union_le _ _ _
    _ = ∫⁻ w in ⋃ k, A k, f w := by
        rw [Measure.restrict_eq_zero.2 Real.volume_singleton, lintegral_zero_measure, zero_add]
    _ ≤ ∑' k, ∫⁻ w in A k, f w := lintegral_iUnion_le _ _
    _ ≤ ∑' k, ENNReal.ofReal (K * ρ ^ k) := ENNReal.tsum_le_tsum hlayer
    _ = ENNReal.ofReal (∑' k, K * ρ ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hρ0 hs).mul_left K)).symm
    _ = ENNReal.ofReal (K / (1 - ρ)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hs, div_eq_mul_inv]

/-- Jordan's inequality on a cell: `|sin(Lw)|` dominates `κ` times the distance from `w` to the
nearer endpoint of `I_i = [iπ/L, (i+1)π/L]`, where `κ = 2L/π`. -/
lemma min_le_abs_sin {L w : ℝ} (hL : 0 < L) (i : ℕ)
    (hw : w ∈ Icc (i * π / L) ((i + 1) * π / L)) :
    min (2 * L / π * |w - i * π / L|) (2 * L / π * |w - (i + 1) * π / L|) ≤ |sin (L * w)| := by
  set x := L * w - i * π
  have hw1 : i * π ≤ L * w := by
    have := hw.1
    rw [div_le_iff₀ hL] at this
    linarith
  have hw2 : L * w ≤ (i + 1) * π := by
    have := hw.2
    rw [le_div_iff₀ hL] at this
    linarith
  have hx0 : 0 ≤ x := by linarith
  have hxπ : x ≤ π := by linarith
  have hsin : |sin (L * w)| = sin x := by
    have : L * w = x + ((i : ℤ) : ℝ) * π := by push_cast; ring
    rw [this, sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul,
      abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hx0 hxπ)]
  have h1 : 2 * L / π * |w - i * π / L| = 2 / π * x := by
    rw [abs_of_nonneg (by linarith [hw.1])]
    field_simp
    ring
  have h2 : 2 * L / π * |w - (i + 1) * π / L| = 2 / π * (π - x) := by
    rw [abs_of_nonpos (by linarith [hw.2])]
    field_simp
    ring
  rw [hsin, h1, h2]
  rcases le_total x (π / 2) with h | h
  · exact (min_le_left _ _).trans (mul_le_sin hx0 h)
  · refine (min_le_right _ _).trans ?_
    rw [← sin_pi_sub]
    exact mul_le_sin (by linarith) (by linarith)

end SineCell

open SineCell in
/-- **Sine-cell inverse moment** (P4, J2–J3): the mean-one lemma implies
`SineCellStatement`, with constant `C = 9 / (1 - 4^s/2)`. -/
theorem sineCell_of (hM : MeanOneStatement) : SineCellStatement := by
  intro s hs0 hs
  have hρ : (4 : ℝ) ^ s / 2 < 1 := by
    have h1 : (4 : ℝ) ^ s < 4 ^ (1 / 2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hρ' : 0 < 1 - (4 : ℝ) ^ s / 2 := by linarith
  refine ⟨9 / (1 - 4 ^ s / 2), div_pos (by norm_num) hρ', ?_⟩
  intro m n i _
  set L : ℝ := 4 ^ m with hLdef
  have hL : 0 < L := by positivity
  set κ : ℝ := 2 * L / π with hκdef
  have hκ : 0 < κ := by positivity
  set c₁ : ℝ := i * π / L with hc₁
  set c₂ : ℝ := (i + 1) * π / L with hc₂
  set g : ℝ → ℝ → ENNReal := fun c w =>
    ENNReal.ofReal (κ * |w - c|) ^ (-s) * ENNReal.ofReal (riesz m n w) with hg
  have hgm : ∀ c, Measurable (g c) := fun c => by
    have := measurable_riesz m n
    fun_prop
  have h4κ : 4 / κ = 2 * (π / L) := by
    rw [hκdef]
    field_simp
    ring
  have hπL : 0 ≤ π / L := by positivity
  have hc₂₁ : c₂ = c₁ + π / L := by rw [hc₁, hc₂]; ring
  have hsub₁ : Icc c₁ c₂ ⊆ Icc (c₁ - 4 / κ) (c₁ + 4 / κ) := by
    intro w hw
    rw [h4κ]
    constructor <;> linarith [hw.1, hw.2]
  have hsub₂ : Icc c₁ c₂ ⊆ Icc (c₂ - 4 / κ) (c₂ + 4 / κ) := by
    intro w hw
    rw [h4κ]
    constructor <;> linarith [hw.1, hw.2]
  have hend := fun c => lintegral_rpow_neg_dist_mul_riesz_le hM hs0.le hρ m n hκ c
  have hpt : ∀ w ∈ Icc c₁ c₂,
      ENNReal.ofReal |sin (L * w)| ^ (-s) * ENNReal.ofReal (riesz m n w) ≤ g c₁ w + g c₂ w := by
    intro w hw
    have hmin := min_le_abs_sin hL i hw
    rw [hg, ← add_mul]
    refine mul_le_mul_left ?_ _
    rcases le_total (κ * |w - c₁|) (κ * |w - c₂|) with h | h
    · rw [min_eq_left h] at hmin
      exact (rpow_neg_le_rpow_neg hs0.le (ENNReal.ofReal_le_ofReal hmin)).trans le_self_add
    · rw [min_eq_right h] at hmin
      exact (rpow_neg_le_rpow_neg hs0.le (ENNReal.ofReal_le_ofReal hmin)).trans le_add_self
  have hE : 0 ≤ (8 / κ + 2 * π / 4 ^ (m + 1)) / (1 - 4 ^ s / 2) := by positivity
  calc ∫⁻ w in Icc c₁ c₂, ENNReal.ofReal |sin (L * w)| ^ (-s) * ENNReal.ofReal (riesz m n w)
      ≤ ∫⁻ w in Icc c₁ c₂, (g c₁ w + g c₂ w) := setLIntegral_mono ((hgm c₁).add (hgm c₂)) hpt
    _ = (∫⁻ w in Icc c₁ c₂, g c₁ w) + ∫⁻ w in Icc c₁ c₂, g c₂ w := lintegral_add_left (hgm c₁) _
    _ ≤ (∫⁻ w in Icc (c₁ - 4 / κ) (c₁ + 4 / κ), g c₁ w) +
          ∫⁻ w in Icc (c₂ - 4 / κ) (c₂ + 4 / κ), g c₂ w :=
        add_le_add (lintegral_mono_set hsub₁) (lintegral_mono_set hsub₂)
    _ ≤ ENNReal.ofReal ((8 / κ + 2 * π / 4 ^ (m + 1)) / (1 - 4 ^ s / 2)) +
          ENNReal.ofReal ((8 / κ + 2 * π / 4 ^ (m + 1)) / (1 - 4 ^ s / 2)) :=
        add_le_add (hend c₁) (hend c₂)
    _ = ENNReal.ofReal (9 / (1 - 4 ^ s / 2) * π / L) := by
        rw [← ENNReal.ofReal_add hE hE]
        congr 1
        rw [pow_succ, ← hLdef, hκdef]
        field_simp
        ring

end Favard
