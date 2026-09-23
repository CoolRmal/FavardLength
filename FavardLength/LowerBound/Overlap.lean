import FavardLength.LowerBound.Angular
import FavardLength.LowerBound.Digits
import FavardLength.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The angular integral of the energy (L2)

For two depth-`n` squares `w, w'`, the overlap of their direction-`θ` projections is
`max 0 (σ 4^{-n} - |π_θ(corner w) - π_θ(corner w')|)`. We show that its integral over
`θ ∈ [0, π/4]` is at most `80 · 4^k / 16^n` when the codes first differ at level `k`, and at most
`80 / 4^n` when `w = w'`. Encoding both cases with the agreement weight
`∑_{j ≤ n} 4^j [w, w' agree below level j]` and counting agreeing pairs gives
`∫_0^{π/4} ∑_{w,w'} overlap ≤ 80 (n + 1)`.

Compared with the manuscript we bound the projected interval length `σ 4^{-n}` by `2 · 4^{-n}`
and use the angular separation lemma of `FavardLength.LowerBound.Angular` instead of an arcsine
computation; the constants are therefore cruder.
-/

open MeasureTheory Set Real

namespace Favard.LowerBound

/-- The overlap length of the direction-`θ` projections of the squares `w` and `w'` (valid for
`θ ∈ [0, π/2]`, where the projections are intervals of length `σ 4^{-n}`). -/
noncomputable def overlap {n : ℕ} (w w' : SqCode n) (θ : ℝ) : ℝ :=
  max 0 ((cos θ + sin θ) / 4 ^ n - |proj θ (corner w) - proj θ (corner w')|)

theorem continuous_overlap {n : ℕ} (w w' : SqCode n) : Continuous (overlap w w') := by
  unfold overlap proj
  fun_prop

theorem overlap_nonneg {n : ℕ} (w w' : SqCode n) (θ : ℝ) : 0 ≤ overlap w w' θ :=
  le_max_left _ _

theorem cos_add_sin_div_le (n : ℕ) (θ : ℝ) : (cos θ + sin θ) / 4 ^ n ≤ 2 / 4 ^ n :=
  div_le_div_of_nonneg_right (by linarith [cos_le_one θ, sin_le_one θ]) (by positivity)

theorem overlap_le {n : ℕ} (w w' : SqCode n) (θ : ℝ) : overlap w w' θ ≤ 2 / 4 ^ n := by
  unfold overlap
  refine max_le (by positivity) ?_
  linarith [cos_add_sin_div_le n θ, abs_nonneg (proj θ (corner w) - proj θ (corner w'))]

theorem overlap_eq_zero {n : ℕ} {w w' : SqCode n} {θ : ℝ}
    (h : 2 / 4 ^ n < |proj θ (corner w) - proj θ (corner w')|) : overlap w w' θ = 0 := by
  unfold overlap
  refine max_eq_left ?_
  linarith [cos_add_sin_div_le n θ]

theorem proj_sub_proj (θ : ℝ) (p q : ℝ × ℝ) :
    proj θ p - proj θ q = (p.1 - q.1) * cos θ + (p.2 - q.2) * sin θ := by
  unfold proj
  ring

/-- The agreement weight `∑_{j ≤ n} 4^j [w, w' agree below level j]`. -/
noncomputable def agreeWeight {n : ℕ} (w w' : SqCode n) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (4 : ℝ) ^ j * (if ∀ i : Fin n, (i : ℕ) < j → w i = w' i then 1 else 0)

theorem pow_le_agreeWeight {n : ℕ} {w w' : SqCode n} {j : ℕ} (hj : j ≤ n)
    (h : ∀ i : Fin n, (i : ℕ) < j → w i = w' i) : (4 : ℝ) ^ j ≤ agreeWeight w w' := by
  unfold agreeWeight
  have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hj)
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => ?_) hmem)
  · simp [eq_true h]
  · positivity

theorem agreeWeight_nonneg {n : ℕ} (w w' : SqCode n) : 0 ≤ agreeWeight w w' := by
  unfold agreeWeight
  exact Finset.sum_nonneg fun j _ => by positivity

/-- The trivial bound `∫_0^{π/4} overlap ≤ 2 · 4^{-n}`. -/
theorem integral_overlap_le_trivial {n : ℕ} (w w' : SqCode n) :
    ∫ θ in (0)..(π / 4), overlap w w' θ ≤ 2 / 4 ^ n := by
  have hpi : 0 ≤ π / 4 := by positivity
  calc ∫ θ in (0)..(π / 4), overlap w w' θ ≤ ∫ _ in (0)..(π / 4), (2 : ℝ) / 4 ^ n :=
        intervalIntegral.integral_mono_on hpi ((continuous_overlap w w').intervalIntegrable _ _)
          intervalIntegrable_const fun θ _ => overlap_le w w' θ
    _ = π / 4 * (2 / 4 ^ n) := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ 1 * (2 / 4 ^ n) := by gcongr; linarith [pi_le_four]
    _ = 2 / 4 ^ n := one_mul _

/-- If the overlap vanishes off an interval of length `2D` and is bounded by `δ`, its integral
over `[0, π/4]` is at most `2Dδ`. -/
theorem integral_overlap_le_of_support {n : ℕ} {w w' : SqCode n} {θ₀ D δ : ℝ} (hD : 0 ≤ D)
    (hδ : 0 ≤ δ) (h : ∀ θ ∈ Icc 0 (π / 4), overlap w w' θ ≤ (Icc (θ₀ - D) (θ₀ + D)).indicator
      (fun _ => δ) θ) :
    ∫ θ in (0)..(π / 4), overlap w w' θ ≤ 2 * D * δ := by
  have hpi : 0 ≤ π / 4 := by positivity
  set g : ℝ → ℝ := (Icc (θ₀ - D) (θ₀ + D)).indicator (fun _ => δ) with hg
  have hgi : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => indicator_nonneg (fun _ _ => hδ) θ
  rw [intervalIntegral.integral_of_le hpi]
  calc ∫ θ in Ioc 0 (π / 4), overlap w w' θ ≤ ∫ θ in Ioc 0 (π / 4), g θ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => overlap_nonneg w w' θ)
          hgi.restrict ?_
        exact (ae_restrict_mem measurableSet_Ioc).mono fun θ hθ => h θ (Ioc_subset_Icc_self hθ)
    _ ≤ ∫ θ, g θ := setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
    _ = 2 * D * δ := by
        rw [hg, integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
          volume_real_Icc_of_le (by linarith)]
        ring

/-- **Pair estimate (L2).** The angular integral of the overlap of two squares is at most
`80 · 16^{-n}` times their agreement weight. -/
theorem integral_overlap_le {n : ℕ} (w w' : SqCode n) :
    ∫ θ in (0)..(π / 4), overlap w w' θ ≤ 80 / (4 ^ n * 4 ^ n) * agreeWeight w w' := by
  have hN : (0 : ℝ) < 4 ^ n := by positivity
  have htriv := integral_overlap_le_trivial w w'
  by_cases hww : w = w'
  · -- diagonal pair
    have hW : (4 : ℝ) ^ n ≤ agreeWeight w w' :=
      pow_le_agreeWeight le_rfl fun i _ => by rw [hww]
    refine htriv.trans ?_
    calc (2 : ℝ) / 4 ^ n ≤ 80 / (4 ^ n * 4 ^ n) * 4 ^ n := by
          rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hN.ne']
          gcongr
          norm_num
      _ ≤ 80 / (4 ^ n * 4 ^ n) * agreeWeight w w' := by gcongr
  · obtain ⟨k, hlt, hk⟩ := exists_first_diff hww
    have hW : (4 : ℝ) ^ (k : ℕ) ≤ agreeWeight w w' :=
      pow_le_agreeWeight k.isLt.le fun i hi => hlt i hi
    have ha : (0 : ℝ) < 4 ^ (k : ℕ) := by positivity
    suffices hmain : ∫ θ in (0)..(π / 4), overlap w w' θ ≤ 80 / (4 ^ n * 4 ^ n) * 4 ^ (k : ℕ) by
      exact hmain.trans (by gcongr)
    set a : ℝ := 4 ^ (k : ℕ) with ha_def
    set N : ℝ := 4 ^ n with hN_def
    set d : ℝ := 1 / (2 * a) with hd_def
    set δ : ℝ := 2 / N with hδ_def
    have hd : 0 < d := by positivity
    have hδ0 : 0 ≤ δ := by positivity
    set v₁ := (corner w).1 - (corner w').1 with hv₁
    set v₂ := (corner w).2 - (corner w').2 with hv₂
    have hv : d ^ 2 ≤ v₁ ^ 2 + v₂ ^ 2 := sq_le_corner_sub k hlt hk
    by_cases hδd : 2 * δ ≤ d
    · by_cases hex : ∃ θ₀ ∈ Icc 0 (π / 4), |v₁ * cos θ₀ + v₂ * sin θ₀| ≤ δ
      · obtain ⟨θ₀, hθ₀, hθ₀δ⟩ := hex
        have hbound := integral_overlap_le_of_support (w := w) (w' := w') (θ₀ := θ₀)
          (D := 5 * δ / d) (by positivity) hδ0 fun θ hθ => by
            by_cases hθδ : |v₁ * cos θ + v₂ * sin θ| ≤ δ
            · have hsep := abs_sub_le_of_abs_linForm_le hd hv hδd
                ⟨hθ₀.1, by linarith [hθ₀.2, pi_pos]⟩ ⟨hθ.1, by linarith [hθ.2, pi_pos]⟩
                hθ₀δ hθδ
              have hmem : θ ∈ Icc (θ₀ - 5 * δ / d) (θ₀ + 5 * δ / d) := by
                rw [abs_le] at hsep
                constructor <;> linarith [hsep.1, hsep.2]
              rw [indicator_of_mem hmem]
              exact overlap_le w w' θ
            · rw [overlap_eq_zero (by rw [proj_sub_proj]; exact lt_of_not_ge hθδ)]
              exact indicator_nonneg (fun _ _ => hδ0) θ
        refine hbound.trans (le_of_eq ?_)
        rw [hd_def, hδ_def]
        field_simp
        ring
      · push Not at hex
        have hzero : ∫ θ in (0)..(π / 4), overlap w w' θ = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ hθ => ?_]
          · simp
          · rw [uIcc_of_le (by positivity)] at hθ
            exact overlap_eq_zero (by rw [proj_sub_proj]; exact hex θ hθ)
        rw [hzero]
        positivity
    · -- the squares are close: `4^n < 8 · 4^k`
      push Not at hδd
      have hNa : N < 8 * a := by
        rw [hd_def, hδ_def] at hδd
        rw [div_lt_iff₀ (by positivity)] at hδd
        field_simp at hδd
        linarith
      refine htriv.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hN (by positivity)]
      nlinarith

/-- The number of ordered pairs of depth-`n` codes, weighted by agreement: `(n + 1) 16^n`. -/
theorem sum_agreeWeight (n : ℕ) :
    ∑ w : SqCode n, ∑ w' : SqCode n, agreeWeight w w' = (n + 1) * (4 ^ n * 4 ^ n) := by
  unfold agreeWeight
  have hinner : ∀ (w : SqCode n) (j : ℕ), j ≤ n → ∑ w' : SqCode n,
      (4 : ℝ) ^ j * (if ∀ i : Fin n, (i : ℕ) < j → w i = w' i then 1 else 0) = 4 ^ n := by
    intro w j hj
    rw [← Finset.mul_sum, Finset.sum_boole, card_agree_below hj w, Nat.cast_pow,
      Nat.cast_ofNat, ← pow_add, Nat.add_sub_cancel' hj]
  have hcard : (Finset.univ : Finset (SqCode n)).card = 4 ^ n := by
    simp [Finset.card_univ]
  calc ∑ w : SqCode n, ∑ w' : SqCode n, ∑ j ∈ Finset.range (n + 1),
        (4 : ℝ) ^ j * (if ∀ i : Fin n, (i : ℕ) < j → w i = w' i then 1 else 0)
      = ∑ w : SqCode n, ∑ j ∈ Finset.range (n + 1), ∑ w' : SqCode n,
        (4 : ℝ) ^ j * (if ∀ i : Fin n, (i : ℕ) < j → w i = w' i then 1 else 0) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ = ∑ w : SqCode n, ∑ _j ∈ Finset.range (n + 1), (4 : ℝ) ^ n :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j hj =>
          hinner w j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    _ = (n + 1) * (4 ^ n * 4 ^ n) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, hcard]
        simp only [nsmul_eq_mul]
        push_cast
        ring

/-- **Angular energy bound.** `∫_0^{π/4} ∑_{w,w'} overlap ≤ 80 (n + 1)`. -/
theorem integral_sum_overlap_le (n : ℕ) :
    ∫ θ in (0)..(π / 4), ∑ w : SqCode n, ∑ w' : SqCode n, overlap w w' θ ≤ 80 * (n + 1) := by
  have hN : (0 : ℝ) < 4 ^ n := by positivity
  rw [intervalIntegral.integral_finsetSum fun w _ =>
    (continuous_finsetSum _ fun w' _ => continuous_overlap w w').intervalIntegrable _ _]
  calc ∑ w : SqCode n, ∫ θ in (0)..(π / 4), ∑ w' : SqCode n, overlap w w' θ
      = ∑ w : SqCode n, ∑ w' : SqCode n, ∫ θ in (0)..(π / 4), overlap w w' θ :=
        Finset.sum_congr rfl fun w _ => intervalIntegral.integral_finsetSum fun w' _ =>
          (continuous_overlap w w').intervalIntegrable _ _
    _ ≤ ∑ w : SqCode n, ∑ w' : SqCode n, 80 / (4 ^ n * 4 ^ n) * agreeWeight w w' :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ => integral_overlap_le w w'
    _ = 80 / (4 ^ n * 4 ^ n) * ∑ w : SqCode n, ∑ w' : SqCode n, agreeWeight w w' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = 80 * (n + 1) := by
        rw [sum_agreeWeight]
        field_simp

end Favard.LowerBound
