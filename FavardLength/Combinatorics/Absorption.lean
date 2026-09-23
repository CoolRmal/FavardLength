import FavardLength.Combinatorics.Decomposition
import FavardLength.Combinatorics.Maximal
import FavardLength.Combinatorics.Statements

/-!
# Energy absorption (G10–G12)

Manuscript, "Energy absorption by Cauchy–Schwarz". Write `E = ∫ F_N²` and `S = ∑_{R ∈ 𝓡} 4^{-|R|}`.

* (G11) Integrating the pointwise decomposition `F_N² ≤ 8K ∑_R h_R²` on `{F_N ≥ 8K}` and using
  (G10) `∫ h_R² ≤ 4^{-|R|} E` gives `∫_{F_N ≥ 8K} F_N² ≤ 8K S E`.
* (G12) On `{F_N < 8K}` the discrete layer cake `n² = ∑_{k < n} (2k + 1)` and the distribution
  bound (G5) `μ_N(t) ≤ 9σ/t` give `∫_{F_N < 8K} F_N² ≤ 18 σ (8K + 1)`.
* With the packing inequality `S ≤ C K μ_N(K)` and `μ_N(K) ≤ c₀ K⁻²`, `c₀ = 1/(16C)`, the first
  term is at most `E/2`, and absorption gives `E ≤ 36 σ (8K + 1) ≤ 648 K`.

The result is `energyAbsorption_of_packing : PackingStatement → EnergyAbsorptionStatement`.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ}

/-- **(G11)**: `∫_{F_N ≥ 8K} F_N² ≤ 8K (∑_{R ∈ 𝓡} 4^{-|R|}) ∫ F_N²`. -/
theorem integral_indicator_superLevel_le (hθ : θ ∈ Icc 0 (π / 2)) {K : ℝ} (hK : 1 < 2 * K)
    (N : ℕ) :
    ∫ x, (superLevel N θ (8 * K)).indicator (fun x => (maxCount N θ x : ℝ) ^ 2) x ≤
      8 * K * (∑ R ∈ retained N θ K, 1 / 4 ^ R.length) * ∫ x, (maxCount N θ x : ℝ) ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hF := integrable_maxCount_pow hθ N two_ne_zero
  have hsum : Integrable fun x => 8 * K * ∑ R ∈ retained N θ K, (subtreeMax N θ R x : ℝ) ^ 2 :=
    (integrable_finsetSum _ fun R _ => integrable_subtreeMax_sq hθ N R).const_mul _
  calc ∫ x, (superLevel N θ (8 * K)).indicator (fun x => (maxCount N θ x : ℝ) ^ 2) x
      ≤ ∫ x, 8 * K * ∑ R ∈ retained N θ K, (subtreeMax N θ R x : ℝ) ^ 2 := by
        refine integral_mono (hF.indicator (measurableSet_superLevel hθ N _)) hsum fun x => ?_
        by_cases hx : x ∈ superLevel N θ (8 * K)
        · rw [Set.indicator_of_mem hx]
          exact maxCount_sq_le_sum_subtreeMax_sq hθ hK hx
        · rw [Set.indicator_of_notMem hx]
          exact mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = 8 * K * ∑ R ∈ retained N θ K, ∫ x, (subtreeMax N θ R x : ℝ) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun R _ => integrable_subtreeMax_sq hθ N R]
    _ ≤ 8 * K * ∑ R ∈ retained N θ K, 1 / 4 ^ R.length * ∫ x, (maxCount N θ x : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) (by linarith)
        exact integral_subtreeMax_sq_le hθ (length_le_of_mem_retained hR)
    _ = 8 * K * (∑ R ∈ retained N θ K, 1 / 4 ^ R.length) * ∫ x, (maxCount N θ x : ℝ) ^ 2 := by
        rw [← Finset.sum_mul]
        ring

/-- The discrete layer cake identity `n² = ∑_{k < M, k < n} (2k + 1)` for `n ≤ M`. -/
theorem sq_eq_sum_range_ite {n M : ℕ} (h : n ≤ M) :
    ((n : ℝ)) ^ 2 = ∑ k ∈ Finset.range M, if k + 1 ≤ n then (2 * k + 1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  have : (Finset.range M).filter (fun k => k + 1 ≤ n) = Finset.range n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this]
  clear this h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- **(G12)**: `∫_{F_N < 8K} F_N² ≤ 18 σ (8K + 1)`. -/
theorem integral_indicator_compl_superLevel_le (hθ : θ ∈ Icc 0 (π / 2)) {K : ℝ} (hK : 0 < K)
    (N : ℕ) :
    ∫ x, (superLevel N θ (8 * K))ᶜ.indicator (fun x => (maxCount N θ x : ℝ) ^ 2) x ≤
      18 * sig θ * (8 * K + 1) := by
  set M := ⌈8 * K⌉₊ with hM
  have hσ := sig_pos hθ
  have hF := integrable_maxCount_pow hθ N two_ne_zero
  have hind : ∀ k : ℕ, Integrable fun x => (superLevel N θ (k + 1)).indicator (1 : ℝ → ℝ) x :=
    fun k => (integrable_indicator_iff (measurableSet_superLevel hθ N _)).mpr
      (integrableOn_const (ne_of_lt (lt_of_le_of_lt
        (volume_superLevel_le_sig hθ N (by positivity)) ENNReal.ofReal_lt_top)))
  calc ∫ x, (superLevel N θ (8 * K))ᶜ.indicator (fun x => (maxCount N θ x : ℝ) ^ 2) x
      ≤ ∫ x, ∑ k ∈ Finset.range M,
          (2 * k + 1 : ℝ) * (superLevel N θ (k + 1)).indicator 1 x := by
        refine integral_mono (hF.indicator (measurableSet_superLevel hθ N _).compl)
          (integrable_finsetSum _ fun k _ => (hind k).const_mul _) fun x => ?_
        by_cases hx : x ∈ (superLevel N θ (8 * K))ᶜ
        · rw [Set.indicator_of_mem hx]
          have hxlt : (maxCount N θ x : ℝ) < 8 * K := by
            simpa [mem_superLevel] using hx
          have hle : maxCount N θ x ≤ M := by
            have : (maxCount N θ x : ℝ) < M := hxlt.trans_le (Nat.le_ceil _)
            exact_mod_cast this.le
          dsimp only
          rw [sq_eq_sum_range_ite hle]
          refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
          by_cases hk : k + 1 ≤ maxCount N θ x
          · rw [ite_eq_left hk, Set.indicator_of_mem, Pi.one_apply, mul_one]
            rw [mem_superLevel]
            exact_mod_cast hk
          · rw [ite_eq_right hk, Set.indicator_of_notMem, mul_zero]
            rw [mem_superLevel]
            push Not at hk
            exact not_le.mpr (by exact_mod_cast hk)
        · rw [Set.indicator_of_notMem hx]
          exact Finset.sum_nonneg fun k _ =>
            mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    _ = ∑ k ∈ Finset.range M, (2 * k + 1 : ℝ) * volume.real (superLevel N θ (k + 1)) := by
        rw [integral_finsetSum _ fun k _ => (hind k).const_mul _]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_indicator_one (measurableSet_superLevel hθ N _)]
    _ ≤ ∑ k ∈ Finset.range M, 18 * sig θ := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk : (0 : ℝ) < k + 1 := by positivity
        have hμ : volume.real (superLevel N θ (k + 1)) ≤ 9 * sig θ / (k + 1) :=
          ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_superLevel_le_div hθ N hk)
        calc (2 * k + 1 : ℝ) * volume.real (superLevel N θ (k + 1))
            ≤ (2 * k + 1 : ℝ) * (9 * sig θ / (k + 1)) :=
              mul_le_mul_of_nonneg_left hμ (by positivity)
          _ ≤ 18 * sig θ := by
              rw [mul_div_assoc', div_le_iff₀ hk]
              nlinarith
    _ = M * (18 * sig θ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (8 * K + 1) * (18 * sig θ) := by
        refine mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le (by positivity)
    _ = 18 * sig θ * (8 * K + 1) := by ring

/-- **Energy absorption from packing** (G10–G12): the packing inequality implies the first
alternative of the dichotomy. -/
theorem energyAbsorption_of_packing (hP : PackingStatement) : EnergyAbsorptionStatement := by
  obtain ⟨C, hC, hpack⟩ := hP
  refine ⟨1 / (16 * C), 648, by positivity, by norm_num, fun θ hθ K hK N hμ => ?_⟩
  have hK0 : 0 < K := by linarith
  have hσ := sig_pos hθ
  have hσ2 := sig_le_two θ
  set E := ∫ x, (maxCount N θ x : ℝ) ^ 2 with hE
  set S := ∑ R ∈ retained N θ K, (1 / 4 ^ R.length : ℝ) with hS
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun R _ => by positivity
  -- the packing inequality with the small distribution function
  have hSK : 8 * K * S ≤ 1 / 2 := by
    have h1 := hpack θ hθ K hK N
    have h2 : ENNReal.ofReal S ≤ ENNReal.ofReal (C * K * (1 / (16 * C) / K ^ 2)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact h1.trans (by gcongr)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    have : C * K * (1 / (16 * C) / K ^ 2) = 1 / (16 * K) := by
      field_simp
    rw [this] at h2
    calc 8 * K * S ≤ 8 * K * (1 / (16 * K)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / 2 := by field_simp; ring
  -- split the energy at height `8K`
  have hF := integrable_maxCount_pow hθ N two_ne_zero
  have hsplit : E = (∫ x, (superLevel N θ (8 * K)).indicator
      (fun x => (maxCount N θ x : ℝ) ^ 2) x) +
      ∫ x, (superLevel N θ (8 * K))ᶜ.indicator (fun x => (maxCount N θ x : ℝ) ^ 2) x := by
    rw [hE, ← integral_add (hF.indicator (measurableSet_superLevel hθ N _))
      (hF.indicator (measurableSet_superLevel hθ N _).compl)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (Set.indicator_self_add_compl_apply (superLevel N θ (8 * K))
      (fun x => (maxCount N θ x : ℝ) ^ 2) x).symm
  have h11 := integral_indicator_superLevel_le hθ (by linarith : 1 < 2 * K) N
  have h12 := integral_indicator_compl_superLevel_le hθ hK0 N
  rw [← hE, ← hS] at h11
  have hmain : E ≤ 8 * K * S * E + 18 * sig θ * (8 * K + 1) := by
    linarith [add_le_add h11 h12]
  have : 8 * K * S * E ≤ 1 / 2 * E := mul_le_mul_of_nonneg_right hSK hE0
  nlinarith

end Favard.Comb
