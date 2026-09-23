import FavardLength.Combinatorics.Covering
import FavardLength.Combinatorics.Maximal
import FavardLength.Combinatorics.Packing.Cells

/-!
# The maximal cells are controlled by the superlevel set (G9)

Manuscript, proof of (G7), bound (G9), in a form avoiding connected components. Let
`D = gridIcc k j` be a maximal cell. Some retained word `R₀` of length `k` meets `D`; since `R₀`
is marked, its projection contains a point `x₀` with `f_k(x₀) ≥ 2K`, and the half-interval lemma
(`exists_Icc_subset_superLevel`) gives an interval `T_D` of length `σ 4^{-k}/2 ≥ 4^{-k}/2` with
endpoint `x₀` inside `{F_N ≥ K}`. Both `D` and `T_D` lie in the enlargement
`D' = [(j - 3) 4^{-k}, (j + 4) 4^{-k}]` of length `7 · 4^{-k}` (`gridEnl`).

The finite Vitali lemma applied to the enlargements selects a disjoint subfamily `𝒮` with
`|⋃ D'| ≤ 3 ∑_{𝒮} 7 · 4^{-k}`; the intervals `T_D`, `D ∈ 𝒮`, are then disjoint subsets of the
superlevel set, so `∑_{𝒮} 4^{-k} ≤ 2 μ_N(K)`. Since the cells are a.e. disjoint,
`∑_{𝒟} 4^{-k} = |⋃ D| ≤ |⋃ D'| ≤ 42 μ_N(K)` (`sum_maxCells_le`).
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard.Comb

variable {θ : ℝ} {N : ℕ} {K : ℝ}

/-- The enlargement `[(j - 3) 4^{-k}, (j + 4) 4^{-k}]` of the grid interval `gridIcc k j`. -/
noncomputable def gridEnl (k : ℕ) (j : ℤ) : Set ℝ :=
  Icc (((j : ℝ) - 3) / 4 ^ k) (((j : ℝ) + 4) / 4 ^ k)

theorem gridIcc_subset_gridEnl (k : ℕ) (j : ℤ) : gridIcc k j ⊆ gridEnl k j :=
  Icc_subset_Icc (div_le_div_of_nonneg_right (by linarith) (by positivity))
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

theorem volume_gridEnl (k : ℕ) (j : ℤ) :
    volume (gridEnl k j) = 7 * ENNReal.ofReal (1 / 4 ^ k) := by
  rw [gridEnl, Real.volume_Icc,
    show ((j : ℝ) + 4) / 4 ^ k - ((j : ℝ) - 3) / 4 ^ k = 7 * (1 / 4 ^ k) by ring,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **Half-interval in a cell's enlargement.** For every maximal cell there is an interval of
length `σ 4^{-k}/2` contained both in the enlargement of the cell and in `{F_N ≥ K}`. -/
theorem exists_Icc_subset_gridEnl_inter (hθ : θ ∈ Icc 0 (π / 2)) {R₁ : Word}
    (hR₁ : R₁ ∈ retained N θ K) :
    ∃ c : ℝ, Icc c (c + sig θ / 4 ^ (topCell N θ K R₁).1 / 2) ⊆
      gridEnl (topCell N θ K R₁).1 (topCell N θ K R₁).2 ∩ superLevel N θ K := by
  obtain ⟨R₀, hR₀, hl, y, hyR, hyD⟩ := exists_retained_length_eq_topLevel hθ hR₁
  obtain ⟨x₀, hx₀, hcross⟩ := mem_marked.mp (retained_subset_marked N θ K hR₀)
  rw [hl] at hcross
  obtain ⟨c, hc, hsub⟩ := exists_Icc_subset_superLevel hθ hcross.1 hcross.2.1
  refine ⟨c, subset_inter ?_ hsub⟩
  rw [topCell_fst] at hyD ⊢
  set k := topLevel N θ K R₁
  set j := (topCell N θ K R₁).2
  rw [wordIval, hl] at hyR hx₀
  obtain ⟨hy1, hy2⟩ := hyR
  obtain ⟨hx1, hx2⟩ := hx₀
  obtain ⟨hD1, hD2⟩ := hyD
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have e1 : ((j : ℝ) - 3) / 4 ^ k = j / 4 ^ k - 3 * (1 / 4 ^ k) := by ring
  have e2 : ((j : ℝ) + 4) / 4 ^ k = j / 4 ^ k + 4 * (1 / 4 ^ k) := by ring
  have e3 : ((j : ℝ) + 1) / 4 ^ k = j / 4 ^ k + 1 / 4 ^ k := by ring
  have hs2 : sig θ / 4 ^ k ≤ 2 * (1 / 4 ^ k) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (sig_le_two θ) h4.le
  have hs0 : 0 ≤ sig θ / 4 ^ k := div_nonneg (sig_nonneg hθ) h4.le
  rw [e3] at hD2
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [gridEnl, e1, e2]
  rcases hc with hc | hc
  · subst hc
    constructor <;> linarith
  · constructor <;> linarith

/-- **(G9)**: the lengths of the maximal cells sum to at most `42 μ_N(K)`. -/
theorem sum_maxCells_le (hθ : θ ∈ Icc 0 (π / 2)) :
    ENNReal.ofReal (∑ D ∈ maxCells N θ K, (1 / 4 ^ D.1 : ℝ)) ≤
      42 * volume (superLevel N θ K) := by
  classical
  set 𝒟 := maxCells N θ K with h𝒟
  have hex : ∀ D : ℕ × ℤ, ∃ c : ℝ, D ∈ 𝒟 →
      Icc c (c + sig θ / 4 ^ D.1 / 2) ⊆ gridEnl D.1 D.2 ∩ superLevel N θ K := by
    intro D
    by_cases hD : D ∈ 𝒟
    · obtain ⟨R₁, hR₁, rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨c, hc⟩ := exists_Icc_subset_gridEnl_inter hθ hR₁
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hD⟩
  choose c hc using hex
  -- the finite Vitali lemma for the enlargements
  obtain ⟨t, ht𝒟, htd, hvol⟩ := exists_disjoint_subfamily_volume_le 𝒟
    (fun D => ((D.2 : ℝ) - 3) / 4 ^ D.1) (fun D => ((D.2 : ℝ) + 4) / 4 ^ D.1)
  -- the half-intervals of the selected cells are disjoint subsets of the superlevel set
  have hTd : (t : Set (ℕ × ℤ)).PairwiseDisjoint
      (fun D => Icc (c D) (c D + sig θ / 4 ^ D.1 / 2)) :=
    htd.mono_on fun D hD => (hc D (ht𝒟 hD)).trans inter_subset_left
  have hT : ∑ D ∈ t, ENNReal.ofReal (1 / 4 ^ D.1) ≤ 2 * volume (superLevel N θ K) := by
    calc ∑ D ∈ t, ENNReal.ofReal (1 / 4 ^ D.1)
        ≤ ∑ D ∈ t, 2 * volume (Icc (c D) (c D + sig θ / 4 ^ D.1 / 2)) := by
          refine Finset.sum_le_sum fun D _ => ?_
          rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := div_le_div_of_nonneg_right (one_le_sig hθ) (by positivity : (0 : ℝ) ≤ 4 ^ D.1)
          linarith
      _ = 2 * volume (⋃ D ∈ t, Icc (c D) (c D + sig θ / 4 ^ D.1 / 2)) := by
          rw [measure_biUnion_finset hTd fun _ _ => measurableSet_Icc, Finset.mul_sum]
      _ ≤ 2 * volume (superLevel N θ K) := by
          gcongr
          exact iUnion₂_subset fun D hD => (hc D (ht𝒟 hD)).trans inter_subset_right
  -- the cells are a.e. disjoint
  have hunion : ∑ D ∈ 𝒟, ENNReal.ofReal (1 / 4 ^ D.1) = volume (⋃ D ∈ 𝒟, gridIcc D.1 D.2) := by
    rw [measure_biUnion_finset₀ ?_ fun D _ => (measurableSet_gridIcc _ _).nullMeasurableSet]
    · exact Finset.sum_congr rfl fun D _ => (volume_gridIcc _ _).symm
    · intro D₁ h₁ D₂ h₂ hne
      exact volume_inter_eq_zero_of_mem_maxCells hθ h₁ h₂ hne
  calc ENNReal.ofReal (∑ D ∈ 𝒟, (1 / 4 ^ D.1 : ℝ))
      = ∑ D ∈ 𝒟, ENNReal.ofReal (1 / 4 ^ D.1) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
    _ = volume (⋃ D ∈ 𝒟, gridIcc D.1 D.2) := hunion
    _ ≤ volume (⋃ D ∈ 𝒟, gridEnl D.1 D.2) :=
        measure_mono (iUnion₂_mono fun D _ => gridIcc_subset_gridEnl _ _)
    _ ≤ 3 * ∑ D ∈ t, volume (gridEnl D.1 D.2) := hvol
    _ = 21 * ∑ D ∈ t, ENNReal.ofReal (1 / 4 ^ D.1) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [volume_gridEnl, ← mul_assoc]
        norm_num
    _ ≤ 21 * (2 * volume (superLevel N θ K)) := by gcongr
    _ = 42 * volume (superLevel N θ K) := by
        rw [← mul_assoc]
        norm_num

end Favard.Comb
