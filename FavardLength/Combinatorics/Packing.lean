import FavardLength.Combinatorics.Packing.Local
import FavardLength.Combinatorics.Packing.Superlevel
import FavardLength.Combinatorics.Statements

/-!
# The packing inequality (G7)

Manuscript, section "The packing construction", (G6)–(G9). Every retained word meets its own
maximal cell (`inter_topCell_nonempty`), so grouping the retained words by their cells and using
the local bound (G8) (`sum_retainedMeeting_topCell_le`) gives
`∑_{R ∈ 𝓡} 4^{-|R|} ≤ 16 K ∑_{D ∈ 𝒟} |D|`, and (G9) (`sum_maxCells_le`) bounds the last sum by
`42 μ_N(K)`. This proves `PackingStatement` with `C = 16 · 42 = 672`.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ} {N : ℕ} {K : ℝ}

/-- Grouping the retained words by their maximal cells: `∑_{R ∈ 𝓡} 4^{-|R|} ≤ 16 K ∑_{D ∈ 𝒟} |D|`,
by (G8). -/
theorem sum_retained_le (hθ : θ ∈ Icc 0 (π / 2)) (hK : 1 < 2 * K) :
    ∑ R ∈ retained N θ K, (1 / 4 ^ R.length : ℝ) ≤
      16 * K * ∑ D ∈ maxCells N θ K, (1 / 4 ^ D.1 : ℝ) := by
  classical
  calc ∑ R ∈ retained N θ K, (1 / 4 ^ R.length : ℝ)
      = ∑ D ∈ maxCells N θ K,
          ∑ R ∈ retained N θ K with topCell N θ K R = D, (1 / 4 ^ R.length : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun R hR => Finset.mem_image_of_mem _ hR) _).symm
    _ ≤ ∑ D ∈ maxCells N θ K, ∑ R ∈ retainedMeeting N θ K D.1 D.2, (1 / 4 ^ R.length : ℝ) := by
        refine Finset.sum_le_sum fun D _ =>
          Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro R hR
        obtain ⟨hR', rfl⟩ := Finset.mem_filter.mp hR
        exact mem_retainedMeeting.mpr ⟨hR', inter_topCell_nonempty hθ hR'⟩
    _ ≤ ∑ D ∈ maxCells N θ K, 16 * K / 4 ^ D.1 := by
        refine Finset.sum_le_sum fun D hD => ?_
        obtain ⟨R₁, hR₁, rfl⟩ := Finset.mem_image.mp hD
        exact sum_retainedMeeting_topCell_le hθ hK hR₁
    _ = 16 * K * ∑ D ∈ maxCells N θ K, (1 / 4 ^ D.1 : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun D _ => by ring

/-- **Packing inequality (G7)**: `∑_{R ∈ 𝓡} 4^{-|R|} ≤ 672 K μ_N(K)` for every `θ ∈ [0, π/2]`,
`K ≥ 2` and `N`. -/
theorem packing : PackingStatement := by
  refine ⟨672, by norm_num, fun θ hθ K hK N => ?_⟩
  have hK1 : 1 < 2 * K := by linarith
  have hK0 : 0 < K := by linarith
  calc ENNReal.ofReal (∑ R ∈ retained N θ K, 1 / 4 ^ R.length)
      ≤ ENNReal.ofReal (16 * K * ∑ D ∈ maxCells N θ K, (1 / 4 ^ D.1 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (sum_retained_le hθ hK1)
    _ = ENNReal.ofReal (16 * K) * ENNReal.ofReal (∑ D ∈ maxCells N θ K, (1 / 4 ^ D.1 : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (16 * K) * (42 * volume (superLevel N θ K)) := by
        gcongr
        exact sum_maxCells_le hθ
    _ = ENNReal.ofReal (672 * K) * volume (superLevel N θ K) := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 42, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end Favard.Comb
