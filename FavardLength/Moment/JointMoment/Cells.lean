import FavardLength.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cell decomposition of the `(u, v)` square

Let `L = 4^m` and `h = π / L`. The cells `I_i = [i h, (i+1) h]`, `i < L`, cover `[0, π]`. This
file proves:
* every point of `[0, π]` lies in some cell (`exists_mem_cell`);
* the weight estimate (J7): on `(I_i × I_j) ∩ {u ≥ 3/(8L), v ≥ 0}`,
  `1/(u+v) ≤ 12 L / (π (i + j + 1))` (`one_div_add_le`);
* the integral of a function over a subset `Ω` of `[0, π]²` is bounded by the sum over pairs of
  cells of the integrals of cellwise majorants (`setLIntegral_le_sum_cells`);
* the product structure on a product of cells (`setLIntegral_cell_prod_mul`).
-/

open MeasureTheory Set Real Finset

open scoped ENNReal

namespace Favard

namespace JointMoment

/-- The cell `I_i = [iπ/4^m, (i+1)π/4^m]`. -/
def cell (m i : ℕ) : Set ℝ :=
  Icc ((i : ℝ) * π / 4 ^ m) (((i : ℝ) + 1) * π / 4 ^ m)

lemma measurableSet_cell (m i : ℕ) : MeasurableSet (cell m i) :=
  measurableSet_Icc

/-- The cells `I_i`, `i < 4^m`, cover `[0, π]`. -/
lemma exists_mem_cell (m : ℕ) {x : ℝ} (hx : x ∈ Icc 0 π) : ∃ i < 4 ^ m, x ∈ cell m i := by
  have hL : (0 : ℝ) < 4 ^ m := by positivity
  have hL1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  set k := ⌊x * 4 ^ m / π⌋₊ with hk
  have hxk : 0 ≤ x * 4 ^ m / π := by have := hx.1; positivity
  by_cases hkL : k < 4 ^ m
  · refine ⟨k, hkL, ?_, ?_⟩
    · rw [div_le_iff₀ hL]
      exact (le_div_iff₀ pi_pos).1 (Nat.floor_le hxk)
    · rw [le_div_iff₀ hL]
      exact ((div_lt_iff₀ pi_pos).1 (Nat.lt_floor_add_one _)).le
  · refine ⟨4 ^ m - 1, by omega, ?_, ?_⟩
    · have hπx : π ≤ x := by
        have h1 : ((4 ^ m : ℕ) : ℝ) ≤ k := by exact_mod_cast not_lt.1 hkL
        have h2 : (k : ℝ) ≤ x * 4 ^ m / π := Nat.floor_le hxk
        push_cast at h1
        rw [le_div_iff₀ pi_pos] at h2
        nlinarith [mul_le_mul_of_nonneg_right h1 pi_pos.le]
      rw [Nat.cast_sub hL1]
      push_cast
      rw [div_le_iff₀ hL]
      nlinarith [pi_pos]
    · rw [Nat.cast_sub hL1]
      push_cast
      rw [le_div_iff₀ hL]
      simp only [sub_add_cancel]
      nlinarith [hx.2]

/-- The weight estimate (J7): on `(I_i × I_j) ∩ {u ≥ 3/(8L), v ≥ 0}`,
`1/(u+v) ≤ 12 L / (π (i+j+1))`. -/
lemma one_div_add_le {m i j : ℕ} {u v : ℝ} (hu : u ∈ cell m i) (hv : v ∈ cell m j)
    (hu₀ : 3 / 8 / 4 ^ m ≤ u) (hv₀ : 0 ≤ v) :
    1 / (u + v) ≤ 12 * 4 ^ m / (π * ((i : ℝ) + j + 1)) := by
  have hL : (0 : ℝ) < 4 ^ m := by positivity
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu₀
  have hi : (i : ℝ) * π ≤ u * 4 ^ m := (div_le_iff₀ hL).1 hu.1
  have hj : (j : ℝ) * π ≤ v * 4 ^ m := (div_le_iff₀ hL).1 hv.1
  have h0 : 3 / 8 ≤ u * 4 ^ m := (div_le_iff₀ hL).1 hu₀
  have hπ : π ≤ 4 := pi_le_four
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Integrals over a subset of `[0, π]²` are bounded by sums over pairs of cells of the integrals
of cellwise majorants. -/
lemma setLIntegral_le_sum_cells (m : ℕ) {Ω : Set (ℝ × ℝ)} (hΩ : Ω ⊆ Icc 0 π ×ˢ Icc 0 π)
    (g : ℝ × ℝ → ℝ≥0∞) (G : ℕ → ℕ → ℝ × ℝ → ℝ≥0∞) (hG : ∀ i j, Measurable (G i j))
    (hgG : ∀ i < 4 ^ m, ∀ j < 4 ^ m, ∀ p ∈ Ω, p ∈ cell m i ×ˢ cell m j → g p ≤ G i j p) :
    ∫⁻ p in Ω, g p ≤
      ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), ∫⁻ p in cell m i ×ˢ cell m j, G i j p := by
  have hmeas : ∀ i j, MeasurableSet (cell m i ×ˢ cell m j) := fun i j =>
    (measurableSet_cell m i).prod (measurableSet_cell m j)
  calc ∫⁻ p in Ω, g p
      ≤ ∫⁻ p in Ω, ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m),
          (cell m i ×ˢ cell m j).indicator (G i j) p := by
        refine setLIntegral_mono (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
          fun j _ => (hG i j).indicator (hmeas i j)) fun p hp => ?_
        obtain ⟨i, hi, hpi⟩ := exists_mem_cell m (hΩ hp).1
        obtain ⟨j, hj, hpj⟩ := exists_mem_cell m (hΩ hp).2
        have hpij : p ∈ cell m i ×ˢ cell m j := ⟨hpi, hpj⟩
        calc g p ≤ (cell m i ×ˢ cell m j).indicator (G i j) p := by
              rw [indicator_of_mem hpij]
              exact hgG i hi j hj p hp hpij
          _ ≤ ∑ j ∈ range (4 ^ m), (cell m i ×ˢ cell m j).indicator (G i j) p :=
              single_le_sum (f := fun j => (cell m i ×ˢ cell m j).indicator (G i j) p)
                (fun _ _ => zero_le) (mem_range.2 hj)
          _ ≤ _ := single_le_sum (f := fun i => ∑ j ∈ range (4 ^ m),
                (cell m i ×ˢ cell m j).indicator (G i j) p) (fun _ _ => zero_le)
                (mem_range.2 hi)
    _ ≤ ∫⁻ p, ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m),
          (cell m i ×ˢ cell m j).indicator (G i j) p := setLIntegral_le_lintegral _ _
    _ = ∑ i ∈ range (4 ^ m), ∑ j ∈ range (4 ^ m), ∫⁻ p in cell m i ×ˢ cell m j, G i j p := by
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ =>
          (hG i j).indicator (hmeas i j)]
        refine sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun j _ => (hG i j).indicator (hmeas i j)]
        exact sum_congr rfl fun j _ => lintegral_indicator (hmeas i j) _

/-- On a product of cells, the integral of `c φ(u) φ(v)` factors. -/
lemma setLIntegral_cell_prod_mul (m i j : ℕ) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (c : ℝ≥0∞) :
    ∫⁻ p in cell m i ×ˢ cell m j, c * (φ p.1 * φ p.2) =
      c * ((∫⁻ u in cell m i, φ u) * ∫⁻ v in cell m j, φ v) := by
  rw [lintegral_const_mul _ (by fun_prop : Measurable fun p : ℝ × ℝ => φ p.1 * φ p.2),
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hφ.aemeasurable hφ.aemeasurable]

end JointMoment

end Favard
