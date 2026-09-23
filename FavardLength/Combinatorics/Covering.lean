import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The finite Vitali covering lemma for closed intervals

The greedy selection of the manuscript (proof of (G2), and (G13)–(G14)): from a finite family of
closed intervals, repeatedly retain a longest remaining interval and discard every interval
meeting it. The retained intervals are pairwise disjoint and every interval of the family lies in
the concentric triple `[a - (b - a), b + (b - a)]` of a retained interval `[a, b]`. Consequences:

* `exists_disjoint_subfamily_volume_le`: the union has measure at most three times the total
  length of the retained intervals;
* `mul_volume_biUnion_le_lintegral`: a finite weak-type (1,1) inequality. If each interval `I`
  of the family satisfies `c |I| ≤ ∫⁻_I g`, then `c |⋃ I| ≤ 3 ∫⁻ g`.
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace Favard.Comb

/-- The concentric triple `[a - (b - a), b + (b - a)]` of `[a, b]`. -/
def tripleIcc (a b : ℝ) : Set ℝ := Icc (a - (b - a)) (b + (b - a))

theorem Icc_subset_tripleIcc_self (a b : ℝ) : Icc a b ⊆ tripleIcc a b := by
  intro x hx
  have : a ≤ b := hx.1.trans hx.2
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- An interval meeting a longer interval lies in the concentric triple of the longer one. -/
theorem Icc_subset_tripleIcc {a b c d : ℝ} (hmeet : ¬Disjoint (Icc a b) (Icc c d))
    (hlen : b - a ≤ d - c) : Icc a b ⊆ tripleIcc c d := by
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨y, hy1, hy2⟩ := hmeet
  intro x hx
  exact ⟨by linarith [hx.1, hy1.2, hy2.1], by linarith [hx.2, hy1.1, hy2.2]⟩

theorem volume_tripleIcc (a b : ℝ) : volume (tripleIcc a b) = 3 * ENNReal.ofReal (b - a) := by
  rw [tripleIcc, Real.volume_Icc, show b + (b - a) - (a - (b - a)) = 3 * (b - a) by ring,
    ENNReal.ofReal_mul (by norm_num)]
  simp

/-- **Finite Vitali covering lemma.** Every finite family of closed intervals has a pairwise
disjoint subfamily such that every interval of the family lies in the concentric triple of a
selected interval. -/
theorem exists_disjoint_subfamily_Icc {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∃ t ⊆ s, (t : Set ι).PairwiseDisjoint (fun i => Icc (a i) (b i)) ∧
      ∀ i ∈ s, ∃ j ∈ t, Icc (a i) (b i) ⊆ tripleIcc (a j) (b j) := by
  classical
  induction h : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s (fun i => b i - a i) hs
    set s' := s.filter fun i => Disjoint (Icc (a i) (b i)) (Icc (a i₀) (b i₀)) ∧ i ≠ i₀
    have hlt : #s' < n := by
      rw [← h]
      refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
      have := Finset.mem_filter.mp (hsub hi₀)
      exact this.2.2 rfl
    obtain ⟨t', ht's, ht'd, ht'c⟩ := ih _ hlt s' rfl
    refine ⟨insert i₀ t', ?_, ?_, ?_⟩
    · exact Finset.insert_subset hi₀ (ht's.trans (Finset.filter_subset _ _))
    · rw [Finset.coe_insert]
      refine ht'd.insert fun j hj _ => ?_
      exact ((Finset.mem_filter.mp (ht's hj)).2.1).symm
    · intro i hi
      by_cases hi' : i ∈ s'
      · obtain ⟨j, hj, hij⟩ := ht'c i hi'
        exact ⟨j, Finset.mem_insert_of_mem hj, hij⟩
      · refine ⟨i₀, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.mem_filter, not_and, not_and_or, not_not] at hi'
        by_cases hdisj : Disjoint (Icc (a i) (b i)) (Icc (a i₀) (b i₀))
        · rcases hi' hi with h' | h'
          · exact absurd hdisj h'
          · rw [h']
            exact Icc_subset_tripleIcc_self _ _
        · exact Icc_subset_tripleIcc hdisj (hmax i hi)

/-- **Finite Vitali lemma, measure form**: a pairwise disjoint subfamily whose total length is
at least a third of the measure of the union. -/
theorem exists_disjoint_subfamily_volume_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∃ t ⊆ s, (t : Set ι).PairwiseDisjoint (fun i => Icc (a i) (b i)) ∧
      volume (⋃ i ∈ s, Icc (a i) (b i)) ≤ 3 * ∑ i ∈ t, volume (Icc (a i) (b i)) := by
  obtain ⟨t, hts, htd, htc⟩ := exists_disjoint_subfamily_Icc s a b
  refine ⟨t, hts, htd, ?_⟩
  calc volume (⋃ i ∈ s, Icc (a i) (b i)) ≤ volume (⋃ j ∈ t, tripleIcc (a j) (b j)) := by
        refine measure_mono (Set.iUnion₂_subset fun i hi => ?_)
        obtain ⟨j, hj, hij⟩ := htc i hi
        exact hij.trans (Set.subset_biUnion_of_mem (u := fun j => tripleIcc (a j) (b j)) hj)
    _ ≤ ∑ j ∈ t, volume (tripleIcc (a j) (b j)) := measure_biUnion_finset_le _ _
    _ = 3 * ∑ i ∈ t, volume (Icc (a i) (b i)) := by
        rw [Finset.mul_sum]
        simp only [volume_tripleIcc, Real.volume_Icc]

/-- **Finite weak-type (1,1) inequality (G2).** If every interval `I` of a finite family satisfies
`c |I| ≤ ∫⁻_I g`, then `c |⋃ I| ≤ 3 ∫⁻ g`. -/
theorem mul_volume_biUnion_le_lintegral {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (g : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ i ∈ s, c * volume (Icc (a i) (b i)) ≤ ∫⁻ x in Icc (a i) (b i), g x) :
    c * volume (⋃ i ∈ s, Icc (a i) (b i)) ≤ 3 * ∫⁻ x, g x := by
  obtain ⟨t, hts, htd, hvol⟩ := exists_disjoint_subfamily_volume_le s a b
  calc c * volume (⋃ i ∈ s, Icc (a i) (b i))
      ≤ c * (3 * ∑ i ∈ t, volume (Icc (a i) (b i))) := by gcongr
    _ = 3 * ∑ i ∈ t, c * volume (Icc (a i) (b i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 3 * ∑ i ∈ t, ∫⁻ x in Icc (a i) (b i), g x := by
        gcongr with i hi
        exact h i (hts hi)
    _ = 3 * ∫⁻ x in ⋃ i ∈ t, Icc (a i) (b i), g x := by
        rw [lintegral_biUnion_finset htd (fun _ _ => measurableSet_Icc)]
    _ ≤ 3 * ∫⁻ x, g x := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end Favard.Comb
