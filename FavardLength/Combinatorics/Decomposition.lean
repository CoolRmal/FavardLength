import FavardLength.Combinatorics.Marking
import FavardLength.Combinatorics.Subtree
import Mathlib.Algebra.Order.Chebyshev

/-!
# The retained-subtree decomposition of high multiplicities (pointwise G11)

Manuscript, "Energy absorption by Cauchy–Schwarz". Fix a point `x` with `F_N(x) ≥ 8K` and a
generation `n` attaining the maximum. Its first crossing `m` is strictly earlier (G6). Every
depth-`n` square counted at `x` lies below a unique retained square, and the retained squares
that occur lie below the fewer than `8K` depth-`m` squares counted at `x`. Grouping the counted
squares by retained ancestor and applying Cauchy–Schwarz gives

`F_N(x)² ≤ 8K ∑_{R ∈ 𝓡} h_R(x)²` (`maxCount_sq_le_sum_subtreeMax_sq`).
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ}

/-- **Pointwise decomposition (G11)**: where `F_N(x) ≥ 8K`,
`F_N(x)² ≤ 8K ∑_{R ∈ 𝓡} h_R(x)²`. -/
theorem maxCount_sq_le_sum_subtreeMax_sq (hθ : θ ∈ Icc 0 (π / 2)) {K : ℝ} (hK : 1 < 2 * K)
    {N : ℕ} {x : ℝ} (hx : 8 * K ≤ (maxCount N θ x : ℝ)) :
    (maxCount N θ x : ℝ) ^ 2 ≤ 8 * K * ∑ R ∈ retained N θ K, (subtreeMax N θ R x : ℝ) ^ 2 := by
  classical
  have hK0 : 0 < K := by linarith
  -- a generation attaining the maximum, and the first crossing
  obtain ⟨n, hnN, hn⟩ := exists_count_eq_maxCount N θ x
  have hx2 : x ∈ superLevel N θ (2 * K) := by
    rw [mem_superLevel]
    linarith
  obtain ⟨m, hm⟩ := exists_firstCross hx2
  have hcn : 8 * K ≤ (count n θ x : ℝ) := by rw [hn]; exact hx
  have hmn : m < n := hm.lt_of_le_count hθ hK hcn
  -- the counted squares at generation `n`
  set Q := (words n).filter fun q => x ∈ wordIval θ q with hQ
  have hQcard : #Q = count n θ x := by
    rw [count_eq_wcount hθ]
    rfl
  -- every counted square has a retained prefix of length at most `m`
  have hpre : ∀ q ∈ Q, ∃ R ∈ retained N θ K, R <+: q ∧ R.length ≤ m := by
    intro q hq
    obtain ⟨hqw, hxq⟩ := Finset.mem_filter.mp hq
    exact exists_retained_prefix_of_firstCross hθ hm
      ((mem_words.mp hqw).symm ▸ hmn.le) hxq
  -- the grouping
  set a : Word → ℕ := fun R => #(Q.filter fun q => R <+: q) with ha
  have ha_eq : ∀ R, a R = wcount θ (desc R n) x := by
    intro R
    simp only [ha, hQ, wcount, desc, Finset.filter_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter]
    tauto
  have hsum : #Q = ∑ R ∈ retained N θ K, a R := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hq
        obtain ⟨R, hR, hRq, -⟩ := hpre q hq
        exact ⟨R, hR, hq, hRq⟩
      · rintro ⟨R, -, hq, -⟩
        exact hq
    · intro R hR R' hR' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hq hq'
      exact hne (retained_prefix_unique hR hR' (Finset.mem_filter.mp hq).2
        (Finset.mem_filter.mp hq').2)
  -- the retained squares that occur
  set supp := (retained N θ K).filter fun R => a R ≠ 0 with hsupp
  have hsupp_card : (#supp : ℝ) ≤ 8 * K := by
    set Qm := (words m).filter fun u => x ∈ wordIval θ u
    have hQm : (#Qm : ℝ) < 8 * K := by
      have : #Qm = count m θ x := by
        rw [count_eq_wcount hθ]
        rfl
      rw [this]
      exact hm.count_lt hθ hK
    have hf : ∀ R ∈ supp, ∃ u ∈ Qm, R <+: u := by
      intro R hR
      obtain ⟨hRr, haR⟩ := Finset.mem_filter.mp hR
      obtain ⟨q, hq⟩ := Finset.card_ne_zero.mp haR
      obtain ⟨hqQ, hRq⟩ := Finset.mem_filter.mp hq
      obtain ⟨R', hR', hR'q, hR'm⟩ := hpre q hqQ
      have hRR' : R = R' := retained_prefix_unique hRr hR' hRq hR'q
      obtain ⟨hqw, hxq⟩ := Finset.mem_filter.mp hqQ
      have hqlen := mem_words.mp hqw
      refine ⟨q.take m, Finset.mem_filter.mpr ⟨take_mem_words hqw hmn.le,
        wordIval_subset_of_prefix hθ (List.take_prefix _ _) hxq⟩, ?_⟩
      rw [List.prefix_take_iff]
      exact ⟨hRq, hRR' ▸ hR'm⟩
    choose! g hgQ hgR using hf
    have hinj : Set.InjOn g supp := by
      intro R hR R' hR' hRR'
      refine retained_prefix_unique (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR').1
        (hgR R hR) ?_
      rw [hRR']
      exact hgR R' hR'
    have := Finset.card_le_card_of_injOn g (fun R hR => hgQ R hR) hinj
    have : (#supp : ℝ) ≤ #Qm := by exact_mod_cast this
    linarith
  -- Cauchy–Schwarz
  have hsupp_sum : ∑ R ∈ supp, (a R : ℝ) = ∑ R ∈ retained N θ K, (a R : ℝ) := by
    rw [hsupp]
    exact Finset.sum_filter_of_ne fun R _ h => by exact_mod_cast h
  have hsum' : (maxCount N θ x : ℝ) = ∑ R ∈ supp, (a R : ℝ) := by
    rw [hsupp_sum, ← hn, ← hQcard, hsum, Nat.cast_sum]
  have hCS := sq_sum_le_card_mul_sum_sq (s := supp) (f := fun R => (a R : ℝ))
  rw [hsum']
  calc (∑ R ∈ supp, (a R : ℝ)) ^ 2 ≤ #supp * ∑ R ∈ supp, (a R : ℝ) ^ 2 := hCS
    _ ≤ 8 * K * ∑ R ∈ supp, (a R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsupp_card (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ 8 * K * ∑ R ∈ retained N θ K, (subtreeMax N θ R x : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc ∑ R ∈ supp, (a R : ℝ) ^ 2 ≤ ∑ R ∈ supp, (subtreeMax N θ R x : ℝ) ^ 2 := by
              refine Finset.sum_le_sum fun R _ => pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2
              rw [ha_eq]
              exact_mod_cast wcount_desc_le_subtreeMax hnN θ R x
          _ ≤ ∑ R ∈ retained N θ K, (subtreeMax N θ R x : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => sq_nonneg _

end Favard.Comb
