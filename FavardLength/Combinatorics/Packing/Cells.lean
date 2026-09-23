import FavardLength.Combinatorics.Grid
import FavardLength.Combinatorics.Marking

/-!
# Maximal eligible grid cells of the packing construction

Manuscript, proof of (G7). Fix `N`, `θ ∈ [0, π/2]`, a threshold `K` and the retained family
`𝓡 = retained N θ K`. A closed base-four grid interval `gridIcc k j` of length `4^{-k}` is
*eligible* (`GridEligible`) if it meets the projection of a retained word `R` of side length
`4^{-|R|} ≥ 4^{-k}`, i.e. `|R| ≤ k`.

Instead of the maximal eligible intervals themselves we use, for each `R ∈ 𝓡`, the largest
eligible grid ancestor of the level-`|R|` grid interval containing the left endpoint of the
projection of `R` (`topCell`); the family of these cells is `maxCells N θ K`, a finite set by
construction. We prove:

* every retained word meets its own cell (`inter_topCell_nonempty`);
* **maximality**: a retained word meeting the cell of level `k` of some `R₁ ∈ 𝓡` has length at
  least `k` (`topLevel_le_length_of_inter`), and some retained word of length exactly `k` meets
  it (`exists_retained_length_eq_topLevel`);
* distinct cells meet in a null set (`volume_inter_eq_zero_of_mem_maxCells`).
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ} {N : ℕ} {K : ℝ}

/-- The index `⌊p 4^{|w|}⌋` of the level-`|w|` grid interval containing the left endpoint
`p = wordPos θ w` of the projection of `w`. -/
noncomputable def baseIdx (θ : ℝ) (w : Word) : ℤ :=
  ⌊wordPos θ w * 4 ^ w.length⌋

theorem wordPos_mem_gridIcc_baseIdx (θ : ℝ) (w : Word) :
    wordPos θ w ∈ gridIcc w.length (baseIdx θ w) :=
  mem_gridIcc_floor _ _

/-- A grid interval `gridIcc k j` is *eligible* if it meets the projection of a retained word
whose side length `4^{-|R|}` is at least the length `4^{-k}` of the interval. -/
def GridEligible (N : ℕ) (θ K : ℝ) (k : ℕ) (j : ℤ) : Prop :=
  ∃ R ∈ retained N θ K, R.length ≤ k ∧ (wordIval θ R ∩ gridIcc k j).Nonempty

/-- The level-`k` grid ancestor (`k ≤ |R|`) of the base interval of `R` is eligible. -/
def AncEligible (N : ℕ) (θ K : ℝ) (R : Word) (k : ℕ) : Prop :=
  k ≤ R.length ∧ GridEligible N θ K k (gridAnc R.length k (baseIdx θ R))

/-- The base interval of a retained word is eligible. -/
theorem ancEligible_length (hθ : θ ∈ Icc 0 (π / 2)) {R : Word} (hR : R ∈ retained N θ K) :
    AncEligible N θ K R R.length := by
  refine ⟨le_rfl, R, hR, le_rfl, wordPos θ R, wordPos_mem_wordIval hθ R, ?_⟩
  rw [gridAnc_self]
  exact wordPos_mem_gridIcc_baseIdx θ R

open Classical in
/-- The level of the largest eligible grid ancestor of the base interval of `R`. -/
noncomputable def topLevel (N : ℕ) (θ K : ℝ) (R : Word) : ℕ :=
  if h : ∃ k, AncEligible N θ K R k then Nat.find h else 0

/-- The largest eligible grid ancestor `(level, index)` of the base interval of `R`. -/
noncomputable def topCell (N : ℕ) (θ K : ℝ) (R : Word) : ℕ × ℤ :=
  (topLevel N θ K R, gridAnc R.length (topLevel N θ K R) (baseIdx θ R))

/-- The family `𝒟` of maximal cells: the cells `topCell R` of the retained words `R`. -/
noncomputable def maxCells (N : ℕ) (θ K : ℝ) : Finset (ℕ × ℤ) :=
  (retained N θ K).image (topCell N θ K)

theorem topCell_fst (R : Word) : (topCell N θ K R).1 = topLevel N θ K R := rfl

theorem topCell_snd (R : Word) :
    (topCell N θ K R).2 = gridAnc R.length (topLevel N θ K R) (baseIdx θ R) := rfl

theorem topLevel_spec (hθ : θ ∈ Icc 0 (π / 2)) {R : Word} (hR : R ∈ retained N θ K) :
    AncEligible N θ K R (topLevel N θ K R) := by
  classical
  have h : ∃ k, AncEligible N θ K R k := ⟨_, ancEligible_length hθ hR⟩
  unfold topLevel
  split_ifs
  exact Nat.find_spec h

/-- Minimality of the top level: no smaller level gives an eligible ancestor. -/
theorem not_ancEligible_of_lt_topLevel {R : Word} {m : ℕ} (hm : m < topLevel N θ K R) :
    ¬AncEligible N θ K R m := by
  classical
  unfold topLevel at hm
  split_ifs at hm with h
  · exact Nat.find_min h hm
  · exact absurd hm (Nat.not_lt_zero _)

theorem topLevel_le_length (hθ : θ ∈ Icc 0 (π / 2)) {R : Word} (hR : R ∈ retained N θ K) :
    topLevel N θ K R ≤ R.length :=
  (topLevel_spec hθ hR).1

theorem gridEligible_topCell (hθ : θ ∈ Icc 0 (π / 2)) {R : Word} (hR : R ∈ retained N θ K) :
    GridEligible N θ K (topCell N θ K R).1 (topCell N θ K R).2 :=
  (topLevel_spec hθ hR).2

/-- Every retained word meets its own cell. -/
theorem inter_topCell_nonempty (hθ : θ ∈ Icc 0 (π / 2)) {R : Word} (hR : R ∈ retained N θ K) :
    (wordIval θ R ∩ gridIcc (topCell N θ K R).1 (topCell N θ K R).2).Nonempty :=
  ⟨wordPos θ R, wordPos_mem_wordIval hθ R,
    gridIcc_subset_gridAnc (topLevel_le_length hθ hR) _ (wordPos_mem_gridIcc_baseIdx θ R)⟩

/-- **Maximality (i)**: a retained word whose projection meets the cell of `R₁` has side length
at most the length of the cell. Otherwise its level-`|R|` grid ancestor would be an eligible
ancestor of the base interval of `R₁` strictly larger than the cell. -/
theorem topLevel_le_length_of_inter (hθ : θ ∈ Icc 0 (π / 2)) {R₁ R : Word}
    (hR₁ : R₁ ∈ retained N θ K) (hR : R ∈ retained N θ K)
    (h : (wordIval θ R ∩ gridIcc (topCell N θ K R₁).1 (topCell N θ K R₁).2).Nonempty) :
    topLevel N θ K R₁ ≤ R.length := by
  by_contra hlt
  push Not at hlt
  have hk₁ : topLevel N θ K R₁ ≤ R₁.length := topLevel_le_length hθ hR₁
  refine not_ancEligible_of_lt_topLevel hlt ⟨hlt.le.trans hk₁, R, hR, le_rfl, ?_⟩
  obtain ⟨x, hxR, hxD⟩ := h
  refine ⟨x, hxR, ?_⟩
  rw [topCell_fst, topCell_snd] at hxD
  rw [← gridAnc_gridAnc hlt.le hk₁]
  exact gridIcc_subset_gridAnc hlt.le _ hxD

/-- **Maximality (ii)**: some retained word of length exactly the level of the cell of `R₁`
meets it. -/
theorem exists_retained_length_eq_topLevel (hθ : θ ∈ Icc 0 (π / 2)) {R₁ : Word}
    (hR₁ : R₁ ∈ retained N θ K) :
    ∃ R₀ ∈ retained N θ K, R₀.length = topLevel N θ K R₁ ∧
      (wordIval θ R₀ ∩ gridIcc (topCell N θ K R₁).1 (topCell N θ K R₁).2).Nonempty := by
  obtain ⟨R₀, hR₀, hle, hmeet⟩ := gridEligible_topCell hθ hR₁
  exact ⟨R₀, hR₀, le_antisymm hle (topLevel_le_length_of_inter hθ hR₁ hR₀ hmeet), hmeet⟩

/-- The level of a cell is at most `N`. -/
theorem topLevel_le (hθ : θ ∈ Icc 0 (π / 2)) {R₁ : Word} (hR₁ : R₁ ∈ retained N θ K) :
    topLevel N θ K R₁ ≤ N := by
  obtain ⟨R₀, hR₀, hl, -⟩ := exists_retained_length_eq_topLevel hθ hR₁
  exact hl ▸ length_le_of_mem_retained hR₀

/-- Cells of comparable levels: if the cell of `R₁` has level at most that of `R₂`, then they
coincide or meet in a null set. -/
theorem topCell_eq_or_volume_inter_eq_zero (hθ : θ ∈ Icc 0 (π / 2)) {R₁ R₂ : Word}
    (hR₁ : R₁ ∈ retained N θ K) (hR₂ : R₂ ∈ retained N θ K)
    (hle : topLevel N θ K R₁ ≤ topLevel N θ K R₂) :
    topCell N θ K R₁ = topCell N θ K R₂ ∨
      volume (gridIcc (topCell N θ K R₁).1 (topCell N θ K R₁).2 ∩
        gridIcc (topCell N θ K R₂).1 (topCell N θ K R₂).2) = 0 := by
  rcases gridAnc_eq_or_volume_inter_eq_zero hle (topCell N θ K R₁).2 (topCell N θ K R₂).2 with
    h | h
  · left
    rcases hle.lt_or_eq with hlt | heq
    · -- the cell of `R₁` would be an eligible ancestor of the base interval of `R₂`
      exfalso
      have hk₂ : topLevel N θ K R₂ ≤ R₂.length := topLevel_le_length hθ hR₂
      refine not_ancEligible_of_lt_topLevel hlt ⟨hlt.le.trans hk₂, ?_⟩
      have hE := gridEligible_topCell hθ hR₁
      rw [← h, topCell_fst, topCell_snd R₂, gridAnc_gridAnc hlt.le hk₂] at hE
      exact hE
    · rw [topCell_snd R₂, ← heq, gridAnc_self] at h
      refine Prod.ext heq ?_
      rw [topCell_snd R₂, ← heq]
      exact h.symm
  · exact Or.inr h

/-- Distinct maximal cells meet in a null set. -/
theorem volume_inter_eq_zero_of_mem_maxCells (hθ : θ ∈ Icc 0 (π / 2)) {D₁ D₂ : ℕ × ℤ}
    (h₁ : D₁ ∈ maxCells N θ K) (h₂ : D₂ ∈ maxCells N θ K) (hne : D₁ ≠ D₂) :
    volume (gridIcc D₁.1 D₁.2 ∩ gridIcc D₂.1 D₂.2) = 0 := by
  classical
  obtain ⟨R₁, hR₁, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨R₂, hR₂, rfl⟩ := Finset.mem_image.mp h₂
  rcases le_total (topLevel N θ K R₁) (topLevel N θ K R₂) with hle | hle
  · exact (topCell_eq_or_volume_inter_eq_zero hθ hR₁ hR₂ hle).resolve_left hne
  · rw [inter_comm]
    exact (topCell_eq_or_volume_inter_eq_zero hθ hR₂ hR₁ hle).resolve_left (Ne.symm hne)

end Favard.Comb
