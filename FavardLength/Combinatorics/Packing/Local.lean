import FavardLength.Combinatorics.Packing.Cells

/-!
# The local packing bound (G8)

Manuscript, proof of (G7). Let `gridIcc k j` be a grid interval of length `4^{-k}`, `k ≤ N`, such
that every retained word whose projection meets it has length at least `k` (maximality of the
cells, `topLevel_le_length_of_inter`). Consider the distinct depth-`k` ancestors of the retained
words meeting it. Their projections have length `σ 4^{-k} ≥ 4^{-k}` and meet the interval, so each
contains one of its two endpoints. If there were more than `16K` ancestors, an endpoint `e` would
have `f_k(e) > 8K`; by (G6) its first crossing `m` is `< k`, and the retained prefix of the
length-`m` prefix of an ancestor containing `e` is a retained word of length `< k` meeting the
interval, which is impossible. Hence there are at most `16K` ancestors, and the packing inequality
(G1) under each of them gives (G8):
`∑_{R ∈ 𝓡, I_R ∩ D ≠ ∅} 4^{-|R|} ≤ 16 K 4^{-k}`.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ} {N : ℕ} {K : ℝ}

open Classical in
/-- The retained words whose projection meets the grid interval `gridIcc k j`. -/
noncomputable def retainedMeeting (N : ℕ) (θ K : ℝ) (k : ℕ) (j : ℤ) : Finset Word :=
  (retained N θ K).filter fun R => (wordIval θ R ∩ gridIcc k j).Nonempty

theorem mem_retainedMeeting {k : ℕ} {j : ℤ} {R : Word} :
    R ∈ retainedMeeting N θ K k j ↔
      R ∈ retained N θ K ∧ (wordIval θ R ∩ gridIcc k j).Nonempty := by
  classical
  unfold retainedMeeting
  rw [Finset.mem_filter]

theorem left_mem_gridIcc (k : ℕ) (j : ℤ) : (j : ℝ) / 4 ^ k ∈ gridIcc k j :=
  ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩

theorem right_mem_gridIcc (k : ℕ) (j : ℤ) : ((j : ℝ) + 1) / 4 ^ k ∈ gridIcc k j :=
  ⟨div_le_div_of_nonneg_right (by linarith) (by positivity), le_rfl⟩

/-- A depth-`k` projection meeting a level-`k` grid interval contains one of its endpoints. -/
theorem endpoint_mem_wordIval (hθ : θ ∈ Icc 0 (π / 2)) {k : ℕ} {j : ℤ} {a : Word}
    (ha : a.length = k) (hmeet : (wordIval θ a ∩ gridIcc k j).Nonempty) :
    (j : ℝ) / 4 ^ k ∈ wordIval θ a ∨ ((j : ℝ) + 1) / 4 ^ k ∈ wordIval θ a := by
  rw [wordIval, ha] at hmeet ⊢
  exact endpoint_mem_of_inter_nonempty
    (div_le_div_of_nonneg_right (one_le_sig hθ) (by positivity)) hmeet

/-- If every retained word meeting `gridIcc k j` has length at least `k`, then no point `e` of
the interval lies in the projections of more than `8K` depth-`k` words. -/
theorem card_le_of_forall_mem (hθ : θ ∈ Icc 0 (π / 2)) (hK : 1 < 2 * K) {k : ℕ} {j : ℤ}
    (hkN : k ≤ N)
    (hmax : ∀ R ∈ retained N θ K, (wordIval θ R ∩ gridIcc k j).Nonempty → k ≤ R.length)
    {e : ℝ} (he : e ∈ gridIcc k j) {B : Finset Word} (hB : B ⊆ words k)
    (heB : ∀ a ∈ B, e ∈ wordIval θ a) : (#B : ℝ) ≤ 8 * K := by
  by_contra hlt
  push Not at hlt
  have hcount : 8 * K ≤ (count k θ e : ℝ) :=
    hlt.le.trans (by exact_mod_cast card_le_count hθ hB heB)
  have hK0 : 0 < K := by linarith
  have hsl : e ∈ superLevel N θ (2 * K) := mem_superLevel_iff_exists.mpr ⟨k, hkN, by linarith⟩
  obtain ⟨m, hm⟩ := exists_firstCross hsl
  have hmk : m < k := hm.lt_of_le_count hθ hK hcount
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < #B := by linarith
    exact_mod_cast this
  obtain ⟨a, ha⟩ := hBne
  have hal : a.length = k := mem_words.mp (hB ha)
  obtain ⟨r, hr, hra, hrm⟩ :=
    exists_retained_prefix_of_firstCross hθ hm (hal ▸ hmk.le) (heB a ha)
  have := hmax r hr ⟨e, wordIval_subset_of_prefix hθ hra (heB a ha), he⟩
  omega

/-- **Local packing bound (G8).** If `k ≤ N` and every retained word meeting `gridIcc k j` has
length at least `k`, then the retained words meeting it satisfy
`∑ 4^{-|R|} ≤ 16 K 4^{-k}`. -/
theorem sum_retainedMeeting_le (hθ : θ ∈ Icc 0 (π / 2)) (hK : 1 < 2 * K) {k : ℕ} {j : ℤ}
    (hkN : k ≤ N)
    (hmax : ∀ R ∈ retained N θ K, (wordIval θ R ∩ gridIcc k j).Nonempty → k ≤ R.length) :
    ∑ R ∈ retainedMeeting N θ K k j, (1 / 4 ^ R.length : ℝ) ≤ 16 * K / 4 ^ k := by
  classical
  set S := retainedMeeting N θ K k j with hS
  set A := S.image (List.take k) with hA
  have hSk : ∀ R ∈ S, k ≤ R.length := fun R hR =>
    hmax R (mem_retainedMeeting.mp hR).1 (mem_retainedMeeting.mp hR).2
  have hAw : A ⊆ words k := by
    intro a ha
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_words, List.length_take]
    exact min_eq_left (hSk R hR)
  have hAmeet : ∀ a ∈ A, (wordIval θ a ∩ gridIcc k j).Nonempty := by
    intro a ha
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, hx1, hx2⟩ := (mem_retainedMeeting.mp hR).2
    exact ⟨x, wordIval_subset_of_prefix hθ (List.take_prefix _ _) hx1, hx2⟩
  -- at most `16K` ancestors
  set e₁ : ℝ := (j : ℝ) / 4 ^ k
  set e₂ : ℝ := ((j : ℝ) + 1) / 4 ^ k
  set A₁ := A.filter fun a => e₁ ∈ wordIval θ a
  set A₂ := A.filter fun a => e₂ ∈ wordIval θ a
  have h₁ : (#A₁ : ℝ) ≤ 8 * K :=
    card_le_of_forall_mem hθ hK hkN hmax (left_mem_gridIcc k j)
      ((Finset.filter_subset _ _).trans hAw) fun a ha => (Finset.mem_filter.mp ha).2
  have h₂ : (#A₂ : ℝ) ≤ 8 * K :=
    card_le_of_forall_mem hθ hK hkN hmax (right_mem_gridIcc k j)
      ((Finset.filter_subset _ _).trans hAw) fun a ha => (Finset.mem_filter.mp ha).2
  have hcardN : #A ≤ #A₁ + #A₂ := by
    calc #A ≤ #(A₁ ∪ A₂) := by
          refine Finset.card_le_card fun a ha => ?_
          rcases endpoint_mem_wordIval hθ (mem_words.mp (hAw ha)) (hAmeet a ha) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, h⟩)
      _ ≤ #A₁ + #A₂ := Finset.card_union_le _ _
  have hcard : (#A : ℝ) ≤ 16 * K := by
    have : (#A : ℝ) ≤ #A₁ + #A₂ := by exact_mod_cast hcardN
    linarith
  -- the packing inequality (G1) under each ancestor
  have hfib : ∀ a ∈ A,
      ∑ R ∈ S with R.take k = a, (1 / 4 ^ R.length : ℝ) ≤ 1 / 4 ^ k := by
    intro a ha
    rw [← mem_words.mp (hAw ha)]
    refine PrefixFree.sum_inv_four_pow_le ((prefixFree_retained N θ K).subset ?_) ?_
    · intro R hR
      exact (mem_retainedMeeting.mp (Finset.mem_filter.mp hR).1).1
    · intro R hR
      rw [← (Finset.mem_filter.mp hR).2]
      exact List.take_prefix _ _
  calc ∑ R ∈ S, (1 / 4 ^ R.length : ℝ)
      = ∑ a ∈ A, ∑ R ∈ S with R.take k = a, (1 / 4 ^ R.length : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun R hR => Finset.mem_image_of_mem _ hR) _).symm
    _ ≤ ∑ a ∈ A, (1 / 4 ^ k : ℝ) := Finset.sum_le_sum hfib
    _ = #A * (1 / 4 ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 16 * K * (1 / 4 ^ k) := by gcongr
    _ = 16 * K / 4 ^ k := by ring

/-- **(G8) for the maximal cells**: the retained words meeting the cell of a retained word
`R₁` satisfy `∑ 4^{-|R|} ≤ 16 K 4^{-k}`, `k` the level of the cell. -/
theorem sum_retainedMeeting_topCell_le (hθ : θ ∈ Icc 0 (π / 2)) (hK : 1 < 2 * K) {R₁ : Word}
    (hR₁ : R₁ ∈ retained N θ K) :
    ∑ R ∈ retainedMeeting N θ K (topCell N θ K R₁).1 (topCell N θ K R₁).2,
        (1 / 4 ^ R.length : ℝ) ≤ 16 * K / 4 ^ (topCell N θ K R₁).1 :=
  sum_retainedMeeting_le hθ hK (topLevel_le hθ hR₁)
    fun _ hR hmeet => topLevel_le_length_of_inter hθ hR₁ hR hmeet

end Favard.Comb
