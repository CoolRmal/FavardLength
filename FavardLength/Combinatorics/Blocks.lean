import FavardLength.Combinatorics.Words

/-!
# Block decomposition of long words (for G15–G17)

A word of length `N * J` is cut into `J` consecutive blocks of length `N`
(`block N i w = (w.drop (i * N)).take N`). Given a family `W` of words of length `N`, a word is
*green* if one of its blocks belongs to `W` and *black* otherwise. We prove that the number of
black words is exactly `(4^N - #W)^J` (`card_blackWords`), and record the block of a word with a
prescribed prefix of length `i * N`.
-/

open Finset

namespace Favard.Comb

/-- The `i`-th block of length `N` of the word `w`. -/
def block (N i : ℕ) (w : Word) : Word :=
  (w.drop (i * N)).take N

theorem block_zero (N : ℕ) (w : Word) : block N 0 w = w.take N := by
  simp [block]

/-- If `u` has length `i * N`, the `i`-th block of `u ++ z` is the first `N` letters of `z`. -/
theorem block_append_of_length {N i : ℕ} {u : Word} (hu : u.length = i * N) (z : Word) :
    block N i (u ++ z) = z.take N := by
  simp [block, ← hu]

/-- The blocks of `a ++ b` with `|a| = N` after the first are the blocks of `b`. -/
theorem block_succ_append {N i : ℕ} {a : Word} (ha : a.length = N) (b : Word) :
    block N (i + 1) (a ++ b) = block N i b := by
  simp only [block, Nat.succ_mul, add_comm (i * N) N, ← List.drop_drop]
  rw [List.drop_left' ha]

theorem block_mem_words {N J i : ℕ} {w : Word} (hw : w ∈ words (N * J)) (hi : i < J) :
    block N i w ∈ words N := by
  rw [mem_words] at hw ⊢
  simp only [block, List.length_take, List.length_drop, hw]
  have : (i + 1) * N ≤ N * J := by rw [mul_comm N J]; exact Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  omega

/-- A word of length at least `N` extending `s` (with `|s| ≤ N`) has its first `N` letters among
the depth-`N` descendants of `s`. -/
theorem take_mem_desc {N : ℕ} {s z : Word} (hsz : s <+: z) (hs : s.length ≤ N)
    (hz : N ≤ z.length) : z.take N ∈ desc s N := by
  rw [mem_desc]
  refine ⟨by simp [hz], ?_⟩
  rw [List.prefix_take_iff]
  exact ⟨hsz, hs⟩

open Classical in
/-- The black words: words of length `N * J` none of whose `J` blocks lies in `W`. -/
noncomputable def blackWords (N J : ℕ) (W : Finset Word) : Finset Word :=
  (words (N * J)).filter fun v => ∀ i < J, block N i v ∉ W

open Classical in
/-- The green words: words of length `N * J` some block of which lies in `W`. -/
noncomputable def greenWords (N J : ℕ) (W : Finset Word) : Finset Word :=
  (words (N * J)).filter fun v => ∃ i < J, block N i v ∈ W

theorem mem_blackWords {N J : ℕ} {W : Finset Word} {v : Word} :
    v ∈ blackWords N J W ↔ v ∈ words (N * J) ∧ ∀ i < J, block N i v ∉ W := by
  classical
  unfold blackWords
  rw [Finset.mem_filter]

theorem mem_greenWords {N J : ℕ} {W : Finset Word} {v : Word} :
    v ∈ greenWords N J W ↔ v ∈ words (N * J) ∧ ∃ i < J, block N i v ∈ W := by
  classical
  unfold greenWords
  rw [Finset.mem_filter]

theorem greenWords_subset_words (N J : ℕ) (W : Finset Word) : greenWords N J W ⊆ words (N * J) :=
  fun _ hv => (mem_greenWords.mp hv).1

theorem blackWords_subset_words (N J : ℕ) (W : Finset Word) : blackWords N J W ⊆ words (N * J) :=
  fun _ hv => (mem_blackWords.mp hv).1

/-- Every word of length `N * J` is black or green. -/
theorem words_eq_blackWords_union_greenWords (N J : ℕ) (W : Finset Word) :
    words (N * J) = blackWords N J W ∪ greenWords N J W := by
  ext v
  rw [Finset.mem_union, mem_blackWords, mem_greenWords]
  constructor
  · intro hv
    by_cases h : ∃ i < J, block N i v ∈ W
    · exact Or.inr ⟨hv, h⟩
    · push Not at h
      exact Or.inl ⟨hv, h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

theorem blackWords_succ {N J : ℕ} (W : Finset Word) :
    blackWords N (J + 1) W =
      ((words N \ W) ×ˢ blackWords N J W).image fun p => p.1 ++ p.2 := by
  ext v
  rw [mem_blackWords, Finset.mem_image]
  constructor
  · rintro ⟨hv, hblk⟩
    rw [mem_words] at hv
    have hlen : N ≤ v.length := by rw [hv, Nat.mul_succ]; omega
    refine ⟨(v.take N, v.drop N), ?_, List.take_append_drop _ _⟩
    rw [Finset.mem_product, Finset.mem_sdiff, mem_blackWords, mem_words, mem_words]
    have hb : ∀ i, block N (i + 1) v = block N i (v.drop N) := by
      intro i
      conv_lhs => rw [← List.take_append_drop N v]
      exact block_succ_append (by simp [hlen]) _
    refine ⟨⟨by simp [hlen], by simpa [block_zero] using hblk 0 (Nat.succ_pos J)⟩,
      by simp [hv, Nat.mul_succ], fun i hi => ?_⟩
    rw [← hb]
    exact hblk (i + 1) (Nat.succ_lt_succ hi)
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product, Finset.mem_sdiff, mem_blackWords] at hab
    obtain ⟨⟨ha, haW⟩, hb, hbblk⟩ := hab
    have hal : a.length = N := mem_words.mp ha
    refine ⟨?_, fun i hi => ?_⟩
    · have := append_mem_words ha hb
      rwa [show N + N * J = N * (J + 1) by ring] at this
    · rcases i with _ | i
      · rw [block_zero, List.take_left' hal]
        exact haW
      · rw [block_succ_append hal]
        exact hbblk i (Nat.lt_of_succ_lt_succ hi)

/-- **Black words (G16)**: exactly `(4^N - #W)^J` words of length `N * J` have no block in `W`. -/
theorem card_blackWords {N : ℕ} {W : Finset Word} (hW : W ⊆ words N) (J : ℕ) :
    #(blackWords N J W) = (4 ^ N - #W) ^ J := by
  induction J with
  | zero =>
    have : blackWords N 0 W = {[]} := by
      ext v
      simp [mem_blackWords]
    simp [this]
  | succ J ih =>
    rw [blackWords_succ, Finset.card_image_of_injOn, Finset.card_product, ih,
      Finset.card_sdiff_of_subset hW, card_words, pow_succ, mul_comm]
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_sdiff] at hab hab'
    have hl : a.length = a'.length :=
      (mem_words.mp hab.1.1).trans (mem_words.mp hab'.1.1).symm
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact Prod.ext h1 h2

end Favard.Comb
