import FavardLength.Squares
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Words over the four-letter alphabet

A construction square of the four-corner Cantor set is coded by a finite word over the alphabet
`Bool × Bool` (x-digit, y-digit); a square contains another exactly when its word is a prefix
of the other's word. This file sets up the word combinatorics used by the combinatorial
dichotomy (manuscript `favard-optimized-quarter-proof.md`, section "The combinatorial
dichotomy"):

* `Favard.Comb.words n`: the `4 ^ n` words of length `n` (the image of `SqCode n` under
  `List.ofFn`);
* `Favard.Comb.desc w n`: the depth-`n` descendants of `w`, of which there are
  `4 ^ (n - w.length)`;
* `Favard.Comb.PrefixFree`: prefix-free families, their disjoint descendant sets, and the packing
  inequality (G1) `∑_{R} 4^{-|R|} ≤ 4^{-|Q|}` for a prefix-free family below `Q`.
-/

open Finset

namespace Favard.Comb

/-- A finite word over the four-letter alphabet `Bool × Bool`, coding a construction square. -/
abbrev Word := List (Bool × Bool)

/-- The words of length `n`, as the image of the square codes `SqCode n` under `List.ofFn`. -/
def words (n : ℕ) : Finset Word :=
  (Finset.univ : Finset (SqCode n)).image List.ofFn

@[simp]
theorem mem_words {n : ℕ} {w : Word} : w ∈ words n ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · rintro rfl
    exact Finset.mem_image.mpr ⟨fun i => w[(i : ℕ)], Finset.mem_univ _, List.ofFn_getElem⟩

theorem ofFn_mem_words {n : ℕ} (w : SqCode n) : List.ofFn w ∈ words n :=
  mem_words.mpr List.length_ofFn

@[simp]
theorem card_words (n : ℕ) : #(words n) = 4 ^ n := by
  rw [words, Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
    Fintype.card_fun]
  simp

theorem nil_mem_words : ([] : Word) ∈ words 0 := by simp

@[simp]
theorem words_zero : words 0 = {[]} := by
  ext w
  simp

theorem append_mem_words {m n : ℕ} {u v : Word} (hu : u ∈ words m) (hv : v ∈ words n) :
    u ++ v ∈ words (m + n) := by
  simp only [mem_words] at *
  simp [hu, hv]

theorem take_mem_words {m n : ℕ} {w : Word} (hw : w ∈ words n) (h : m ≤ n) :
    w.take m ∈ words m := by
  simp only [mem_words] at *
  simp [hw, h]

theorem drop_mem_words {m n : ℕ} {w : Word} (hw : w ∈ words n) :
    w.drop m ∈ words (n - m) := by
  simp only [mem_words] at *
  simp [hw]

/-- The words of length at most `N`. -/
def wordsLE (N : ℕ) : Finset Word :=
  (Finset.range (N + 1)).biUnion words

@[simp]
theorem mem_wordsLE {N : ℕ} {w : Word} : w ∈ wordsLE N ↔ w.length ≤ N := by
  simp [wordsLE]

/-! ### Descendants -/

/-- The depth-`n` descendants of `w`: the words of length `n` having `w` as a prefix. -/
def desc (w : Word) (n : ℕ) : Finset Word :=
  (words n).filter (w <+: ·)

@[simp]
theorem mem_desc {w v : Word} {n : ℕ} : v ∈ desc w n ↔ v.length = n ∧ w <+: v := by
  simp [desc]

theorem desc_subset_words (w : Word) (n : ℕ) : desc w n ⊆ words n :=
  Finset.filter_subset _ _

theorem desc_eq_image {w : Word} {n : ℕ} (h : w.length ≤ n) :
    desc w n = (words (n - w.length)).image (w ++ ·) := by
  ext v
  simp only [mem_desc, Finset.mem_image, mem_words]
  constructor
  · rintro ⟨hv, t, rfl⟩
    refine ⟨t, ?_, rfl⟩
    simp at hv
    omega
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, List.prefix_append _ _⟩
    simp [ht]
    omega

theorem card_desc {w : Word} {n : ℕ} (h : w.length ≤ n) :
    #(desc w n) = 4 ^ (n - w.length) := by
  rw [desc_eq_image h, Finset.card_image_of_injective _ fun _ _ h => List.append_cancel_left h,
    card_words]

theorem desc_self (w : Word) : desc w w.length = {w} := by
  ext v
  simp only [mem_desc, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hp⟩
    exact (hp.eq_of_length hv.symm).symm
  · rintro rfl
    exact ⟨rfl, List.prefix_refl _⟩

theorem desc_subset_desc {u w : Word} (h : u <+: w) (n : ℕ) : desc w n ⊆ desc u n := by
  intro v hv
  rw [mem_desc] at hv ⊢
  exact ⟨hv.1, h.trans hv.2⟩

theorem mem_desc_take {v : Word} {n : ℕ} (hv : v ∈ words n) (m : ℕ) :
    v ∈ desc (v.take m) n := by
  rw [mem_desc]
  exact ⟨mem_words.mp hv, List.take_prefix _ _⟩

/-- Two words with a common extension are comparable. -/
theorem prefix_or_prefix_of_mem_desc {u w v : Word} {n : ℕ} (hu : v ∈ desc u n)
    (hw : v ∈ desc w n) : u <+: w ∨ w <+: u :=
  List.prefix_or_prefix_of_prefix (mem_desc.mp hu).2 (mem_desc.mp hw).2

/-! ### Prefix-free families -/

/-- A family of words is prefix-free when no member is a proper ancestor of another. -/
def PrefixFree (P : Finset Word) : Prop :=
  ∀ u ∈ P, ∀ w ∈ P, u <+: w → u = w

theorem PrefixFree.subset {P Q : Finset Word} (hQ : PrefixFree Q) (h : P ⊆ Q) : PrefixFree P :=
  fun u hu w hw huw => hQ u (h hu) w (h hw) huw

/-- In a prefix-free family, a word has at most one prefix. -/
theorem PrefixFree.eq_of_prefix {P : Finset Word} (hP : PrefixFree P) {u w v : Word}
    (hu : u ∈ P) (hw : w ∈ P) (huv : u <+: v) (hwv : w <+: v) : u = w := by
  rcases List.prefix_or_prefix_of_prefix huv hwv with h | h
  · exact hP u hu w hw h
  · exact (hP w hw u hu h).symm

/-- The descendant sets of the members of a prefix-free family are pairwise disjoint. -/
theorem PrefixFree.pairwiseDisjoint_desc {P : Finset Word} (hP : PrefixFree P) (n : ℕ) :
    (P : Set Word).PairwiseDisjoint (desc · n) := by
  intro u hu w hw huw
  rw [Function.onFun, Finset.disjoint_left]
  intro v hvu hvw
  exact huw (hP.eq_of_prefix hu hw (mem_desc.mp hvu).2 (mem_desc.mp hvw).2)

/-- The number of depth-`M` descendants of a prefix-free family. -/
theorem PrefixFree.card_biUnion_desc {P : Finset Word} (hP : PrefixFree P) {M : ℕ}
    (hM : ∀ w ∈ P, w.length ≤ M) :
    #(P.biUnion (desc · M)) = ∑ w ∈ P, 4 ^ (M - w.length) := by
  rw [Finset.card_biUnion (hP.pairwiseDisjoint_desc M)]
  exact Finset.sum_congr rfl fun w hw => card_desc (hM w hw)

/-- **Packing inequality (G1)**, counting form: a prefix-free family below `u` has at most as
many depth-`M` descendants as `u`. -/
theorem PrefixFree.sum_four_pow_le {P : Finset Word} (hP : PrefixFree P) {u : Word}
    (hu : ∀ w ∈ P, u <+: w) {M : ℕ} (hM : ∀ w ∈ P, w.length ≤ M) (huM : u.length ≤ M) :
    ∑ w ∈ P, 4 ^ (M - w.length) ≤ 4 ^ (M - u.length) := by
  rw [← hP.card_biUnion_desc hM, ← card_desc huM]
  refine Finset.card_le_card ?_
  intro v hv
  obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
  exact desc_subset_desc (hu w hw) M hvw

/-- **Packing inequality (G1)**: if a prefix-free family lies below `u`, the side lengths
`4^{-|w|}` of its members sum to at most the side length of `u`. -/
theorem PrefixFree.sum_inv_four_pow_le {P : Finset Word} (hP : PrefixFree P) {u : Word}
    (hu : ∀ w ∈ P, u <+: w) :
    ∑ w ∈ P, (1 / 4 ^ w.length : ℝ) ≤ 1 / 4 ^ u.length := by
  set M := P.sup List.length ⊔ u.length
  have hM : ∀ w ∈ P, w.length ≤ M := fun w hw =>
    le_sup_of_le_left (Finset.le_sup (f := List.length) hw)
  have huM : u.length ≤ M := le_sup_right
  have h := hP.sum_four_pow_le hu hM huM
  have h4 : (0 : ℝ) < 4 ^ M := by positivity
  have key : ∀ k ≤ M, (1 / 4 ^ k : ℝ) = (4 ^ (M - k) : ℕ) / 4 ^ M := by
    intro k hk
    rw [Nat.cast_pow, Nat.cast_ofNat, eq_div_iff h4.ne', one_div,
      pow_sub₀ _ (by norm_num : (4 : ℝ) ≠ 0) hk]
    ring
  rw [Finset.sum_congr rfl fun w hw => key _ (hM w hw), key _ huM, ← Finset.sum_div,
    div_le_div_iff_of_pos_right h4, ← Nat.cast_sum]
  exact_mod_cast h

end Favard.Comb
