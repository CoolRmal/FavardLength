import FavardLength.Combinatorics.Blocks
import FavardLength.Combinatorics.Propagation.Selection
import Mathlib.Analysis.Complex.Exponential

/-!
# Black and green words (G16)–(G17)

Let `W` be a family of depth-`N` words (the terminal words of the selection) and cut the words of
length `N J` into `J` blocks of length `N`. A word is *green* if one of its blocks lies in `W` and
*black* otherwise (`Favard.Comb.greenWords`, `Favard.Comb.blackWords`).

* (G16) The black words make up the proportion `(1 - p)^J ≤ e^{-pJ}` of all words, where
  `p = #W / 4^N`, so their projected union has length at most `σ e^{-pJ}`
  (`volume_biUnion_blackWords_le`).
* (G17) If `W` is witnessed with threshold `K`, every point of the green projected union is
  covered by a heavy family for the green words: the witness family of the first block in `W`,
  copied below the prefix preceding that block. The maximal-function estimate then bounds the
  green projected union by `9σ/K` (`volume_biUnion_greenWords_le`).
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard.Comb

variable {θ : ℝ}

/-- **Black words (G16)**: the projections of the black words cover at most `σ e^{-pJ}`, where
`p = #W / 4^N` is the selected fraction. -/
theorem volume_biUnion_blackWords_le (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {W : Finset Word}
    (hW : W ⊆ words N) (J : ℕ) :
    volume (⋃ v ∈ blackWords N J W, wordIval θ v) ≤
      ENNReal.ofReal (sig θ * Real.exp (-(#W / 4 ^ N * J))) := by
  refine (volume_biUnion_wordIval_le θ (blackWords_subset_words N J W)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [card_blackWords hW]
  have hWle : #W ≤ 4 ^ N := (Finset.card_le_card hW).trans_eq (card_words N)
  have h4 : (0 : ℝ) < 4 ^ N := by positivity
  have hWle' : (#W : ℝ) ≤ 4 ^ N := by exact_mod_cast hWle
  set p : ℝ := #W / 4 ^ N with hp
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one h4]
    exact hWle'
  have e : (((4 ^ N - #W) ^ J : ℕ) : ℝ) * (sig θ / 4 ^ (N * J)) = sig θ * (1 - p) ^ J := by
    rw [Nat.cast_pow, Nat.cast_sub hWle, pow_mul,
      show 1 - p = ((4 : ℝ) ^ N - #W) / 4 ^ N by rw [hp, sub_div, div_self h4.ne'], div_pow]
    push_cast
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (sig_nonneg hθ)
  calc (1 - p) ^ J ≤ Real.exp (-p) ^ J :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) J
    _ = Real.exp (-(p * J)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- **Heavy copies (G17)**: a point in the projection of a green word is covered by a heavy family
for the green words, with threshold `K`: the witness family of a block lying in `W`, copied below
the prefix preceding that block. -/
theorem exists_isHeavy_of_mem_greenWords (hθ : θ ∈ Icc 0 (π / 2)) {N J : ℕ} {K : ℝ}
    {W : Finset Word} (hW : IsWitnessed θ N K W) {v : Word} (hv : v ∈ greenWords N J W) {x : ℝ}
    (hx : x ∈ wordIval θ v) : ∃ n S, IsHeavy θ (greenWords N J W) (N * J) K x n S := by
  obtain ⟨hvw, i, hi, hblock⟩ := mem_greenWords.mp hv
  obtain ⟨n, hn, S, hS, hKS, ⟨y, hy⟩, ⟨s, hs, hsb⟩, hdesc⟩ := hW _ hblock
  have hvl : v.length = N * J := mem_words.mp hvw
  have hiN : i * N + N ≤ N * J := by nlinarith
  obtain ⟨u, hu⟩ : ∃ u, u = v.take (i * N) := ⟨_, rfl⟩
  have hul : u.length = i * N := by
    rw [hu, List.length_take, hvl]
    omega
  refine ⟨i * N + n, S.image (u ++ ·), by omega, ?_, ?_, ?_, ?_, ?_⟩
  · -- the copies have depth `i N + n`
    intro w hw
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hw
    exact append_mem_words (mem_words.mpr hul) (hS hs')
  · -- copying is injective
    rw [Finset.card_image_of_injective _ fun _ _ h => List.append_cancel_left h]
    exact hKS
  · -- the copied common point
    refine ⟨wordPos θ u + y / 4 ^ u.length, fun w hw => ?_⟩
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hw
    rw [mem_wordIval_append]
    convert hy s' hs' using 1
    field_simp
    ring
  · -- `x` lies in the projection of the copy of `s`
    refine ⟨u ++ s, Finset.mem_image_of_mem _ hs, wordIval_subset_of_prefix hθ ?_ hx⟩
    have hsb' : s <+: (v.drop (i * N)).take N := hsb
    have h2 : u ++ s <+: u ++ v.drop (i * N) :=
      (List.prefix_append_right_inj u).mpr (hsb'.trans (List.take_prefix _ _))
    rw [hu] at h2 ⊢
    rwa [List.take_append_drop] at h2
  · -- all depth-`N J` descendants of the copies are green
    intro w hw v' hv'
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hv'l, r, rfl⟩ := mem_desc.mp hv'
    rw [mem_greenWords]
    refine ⟨mem_words.mpr hv'l, i, hi, ?_⟩
    rw [List.append_assoc, block_append_of_length hul]
    have hs'l : s'.length = n := mem_words.mp (hS hs')
    refine hdesc s' hs' (take_mem_desc (List.prefix_append _ _) (by omega) ?_)
    simp only [List.length_append] at hv'l ⊢
    omega

/-- **Green words (G17)**: if `W` is witnessed with threshold `K > 0`, the projections of the
green words cover at most `9σ/K`. -/
theorem volume_biUnion_greenWords_le (hθ : θ ∈ Icc 0 (π / 2)) {N J : ℕ} {K : ℝ} (hK : 0 < K)
    {W : Finset Word} (hW : IsWitnessed θ N K W) :
    volume (⋃ v ∈ greenWords N J W, wordIval θ v) ≤ ENNReal.ofReal (9 * sig θ / K) := by
  refine (volume_le_of_forall_heavy hθ (greenWords_subset_words N J W) hK fun x hx => ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    exact exists_isHeavy_of_mem_greenWords hθ hW hv hxv
  · have hcard : (#(greenWords N J W) : ℝ) ≤ 4 ^ (N * J) := by
      exact_mod_cast (Finset.card_le_card (greenWords_subset_words N J W)).trans_eq
        (card_words _)
    have hσ := sig_nonneg hθ
    have h4 : (0 : ℝ) < 4 ^ (N * J) := by positivity
    calc 9 * sig θ * #(greenWords N J W) / (4 ^ (N * J) * K)
        ≤ 9 * sig θ * 4 ^ (N * J) / (4 ^ (N * J) * K) := by gcongr
      _ = 9 * sig θ / K := by field_simp

end Favard.Comb
