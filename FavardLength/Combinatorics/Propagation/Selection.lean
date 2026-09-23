import FavardLength.Combinatorics.Maximal

/-!
# Terminal selection (G13)–(G15)

Fix a direction `θ ∈ [0, π/2]`, a threshold `K > 0` and a depth `N`. Every point of the
superlevel set `{F_N ≥ K}` lies in the projections of `⌈K⌉₊` words of a common length `n ≤ N`
(a *witness family*, (G13)). We index the possible witness families by pairs `(w₀, S)`
(`Favard.Comb.witnessIndex`): `S` is a family of `⌈K⌉₊` words of length `|w₀| ≤ N` containing
`w₀`, whose projections share a point. The index `(w₀, S)` is attached to the concentric triple
`tripleIval θ w₀` of the projection of `w₀`, which contains the projections of all members of `S`.

The finite Vitali lemma selects a subfamily with pairwise disjoint triples carrying a third of
the measure of the superlevel set (G14). The members of the selected families form a prefix-free
family, and their depth-`N` descendants form the set `W` of *terminal words*. We prove
(`Favard.Comb.exists_witnessed_terminal`):

* `W` is *witnessed* (`Favard.Comb.IsWitnessed`): each terminal word descends from a member of a
  family of at least `K` words of a common length `n ≤ N`, with a common projected point, all of
  whose depth-`N` descendants are terminal;
* (G15) `μ_N(K) ≤ 9 σ #W / (4^N K)`, i.e. the selected fraction `#W / 4^N` is at least
  `K μ_N(K) / (9σ)`.
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard.Comb

variable {θ : ℝ}

/-! ### Witness families -/

open Classical in
/-- The witness index set: pairs `(w₀, S)` where `S` is a family of `⌈K⌉₊` words of the common
length `|w₀| ≤ N`, containing `w₀`, whose projections share a point. -/
noncomputable def witnessIndex (N : ℕ) (θ K : ℝ) : Finset (Word × Finset Word) :=
  (wordsLE N ×ˢ (wordsLE N).powerset).filter fun p =>
    p.2 ⊆ words p.1.length ∧ #p.2 = ⌈K⌉₊ ∧ p.1 ∈ p.2 ∧ ∃ y, ∀ w ∈ p.2, y ∈ wordIval θ w

theorem mem_witnessIndex {N : ℕ} {K : ℝ} {p : Word × Finset Word} :
    p ∈ witnessIndex N θ K ↔ p.1.length ≤ N ∧ p.2 ⊆ words p.1.length ∧ #p.2 = ⌈K⌉₊ ∧
      p.1 ∈ p.2 ∧ ∃ y, ∀ w ∈ p.2, y ∈ wordIval θ w := by
  classical
  unfold witnessIndex
  rw [Finset.mem_filter, Finset.mem_product, mem_wordsLE, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨h1, -⟩, h⟩
    exact ⟨h1, h⟩
  · rintro ⟨h1, h2, h⟩
    refine ⟨⟨h1, fun w hw => ?_⟩, h2, h⟩
    rw [mem_wordsLE, mem_words.mp (h2 hw)]
    exact h1

/-- The projections of the members of a witness family lie in the triple attached to it. -/
theorem wordIval_subset_tripleIval_of_mem_witnessIndex {N : ℕ} {K : ℝ}
    {p : Word × Finset Word} (hp : p ∈ witnessIndex N θ K) {w : Word} (hw : w ∈ p.2) :
    wordIval θ w ⊆ tripleIval θ p.1 := by
  obtain ⟨-, hS, -, h0, y, hy⟩ := mem_witnessIndex.mp hp
  exact wordIval_subset_tripleIval (mem_words.mp (hS hw)) (hy w hw) (hy p.1 h0)

/-- **Witness families (G13)**: the superlevel set is covered by the triples attached to the
witness families. -/
theorem superLevel_subset_biUnion_tripleIval (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ}
    (hK : 0 < K) : superLevel N θ K ⊆ ⋃ p ∈ witnessIndex N θ K, tripleIval θ p.1 := by
  intro x hx
  obtain ⟨n, hn, S, hS, hcard, hxS⟩ := exists_witness_family hθ hx
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.ceil_pos.mpr hK
  obtain ⟨w₀, hw₀⟩ := hne
  have hl : w₀.length = n := mem_words.mp (hS hw₀)
  refine Set.mem_iUnion₂.mpr ⟨(w₀, S), ?_, wordIval_subset_tripleIval_self hθ w₀ (hxS w₀ hw₀)⟩
  rw [mem_witnessIndex]
  refine ⟨?_, ?_, hcard, hw₀, x, hxS⟩
  · rw [hl]
    exact hn
  · rw [hl]
    exact hS

/-! ### Selection -/

/-- A *selection*: a family of witness indices whose attached triples are pairwise disjoint. -/
def IsSelection (N : ℕ) (θ K : ℝ) (t : Finset (Word × Finset Word)) : Prop :=
  t ⊆ witnessIndex N θ K ∧
    (t : Set (Word × Finset Word)).PairwiseDisjoint fun p => tripleIval θ p.1

/-- **Selection (G14)**: a selection whose triples carry a third of the measure of the
superlevel set. -/
theorem exists_isSelection (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ t, IsSelection N θ K t ∧
      volume (superLevel N θ K) ≤ 3 * ∑ p ∈ t, volume (tripleIval θ p.1) := by
  obtain ⟨t, hts, htd, hvol⟩ := exists_disjoint_subfamily_volume_le (witnessIndex N θ K)
    (fun p => wordPos θ p.1 - sig θ / 4 ^ p.1.length)
    (fun p => wordPos θ p.1 + 2 * (sig θ / 4 ^ p.1.length))
  exact ⟨t, ⟨hts, htd⟩, (measure_mono (superLevel_subset_biUnion_tripleIval hθ N hK)).trans hvol⟩

namespace IsSelection

variable {N : ℕ} {K : ℝ} {t : Finset (Word × Finset Word)}

/-- Members of two different selected families have disjoint projections. -/
theorem disjoint_wordIval (ht : IsSelection N θ K t) {p q : Word × Finset Word} (hp : p ∈ t)
    (hq : q ∈ t) (hpq : p ≠ q) {u w : Word} (hu : u ∈ p.2) (hw : w ∈ q.2) :
    Disjoint (wordIval θ u) (wordIval θ w) :=
  (ht.2 hp hq hpq).mono (wordIval_subset_tripleIval_of_mem_witnessIndex (ht.1 hp) hu)
    (wordIval_subset_tripleIval_of_mem_witnessIndex (ht.1 hq) hw)

/-- Different selected families are disjoint. -/
theorem pairwiseDisjoint_snd (hθ : θ ∈ Icc 0 (π / 2)) (ht : IsSelection N θ K t) :
    (t : Set (Word × Finset Word)).PairwiseDisjoint Prod.snd := by
  intro p hp q hq hpq
  rw [Function.onFun, Finset.disjoint_left]
  intro w hwp hwq
  exact Set.disjoint_left.mp (ht.disjoint_wordIval hp hq hpq hwp hwq)
    (wordPos_mem_wordIval hθ w) (wordPos_mem_wordIval hθ w)

/-- The members of the selected families form a prefix-free family. -/
theorem prefixFree (hθ : θ ∈ Icc 0 (π / 2)) (ht : IsSelection N θ K t) :
    PrefixFree (t.biUnion Prod.snd) := by
  intro u hu w hw huw
  obtain ⟨p, hp, hup⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨q, hq, hwq⟩ := Finset.mem_biUnion.mp hw
  by_cases hpq : p = q
  · subst hpq
    have hS := (mem_witnessIndex.mp (ht.1 hp)).2.1
    exact huw.eq_of_length ((mem_words.mp (hS hup)).trans (mem_words.mp (hS hwq)).symm)
  · exact absurd huw (not_prefix_of_disjoint hθ (ht.disjoint_wordIval hp hq hpq hup hwq))

/-- The number of terminal words: `#W = ⌈K⌉₊ ∑_{(w₀, S)} 4^{N - |w₀|}`. -/
theorem card_terminal (hθ : θ ∈ Icc 0 (π / 2)) (ht : IsSelection N θ K t) :
    #((t.biUnion Prod.snd).biUnion (desc · N)) = ∑ p ∈ t, ⌈K⌉₊ * 4 ^ (N - p.1.length) := by
  have hmem : ∀ p ∈ t, p.1.length ≤ N ∧ p.2 ⊆ words p.1.length ∧ #p.2 = ⌈K⌉₊ := fun p hp =>
    let h := mem_witnessIndex.mp (ht.1 hp)
    ⟨h.1, h.2.1, h.2.2.1⟩
  have hM : ∀ s ∈ t.biUnion Prod.snd, s.length ≤ N := by
    intro s hs
    obtain ⟨p, hp, hsp⟩ := Finset.mem_biUnion.mp hs
    rw [mem_words.mp ((hmem p hp).2.1 hsp)]
    exact (hmem p hp).1
  rw [(ht.prefixFree hθ).card_biUnion_desc hM, Finset.sum_biUnion (ht.pairwiseDisjoint_snd hθ)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_congr rfl fun s hs => by rw [mem_words.mp ((hmem p hp).2.1 hs)],
    Finset.sum_const, (hmem p hp).2.2, smul_eq_mul]

end IsSelection

/-! ### Terminal words -/

/-- A family `W` of words is *witnessed* at depth `N` with threshold `K` if each member descends
from a member of a family `S` of at least `K` words of a common length `n ≤ N`, whose
projections share a point and all of whose depth-`N` descendants belong to `W`. -/
def IsWitnessed (θ : ℝ) (N : ℕ) (K : ℝ) (W : Finset Word) : Prop :=
  ∀ w ∈ W, ∃ n ≤ N, ∃ S ⊆ words n, K ≤ #S ∧ (∃ y, ∀ s ∈ S, y ∈ wordIval θ s) ∧
    (∃ s ∈ S, s <+: w) ∧ ∀ s ∈ S, desc s N ⊆ W

theorem IsSelection.isWitnessed {N : ℕ} {K : ℝ} {t : Finset (Word × Finset Word)}
    (ht : IsSelection N θ K t) :
    IsWitnessed θ N K ((t.biUnion Prod.snd).biUnion (desc · N)) := by
  intro w hw
  obtain ⟨s, hsP, hws⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨p, hp, hsp⟩ := Finset.mem_biUnion.mp hsP
  obtain ⟨hl, hS, hcard, -, y, hy⟩ := mem_witnessIndex.mp (ht.1 hp)
  refine ⟨p.1.length, hl, p.2, hS, ?_, ⟨y, hy⟩, ⟨s, hsp, (mem_desc.mp hws).2⟩, fun s' hs' => ?_⟩
  · rw [hcard]
    exact Nat.le_ceil K
  · exact Finset.subset_biUnion_of_mem (desc · N) (Finset.mem_biUnion.mpr ⟨p, hp, hs'⟩)

/-- **Terminal selection (G13)–(G15).** There is a witnessed family `W` of depth-`N` words with
`μ_N(K) ≤ 9 σ #W / (4^N K)`. -/
theorem exists_witnessed_terminal (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ W ⊆ words N, IsWitnessed θ N K W ∧
      volume (superLevel N θ K) ≤ ENNReal.ofReal (9 * sig θ * #W / (4 ^ N * K)) := by
  obtain ⟨t, ht, hvol⟩ := exists_isSelection hθ N hK
  refine ⟨(t.biUnion Prod.snd).biUnion (desc · N), Finset.biUnion_subset.mpr fun s _ =>
    desc_subset_words s N, ht.isWitnessed, hvol.trans ?_⟩
  have hσ := sig_nonneg hθ
  have hlen : ∀ p ∈ t, p.1.length ≤ N := fun p hp => (mem_witnessIndex.mp (ht.1 hp)).1
  calc 3 * ∑ p ∈ t, volume (tripleIval θ p.1)
      = ENNReal.ofReal (∑ p ∈ t, 9 * (sig θ / 4 ^ p.1.length)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun p _ => by positivity, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [volume_tripleIval, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (9 * sig θ * #((t.biUnion Prod.snd).biUnion (desc · N)) /
          (4 ^ N * K)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [ht.card_terminal hθ, Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_le_sum fun p hp => ?_
        have hceil : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
        have e : 9 * sig θ * ((⌈K⌉₊ * 4 ^ (N - p.1.length) : ℕ) : ℝ) / (4 ^ N * K) =
            9 * (sig θ / 4 ^ p.1.length) * (⌈K⌉₊ / K) := by
          push_cast
          rw [pow_sub₀ _ (by norm_num : (4 : ℝ) ≠ 0) (hlen p hp)]
          field_simp
        rw [e]
        refine le_mul_of_one_le_right (by positivity) ?_
        rwa [one_le_div hK]

end Favard.Comb
