import FavardLength.Combinatorics.Counting

/-!
# First crossings, marked squares, and the retained family

Manuscript section "The packing construction". Fix `N`, `θ ∈ [0, π/2]` and a threshold `K ≥ 2`.
At a point `x` with `F_N(x) ≥ 2K`, the first crossing generation `m(x)` is the least `n ≤ N` with
`f_n(x) ≥ 2K` (`FirstCross N θ K x n`). A word is *marked* if its length is `m(x)` for some point
`x` of its projected interval; the *retained* family `𝓡 = retained N θ K` consists of the marked
words having no marked proper prefix. We prove:

* existence and uniqueness of the first crossing, `1 ≤ m(x)`, and the bound (G6)
  `2K ≤ f_{m(x)}(x) < 8K`;
* if `f_n(x) ≥ 8K` for some `n ≤ N` then `m(x) < n`;
* `𝓡` is prefix-free and every marked word has a unique retained prefix.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ}

/-- `x` first reaches height `2K` at generation `n ≤ N`: `f_n(x) ≥ 2K` while `f_m(x) < 2K` for
every `m < n`. -/
def FirstCross (N : ℕ) (θ K x : ℝ) (n : ℕ) : Prop :=
  n ≤ N ∧ 2 * K ≤ (count n θ x : ℝ) ∧ ∀ m < n, (count m θ x : ℝ) < 2 * K

/-- A first crossing exists as soon as `F_N(x) ≥ 2K`. -/
theorem exists_firstCross {N : ℕ} {K x : ℝ} (h : x ∈ superLevel N θ (2 * K)) :
    ∃ n, FirstCross N θ K x n := by
  classical
  have hex : ∃ n, n ≤ N ∧ 2 * K ≤ (count n θ x : ℝ) := mem_superLevel_iff_exists.mp h
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun m hm => ?_⟩
  have := Nat.find_min hex hm
  push Not at this
  exact this (hm.le.trans (Nat.find_spec hex).1)

/-- The first crossing is at most any crossing generation. -/
theorem FirstCross.le_of_le_count {N n m : ℕ} {K x : ℝ} (h : FirstCross N θ K x n)
    (hc : 2 * K ≤ (count m θ x : ℝ)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  exact absurd hc (not_le.mpr (h.2.2 m hlt))

theorem FirstCross.unique {N n n' : ℕ} {K x : ℝ} (h : FirstCross N θ K x n)
    (h' : FirstCross N θ K x n') : n = n' :=
  le_antisymm (h.le_of_le_count h'.2.1) (h'.le_of_le_count h.2.1)

theorem FirstCross.mem_superLevel {N n : ℕ} {K x : ℝ} (h : FirstCross N θ K x n) :
    x ∈ superLevel N θ (2 * K) :=
  mem_superLevel_iff_exists.mpr ⟨n, h.1, h.2.1⟩

/-- The first crossing is not the root generation (`f_0 ≤ 1 < 2K`). -/
theorem FirstCross.one_le (hθ : θ ∈ Icc 0 (π / 2)) {N n : ℕ} {K x : ℝ} (hK : 1 < 2 * K)
    (h : FirstCross N θ K x n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (count 0 θ x : ℝ) ≤ 1 := by exact_mod_cast count_zero_le_one hθ x
    linarith [h.2.1]
  · exact hn

/-- **First-crossing bound (G6)**: `f_{m(x)}(x) < 8K`. -/
theorem FirstCross.count_lt (hθ : θ ∈ Icc 0 (π / 2)) {N n : ℕ} {K x : ℝ} (hK : 1 < 2 * K)
    (h : FirstCross N θ K x n) : (count n θ x : ℝ) < 8 * K := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.one_le hθ hK; omega⟩
  have h1 : (count (m + 1) θ x : ℝ) ≤ 4 * count m θ x := by
    exact_mod_cast count_succ_le hθ m x
  have h2 := h.2.2 m (Nat.lt_succ_self m)
  linarith

/-- If `f_n(x) ≥ 8K` at some generation `n`, the first crossing happens strictly before `n`. -/
theorem FirstCross.lt_of_le_count (hθ : θ ∈ Icc 0 (π / 2)) {N n m : ℕ} {K x : ℝ}
    (hK : 1 < 2 * K) (h : FirstCross N θ K x m) (hc : 8 * K ≤ (count n θ x : ℝ)) : m < n := by
  have hK0 : 0 < K := by linarith
  have hle : m ≤ n := h.le_of_le_count (by linarith)
  refine lt_of_le_of_ne hle fun hmn => ?_
  subst hmn
  linarith [h.count_lt hθ hK]

/-! ### Marked and retained words -/

open Classical in
/-- The marked words: a word `w` of length at most `N` is marked if some point `x` of its
projected interval has first crossing generation `|w|`. -/
noncomputable def marked (N : ℕ) (θ K : ℝ) : Finset Word :=
  (wordsLE N).filter fun w => ∃ x ∈ wordIval θ w, FirstCross N θ K x w.length

open Classical in
/-- The retained family `𝓡`: marked words without a marked proper prefix. -/
noncomputable def retained (N : ℕ) (θ K : ℝ) : Finset Word :=
  (marked N θ K).filter fun w => ∀ v ∈ marked N θ K, v <+: w → v = w

theorem mem_marked {N : ℕ} {K : ℝ} {w : Word} :
    w ∈ marked N θ K ↔ ∃ x ∈ wordIval θ w, FirstCross N θ K x w.length := by
  classical
  unfold marked
  rw [Finset.mem_filter, mem_wordsLE]
  constructor
  · exact fun h => h.2
  · rintro ⟨x, hx, h⟩
    exact ⟨h.1, x, hx, h⟩

theorem mem_marked_of_firstCross {N : ℕ} {K x : ℝ} {w : Word}
    (h : FirstCross N θ K x w.length) (hx : x ∈ wordIval θ w) : w ∈ marked N θ K :=
  mem_marked.mpr ⟨x, hx, h⟩

theorem length_le_of_mem_marked {N : ℕ} {K : ℝ} {w : Word} (hw : w ∈ marked N θ K) :
    w.length ≤ N := by
  obtain ⟨x, -, h⟩ := mem_marked.mp hw
  exact h.1

theorem one_le_length_of_mem_marked (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {K : ℝ} (hK : 1 < 2 * K)
    {w : Word} (hw : w ∈ marked N θ K) : 1 ≤ w.length := by
  obtain ⟨x, -, h⟩ := mem_marked.mp hw
  exact h.one_le hθ hK

theorem mem_retained {N : ℕ} {K : ℝ} {w : Word} :
    w ∈ retained N θ K ↔ w ∈ marked N θ K ∧ ∀ v ∈ marked N θ K, v <+: w → v = w := by
  classical
  unfold retained
  rw [Finset.mem_filter]

theorem retained_subset_marked (N : ℕ) (θ K : ℝ) : retained N θ K ⊆ marked N θ K := by
  classical
  exact Finset.filter_subset _ _

/-- The retained family is prefix-free. -/
theorem prefixFree_retained (N : ℕ) (θ K : ℝ) : PrefixFree (retained N θ K) := by
  intro u hu w hw huw
  exact (mem_retained.mp hw).2 u (retained_subset_marked N θ K hu) huw

/-- Every marked word has a retained prefix. -/
theorem exists_retained_prefix {N : ℕ} {K : ℝ} {w : Word} (hw : w ∈ marked N θ K) :
    ∃ r ∈ retained N θ K, r <+: w := by
  classical
  set P := (marked N θ K).filter (· <+: w)
  have hP : P.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hw, List.prefix_refl w⟩⟩
  obtain ⟨r, hrP, hmin⟩ := Finset.exists_min_image P List.length hP
  obtain ⟨hr, hrw⟩ := Finset.mem_filter.mp hrP
  refine ⟨r, mem_retained.mpr ⟨hr, fun v hv hvr => ?_⟩, hrw⟩
  have hvP : v ∈ P := Finset.mem_filter.mpr ⟨hv, hvr.trans hrw⟩
  exact hvr.eq_of_length (le_antisymm hvr.length_le (hmin v hvP))

/-- The retained prefix of a word is unique. -/
theorem retained_prefix_unique {N : ℕ} {K : ℝ} {r r' w : Word} (hr : r ∈ retained N θ K)
    (hr' : r' ∈ retained N θ K) (hrw : r <+: w) (hr'w : r' <+: w) : r = r' :=
  (prefixFree_retained N θ K).eq_of_prefix hr hr' hrw hr'w

theorem one_le_length_of_mem_retained (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {K : ℝ}
    (hK : 1 < 2 * K) {w : Word} (hw : w ∈ retained N θ K) : 1 ≤ w.length :=
  one_le_length_of_mem_marked hθ hK (retained_subset_marked N θ K hw)

theorem length_le_of_mem_retained {N : ℕ} {K : ℝ} {w : Word} (hw : w ∈ retained N θ K) :
    w.length ≤ N :=
  length_le_of_mem_marked (retained_subset_marked N θ K hw)

/-- If `x` has first crossing `m` and lies in the projection of a word `v` with `m ≤ |v|`, then
the length-`m` prefix of `v` is marked, so `v` lies below a retained word of length at most `m`.
This is the form used in (G8) and (G11). -/
theorem exists_retained_prefix_of_firstCross (hθ : θ ∈ Icc 0 (π / 2)) {N m : ℕ} {K x : ℝ}
    (h : FirstCross N θ K x m) {v : Word} (hmv : m ≤ v.length) (hx : x ∈ wordIval θ v) :
    ∃ r ∈ retained N θ K, r <+: v ∧ r.length ≤ m := by
  have hm : (v.take m).length = m := by simp [hmv]
  have hxm : x ∈ wordIval θ (v.take m) := wordIval_subset_of_prefix hθ (List.take_prefix _ _) hx
  have hmarked : v.take m ∈ marked N θ K := by
    refine mem_marked_of_firstCross ?_ hxm
    rw [hm]
    exact h
  obtain ⟨r, hr, hrv⟩ := exists_retained_prefix hmarked
  exact ⟨r, hr, hrv.trans (List.take_prefix _ _), hm ▸ hrv.length_le⟩

end Favard.Comb
