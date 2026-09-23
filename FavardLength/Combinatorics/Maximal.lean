import FavardLength.Combinatorics.Counting
import FavardLength.Combinatorics.Covering

/-!
# Maximal-function estimates for counting functions

The manuscript bounds superlevel sets through the centered maximal function (G2) and the
domination `F_N ≤ 2 𝓜 f_N` (G4). We use a finite, uncentred version that avoids the maximal
function: a point lying in the projection of a member of a *heavy family* (at least `c` words of a
common depth whose projections share a point, and all of whose depth-`M` descendants belong to
`T`) lies in the concentric triple of that member's interval, on which the counting function of
`T` has mean at least `c/3` (descendant mass lemma). The finite Vitali lemma then gives
`|X| ≤ 9 σ #T / (4^M c)` (`volume_le_of_forall_heavy`). Special cases:

* (G5) `μ_N(t) ≤ 9σ/t` (`volume_superLevel_le_div`), with `T` all words of length `N`;
* (G17) the green projected union has length at most `9σ/K`, with `T` the green words.

We also record the half-interval lemma used in (G9): if `f_k(x) ≥ 2K` (`k ≤ N`) then an interval
of length `σ 4^{-k}/2` with endpoint `x` lies in `{F_N ≥ K}`.
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard.Comb

variable {θ : ℝ}

theorem tripleIval_eq_tripleIcc (θ : ℝ) (w : Word) :
    tripleIval θ w = tripleIcc (wordPos θ w) (wordPos θ w + sig θ / 4 ^ w.length) := by
  rw [tripleIval, tripleIcc]
  congr 1 <;> ring

/-- A family `S` of depth-`n` words is *heavy* for `x` (with threshold `c`, target family `T` of
depth-`M` words) if it has at least `c` members, their projections share a point, `x` lies in
the projection of one of them, and all depth-`M` descendants of its members belong to `T`. -/
def IsHeavy (θ : ℝ) (T : Finset Word) (M : ℕ) (c x : ℝ) (n : ℕ) (S : Finset Word) : Prop :=
  n ≤ M ∧ S ⊆ words n ∧ c ≤ #S ∧ (∃ y, ∀ w ∈ S, y ∈ wordIval θ w) ∧
    (∃ w ∈ S, x ∈ wordIval θ w) ∧ ∀ w ∈ S, desc w M ⊆ T

/-- The mean of `wcount θ T` over the triple of a member of a heavy family is at least `c/3`. -/
theorem IsHeavy.mean_ge (hθ : θ ∈ Icc 0 (π / 2)) {T : Finset Word} {M n : ℕ} {c x : ℝ}
    {S : Finset Word} (h : IsHeavy θ T M c x n S) :
    ∃ w₀ ∈ S, x ∈ tripleIval θ w₀ ∧
      ENNReal.ofReal (c / 3) * volume (tripleIval θ w₀) ≤
        ∫⁻ z in tripleIval θ w₀, (wcount θ T z : ℝ≥0∞) := by
  obtain ⟨hnM, hS, hc, ⟨y, hy⟩, ⟨w₀, hw₀, hx⟩, hdesc⟩ := h
  refine ⟨w₀, hw₀, wordIval_subset_tripleIval_self hθ w₀ hx, ?_⟩
  have hl₀ : w₀.length = n := mem_words.mp (hS hw₀)
  have hsub : ∀ w ∈ S, wordIval θ w ⊆ tripleIval θ w₀ := fun w hw =>
    wordIval_subset_tripleIval ((mem_words.mp (hS hw)).trans hl₀.symm) (hy w hw) (hy w₀ hw₀)
  refine le_trans ?_ (card_mul_le_setLIntegral_wcount hθ hnM hS hdesc hsub)
  have hℓ : 0 ≤ sig θ / 4 ^ n := div_nonneg (sig_nonneg hθ) (by positivity)
  rcases lt_or_ge c 0 with hc0 | hc0
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
    exact zero_le
  rw [volume_tripleIval, hl₀, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc c / 3 * (3 * (sig θ / 4 ^ n)) = c * (sig θ / 4 ^ n) := by ring
    _ ≤ #S * (sig θ / 4 ^ n) := mul_le_mul_of_nonneg_right hc hℓ

/-- **Maximal-function estimate (G2 + G4).** If every point of `X` is covered by a heavy family
with threshold `c > 0` for the target `T ⊆ words M`, then `|X| ≤ 9 σ #T / (4^M c)`. -/
theorem volume_le_of_forall_heavy (hθ : θ ∈ Icc 0 (π / 2)) {M : ℕ} {T : Finset Word}
    (hT : T ⊆ words M) {X : Set ℝ} {c : ℝ} (hc : 0 < c)
    (hX : ∀ x ∈ X, ∃ n S, IsHeavy θ T M c x n S) :
    volume X ≤ ENNReal.ofReal (9 * sig θ * #T / (4 ^ M * c)) := by
  classical
  set G := (wordsLE M).filter fun w => ENNReal.ofReal (c / 3) * volume (tripleIval θ w) ≤
    ∫⁻ z in tripleIval θ w, (wcount θ T z : ℝ≥0∞) with hG
  have hXG : X ⊆ ⋃ w ∈ G, tripleIval θ w := by
    intro x hx
    obtain ⟨n, S, hS⟩ := hX x hx
    obtain ⟨w₀, hw₀, hxw₀, hmean⟩ := hS.mean_ge hθ
    refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨?_, hmean⟩) hxw₀
    rw [mem_wordsLE, mem_words.mp (hS.2.1 hw₀)]
    exact hS.1
  have hweak := mul_volume_biUnion_le_lintegral G
    (fun w => wordPos θ w - sig θ / 4 ^ w.length)
    (fun w => wordPos θ w + 2 * (sig θ / 4 ^ w.length))
    (fun z => (wcount θ T z : ℝ≥0∞)) (ENNReal.ofReal (c / 3))
    (fun w hw => (Finset.mem_filter.mp hw).2)
  have hmass : ∫⁻ z, (wcount θ T z : ℝ≥0∞) = ENNReal.ofReal (#T * (sig θ / 4 ^ M)) := by
    rw [lintegral_wcount, Finset.sum_congr rfl fun w hw => by rw [mem_words.mp (hT hw)],
      Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hc3 : 0 < c / 3 := by positivity
  calc volume X ≤ volume (⋃ w ∈ G, tripleIval θ w) := measure_mono hXG
    _ ≤ 3 * ENNReal.ofReal (#T * (sig θ / 4 ^ M)) / ENNReal.ofReal (c / 3) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc3)) (Or.inl ENNReal.ofReal_ne_top),
          mul_comm, ← hmass]
        exact hweak
    _ = ENNReal.ofReal (9 * sig θ * #T / (4 ^ M * c)) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_div_of_pos hc3]
        congr 1
        field_simp
        ring

/-- **Distribution bound (G5)**: `μ_N(t) ≤ 9σ/t` for `t > 0`. -/
theorem volume_superLevel_le_div (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    volume (superLevel N θ t) ≤ ENNReal.ofReal (9 * sig θ / t) := by
  classical
  have h := volume_le_of_forall_heavy hθ (T := words N) (fun _ h => h) ht (X := superLevel N θ t)
    (fun x hx => by
      obtain ⟨n, hn, hcount⟩ := mem_superLevel_iff_exists.mp hx
      set S := (words n).filter fun w => x ∈ wordIval θ w
      have hS : (#S : ℝ) = count n θ x := by
        rw [count_eq_wcount hθ]
        rfl
      have hSpos : S.Nonempty := by
        rw [← Finset.card_pos]
        have : (0 : ℝ) < #S := by rw [hS]; linarith
        exact_mod_cast this
      obtain ⟨w₀, hw₀⟩ := hSpos
      refine ⟨n, S, hn, Finset.filter_subset _ _, by rw [hS]; exact hcount,
        ⟨x, fun w hw => (Finset.mem_filter.mp hw).2⟩, ⟨w₀, hw₀, (Finset.mem_filter.mp hw₀).2⟩,
        fun w hw => ?_⟩
      intro v hv
      exact desc_subset_words w N hv)
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [card_words]
  push_cast
  field_simp

/-- **Witness families (G13)**: a point of `{F_N ≥ K}` lies in the projections of `⌈K⌉` words of
a common length `n ≤ N`. -/
theorem exists_witness_family (hθ : θ ∈ Icc 0 (π / 2)) {N : ℕ} {K x : ℝ}
    (hx : x ∈ superLevel N θ K) :
    ∃ n ≤ N, ∃ S ⊆ words n, #S = ⌈K⌉₊ ∧ ∀ w ∈ S, x ∈ wordIval θ w := by
  classical
  obtain ⟨n, hn, hcount⟩ := mem_superLevel_iff_exists.mp hx
  set Sx := (words n).filter fun w => x ∈ wordIval θ w
  have hSx : #Sx = count n θ x := by
    rw [count_eq_wcount hθ]
    rfl
  have hle : ⌈K⌉₊ ≤ #Sx := by
    rw [hSx]
    exact Nat.ceil_le.mpr hcount
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hle
  exact ⟨n, hn, S, hS.trans (Finset.filter_subset _ _), hcard,
    fun w hw => (Finset.mem_filter.mp (hS hw)).2⟩

/-- **Half-interval lemma (used in G9).** If `f_k(x) ≥ 2K` with `k ≤ N`, then some interval of
length `σ 4^{-k}/2` having `x` as an endpoint lies in the superlevel set `{F_N ≥ K}`. -/
theorem exists_Icc_subset_superLevel (hθ : θ ∈ Icc 0 (π / 2)) {N k : ℕ} (hk : k ≤ N)
    {K x : ℝ} (hx : 2 * K ≤ (count k θ x : ℝ)) :
    ∃ a, (a = x ∨ a + sig θ / 4 ^ k / 2 = x) ∧
      Icc a (a + sig θ / 4 ^ k / 2) ⊆ superLevel N θ K := by
  classical
  set ℓ := sig θ / 4 ^ k with hℓ
  set S := (words k).filter fun w => x ∈ wordIval θ w
  set SR := S.filter fun w => x ≤ wordPos θ w + ℓ / 2
  set SL := S.filter fun w => ¬x ≤ wordPos θ w + ℓ / 2
  have hS : (#S : ℝ) = count k θ x := by
    rw [count_eq_wcount hθ]
    rfl
  have hsplit : #SR + #SL = #S := Finset.card_filter_add_card_filter_not _
  have hwl : ∀ w ∈ S, w.length = k := fun w hw => mem_words.mp (Finset.mem_filter.mp hw).1
  -- a family of depth-`k` words all containing every point of an interval gives `F_N ≥ K` there
  have key : ∀ T ⊆ S, K ≤ (#T : ℝ) → ∀ y, (∀ w ∈ T, y ∈ wordIval θ w) →
      y ∈ superLevel N θ K := by
    intro T hT hK y hy
    rw [mem_superLevel]
    have h1 := card_le_count hθ (hT.trans (Finset.filter_subset _ _)) hy
    have h2 := count_le_maxCount hk θ y
    calc K ≤ #T := hK
      _ ≤ maxCount N θ y := by exact_mod_cast h1.trans h2
  have hsum : 2 * K ≤ (#SR : ℝ) + #SL := by
    have : (#S : ℝ) = #SR + #SL := by rw [← hsplit]; push_cast; ring
    linarith
  by_cases hR : K ≤ (#SR : ℝ)
  · refine ⟨x, Or.inl rfl, fun y hy => key SR (Finset.filter_subset _ _) hR y fun w hw => ?_⟩
    obtain ⟨hwS, hwR⟩ := Finset.mem_filter.mp hw
    have hxw := (Finset.mem_filter.mp hwS).2
    rw [wordIval, hwl w hwS] at hxw ⊢
    exact ⟨hxw.1.trans hy.1, by linarith [hy.2]⟩
  · push Not at hR
    have hL : K ≤ (#SL : ℝ) := by linarith
    refine ⟨x - ℓ / 2, Or.inr (by ring), fun y hy => key SL (Finset.filter_subset _ _) hL y
      fun w hw => ?_⟩
    obtain ⟨hwS, hwL⟩ := Finset.mem_filter.mp hw
    have hxw := (Finset.mem_filter.mp hwS).2
    rw [wordIval, hwl w hwS] at hxw ⊢
    push Not at hwL
    exact ⟨by linarith [hy.1], by linarith [hy.2, hxw.2]⟩

end Favard.Comb
