import FavardLength.Combinatorics.Position
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Counting functions of projected squares

For a finite family `S` of words, `wcount θ S x` is the number of members whose projected
interval contains `x`; `count n θ x = wcount θ (words n) x` for `θ ∈ [0, π/2]`. This file proves

* measurability and the mass identity `∫⁻ wcount θ S = ∑_{w ∈ S} σ 4^{-|w|}`;
* the **descendant mass lemma**: if the projections of a family `S` of depth-`n` words lie in `E`
  and all depth-`M` descendants of `S` belong to `T`, then `∫⁻_E wcount θ T ≥ #S σ 4^{-n}`
  (the mechanism behind (G4) and (G17));
* the parent bound (G3): `count n θ x ≤ 4^{n-m} count m θ x` for `m ≤ n`;
* the running maximum `maxCount N θ x = F_N(x) = max_{n ≤ N} f_n(x)` (root included), its
  superlevel sets `superLevel N θ K = {F_N ≥ K}`, their finiteness, and the integrability of
  `F_N²`, with `energy r θ ≤ ∫ F_N²` for `r ≤ N`.
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard.Comb

variable {θ : ℝ}

/-! ### The counting function of a finite family -/

theorem wcount_eq_sum_indicator {R : Type*} [AddCommMonoidWithOne R] (θ : ℝ) (S : Finset Word)
    (x : ℝ) : (wcount θ S x : R) = ∑ w ∈ S, (wordIval θ w).indicator 1 x := by
  classical
  rw [wcount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : x ∈ wordIval θ w <;> simp [h]

theorem wcount_le_card (θ : ℝ) (S : Finset Word) (x : ℝ) : wcount θ S x ≤ #S := by
  classical
  exact Finset.card_filter_le _ _

theorem wcount_mono {S T : Finset Word} (h : S ⊆ T) (x : ℝ) : wcount θ S x ≤ wcount θ T x := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem wcount_empty (θ x : ℝ) : wcount θ ∅ x = 0 := by
  simp [wcount]

theorem wcount_eq_zero_of_notMem {S : Finset Word} {x : ℝ} (h : ∀ w ∈ S, x ∉ wordIval θ w) :
    wcount θ S x = 0 := by
  classical
  rw [wcount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact h

/-- A point with positive count lies in the projection of some member. -/
theorem exists_mem_of_wcount_pos {S : Finset Word} {x : ℝ} (h : 0 < wcount θ S x) :
    ∃ w ∈ S, x ∈ wordIval θ w := by
  classical
  by_contra h'
  push Not at h'
  rw [wcount_eq_zero_of_notMem h'] at h
  exact lt_irrefl _ h

theorem wcount_biUnion {ι : Type*} {P : Finset ι} {f : ι → Finset Word}
    (hP : (P : Set ι).PairwiseDisjoint f) (x : ℝ) :
    wcount θ (P.biUnion f) x = ∑ i ∈ P, wcount θ (f i) x := by
  classical
  unfold wcount
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi j hj hij
  exact Finset.disjoint_filter_filter (hP hi hj hij)

theorem measurable_wcount (θ : ℝ) (S : Finset Word) : Measurable (wcount θ S) := by
  have : wcount θ S = fun x => ∑ w ∈ S, (wordIval θ w).indicator (1 : ℝ → ℕ) x := by
    ext x
    exact_mod_cast wcount_eq_sum_indicator (R := ℕ) θ S x
  rw [this]
  exact Finset.measurable_sum _ fun w _ => measurable_const.indicator (measurableSet_wordIval θ w)

theorem measurable_wcount_real (θ : ℝ) (S : Finset Word) :
    Measurable fun x => (wcount θ S x : ℝ) :=
  measurable_from_nat.comp (measurable_wcount θ S)

theorem measurable_wcount_ennreal (θ : ℝ) (S : Finset Word) :
    Measurable fun x => (wcount θ S x : ℝ≥0∞) :=
  measurable_from_nat.comp (measurable_wcount θ S)

/-- The mass identity `∫⁻ wcount θ S = ∑_{w ∈ S} σ 4^{-|w|}`. -/
theorem lintegral_wcount (θ : ℝ) (S : Finset Word) :
    ∫⁻ x, (wcount θ S x : ℝ≥0∞) = ∑ w ∈ S, ENNReal.ofReal (sig θ / 4 ^ w.length) := by
  simp_rw [wcount_eq_sum_indicator (R := ℝ≥0∞)]
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [lintegral_indicator_one (measurableSet_wordIval θ w), volume_wordIval]
  · exact fun w _ => measurable_const.indicator (measurableSet_wordIval θ w)

/-- The mass identity on a set `E` containing all the projections of the family. -/
theorem setLIntegral_wcount_of_subset (θ : ℝ) {S : Finset Word} {E : Set ℝ}
    (hE : ∀ w ∈ S, wordIval θ w ⊆ E) :
    ∫⁻ x in E, (wcount θ S x : ℝ≥0∞) = ∑ w ∈ S, ENNReal.ofReal (sig θ / 4 ^ w.length) := by
  simp_rw [wcount_eq_sum_indicator (R := ℝ≥0∞)]
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [lintegral_indicator_one (measurableSet_wordIval θ w),
      Measure.restrict_apply (measurableSet_wordIval θ w), inter_eq_left.mpr (hE w hw),
      volume_wordIval]
  · exact fun w _ => measurable_const.indicator (measurableSet_wordIval θ w)

/-- The total multiplicity mass of generation `M` is `σ`. -/
theorem lintegral_wcount_words (θ : ℝ) (M : ℕ) :
    ∫⁻ x, (wcount θ (words M) x : ℝ≥0∞) = ENNReal.ofReal (sig θ) := by
  rw [lintegral_wcount]
  rw [Finset.sum_congr rfl fun w hw => by rw [mem_words.mp hw], Finset.sum_const, card_words,
    nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  field_simp

/-- The union of the projections of a family of depth-`M` words has length at most
`#T σ 4^{-M}`. -/
theorem volume_biUnion_wordIval_le (θ : ℝ) {M : ℕ} {T : Finset Word} (hT : T ⊆ words M) :
    volume (⋃ w ∈ T, wordIval θ w) ≤ ENNReal.ofReal (#T * (sig θ / 4 ^ M)) := by
  refine (measure_biUnion_finset_le T _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun w hw => by rw [volume_wordIval, mem_words.mp (hT hw)],
    Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- A family of words of a common length is prefix-free. -/
theorem prefixFree_of_subset_words {S : Finset Word} {n : ℕ} (hS : S ⊆ words n) :
    PrefixFree S := fun _ hu _ hw huw =>
  huw.eq_of_length ((mem_words.mp (hS hu)).trans (mem_words.mp (hS hw)).symm)

/-- **Descendant mass lemma.** Let `S` be a family of depth-`n` words whose projections lie in
`E`, and let `T` contain all depth-`M` descendants of `S` (`n ≤ M`). Then the counting function
of `T` has mass at least `#S σ 4^{-n}` on `E`. -/
theorem card_mul_le_setLIntegral_wcount (hθ : θ ∈ Icc 0 (π / 2)) {n M : ℕ} (hnM : n ≤ M)
    {S T : Finset Word} (hS : S ⊆ words n) (hST : ∀ w ∈ S, desc w M ⊆ T) {E : Set ℝ}
    (hE : ∀ w ∈ S, wordIval θ w ⊆ E) :
    ENNReal.ofReal (#S * (sig θ / 4 ^ n)) ≤ ∫⁻ x in E, (wcount θ T x : ℝ≥0∞) := by
  classical
  set D := S.biUnion (desc · M) with hD
  have hDT : D ⊆ T := Finset.biUnion_subset.mpr hST
  have hDE : ∀ v ∈ D, wordIval θ v ⊆ E := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
    exact (wordIval_subset_of_prefix hθ (mem_desc.mp hvw).2).trans (hE w hw)
  have hSl : ∀ w ∈ S, w.length ≤ M := fun w hw => (mem_words.mp (hS hw)).trans_le hnM
  have hcard : #D = #S * 4 ^ (M - n) := by
    rw [hD, (prefixFree_of_subset_words hS).card_biUnion_desc hSl,
      Finset.sum_congr rfl fun w hw => by rw [mem_words.mp (hS hw)], Finset.sum_const,
      smul_eq_mul]
  calc ENNReal.ofReal (#S * (sig θ / 4 ^ n))
      = ∑ v ∈ D, ENNReal.ofReal (sig θ / 4 ^ v.length) := by
        rw [Finset.sum_congr rfl fun v hv => by
          rw [(mem_desc.mp (Finset.mem_biUnion.mp hv).choose_spec.2).1], Finset.sum_const,
          nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hcard]
        congr 1
        push_cast
        rw [pow_sub₀ _ (by norm_num : (4 : ℝ) ≠ 0) hnM]
        field_simp
    _ = ∫⁻ x in E, (wcount θ D x : ℝ≥0∞) := (setLIntegral_wcount_of_subset θ hDE).symm
    _ ≤ ∫⁻ x in E, (wcount θ T x : ℝ≥0∞) :=
        lintegral_mono fun x => Nat.cast_le.mpr (wcount_mono hDT x)

/-! ### The multiplicity `count` -/

theorem count_le_card_words (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) (x : ℝ) :
    count n θ x ≤ 4 ^ n := by
  rw [count_eq_wcount hθ, ← card_words n]
  exact wcount_le_card θ _ x

theorem count_zero_le_one (hθ : θ ∈ Icc 0 (π / 2)) (x : ℝ) : count 0 θ x ≤ 1 := by
  simpa using count_le_card_words hθ 0 x

theorem measurable_count' (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    Measurable fun x => count n θ x := by
  simp_rw [count_eq_wcount hθ]
  exact measurable_wcount θ _

/-- **Parent bound (G3)**, iterated: `f_n ≤ 4^{n-m} f_m` for `m ≤ n`. -/
theorem count_le_pow_mul_count (hθ : θ ∈ Icc 0 (π / 2)) {m n : ℕ} (h : m ≤ n) (x : ℝ) :
    count n θ x ≤ 4 ^ (n - m) * count m θ x := by
  classical
  rw [count_eq_wcount hθ, count_eq_wcount hθ]
  unfold wcount
  set Sn := (words n).filter fun w => x ∈ wordIval θ w
  set Sm := (words m).filter fun w => x ∈ wordIval θ w
  have himage : Sn.image (List.take m) ⊆ Sm := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨take_mem_words hw.1 h, wordIval_subset_of_prefix hθ (List.take_prefix _ _) hw.2⟩
  calc #Sn ≤ 4 ^ (n - m) * #(Sn.image (List.take m)) := by
        refine Finset.card_le_mul_card_image _ _ fun u hu => ?_
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        have hwn := mem_words.mp (Finset.mem_filter.mp hw).1
        have hlen : (w.take m).length = m := by simp [hwn, h]
        have hsub : Sn.filter (fun v => v.take m = w.take m) ⊆ desc (w.take m) n := by
          intro v hv
          rw [Finset.mem_filter] at hv
          rw [mem_desc]
          refine ⟨mem_words.mp (Finset.mem_filter.mp hv.1).1, ?_⟩
          rw [← hv.2]
          exact List.take_prefix _ _
        calc _ ≤ #(desc (w.take m) n) := Finset.card_le_card hsub
          _ = 4 ^ (n - m) := by rw [card_desc (by rw [hlen]; exact h), hlen]
    _ ≤ 4 ^ (n - m) * #Sm := Nat.mul_le_mul_left _ (Finset.card_le_card himage)

/-- **Parent bound (G3)**: `f_{n+1} ≤ 4 f_n`. -/
theorem count_succ_le (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) (x : ℝ) :
    count (n + 1) θ x ≤ 4 * count n θ x := by
  simpa using count_le_pow_mul_count hθ (Nat.le_succ n) x

/-- A point in the projection of a word of length `n` has positive depth-`n` count; more
generally the count dominates the number of words of any subfamily containing the point. -/
theorem wcount_le_count (hθ : θ ∈ Icc 0 (π / 2)) {n : ℕ} {S : Finset Word} (hS : S ⊆ words n)
    (x : ℝ) : wcount θ S x ≤ count n θ x := by
  rw [count_eq_wcount hθ]
  exact wcount_mono hS x

/-- If all members of a depth-`n` family contain `x`, the depth-`n` count at `x` is at least the
size of the family. -/
theorem card_le_count (hθ : θ ∈ Icc 0 (π / 2)) {n : ℕ} {S : Finset Word} (hS : S ⊆ words n)
    {x : ℝ} (hx : ∀ w ∈ S, x ∈ wordIval θ w) : #S ≤ count n θ x := by
  classical
  refine le_trans (le_of_eq ?_) (wcount_le_count hθ hS x)
  unfold wcount
  rw [Finset.filter_true_of_mem hx]

theorem count_eq_zero_of_notMem_Icc (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc 0 (sig θ)) : count n θ x = 0 := by
  rw [count_eq_wcount hθ]
  exact wcount_eq_zero_of_notMem fun w _ hw => hx (wordIval_subset_Icc hθ w hw)

/-! ### The running maximum `F_N` -/

/-- The running maximum `F_N(x) = max_{0 ≤ n ≤ N} f_n(x)`, root generation included. -/
noncomputable def maxCount (N : ℕ) (θ x : ℝ) : ℕ :=
  (Finset.range (N + 1)).sup fun n => count n θ x

theorem count_le_maxCount {n N : ℕ} (h : n ≤ N) (θ x : ℝ) : count n θ x ≤ maxCount N θ x :=
  Finset.le_sup (f := fun n => count n θ x) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

theorem maxCount_le_iff {N k : ℕ} {x : ℝ} : maxCount N θ x ≤ k ↔ ∀ n ≤ N, count n θ x ≤ k := by
  simp [maxCount, Finset.sup_le_iff]

theorem exists_count_eq_maxCount (N : ℕ) (θ x : ℝ) :
    ∃ n ≤ N, count n θ x = maxCount N θ x := by
  obtain ⟨n, hn, h⟩ := Finset.exists_mem_eq_sup (Finset.range (N + 1)) Finset.nonempty_range_add_one
    (fun n => count n θ x)
  exact ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), h.symm⟩

theorem maxCount_mono {N N' : ℕ} (h : N ≤ N') (θ x : ℝ) : maxCount N θ x ≤ maxCount N' θ x :=
  maxCount_le_iff.mpr fun _ hn => count_le_maxCount (hn.trans h) θ x

theorem maxCount_succ (N : ℕ) (θ x : ℝ) :
    maxCount (N + 1) θ x = max (maxCount N θ x) (count (N + 1) θ x) := by
  simp only [maxCount, Finset.range_add_one (n := N + 1), Finset.sup_insert]
  rw [max_comm]

theorem maxCount_zero (θ x : ℝ) : maxCount 0 θ x = count 0 θ x := by
  simp [maxCount]

theorem maxCount_le_four_pow (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) (x : ℝ) :
    maxCount N θ x ≤ 4 ^ N :=
  maxCount_le_iff.mpr fun n hn =>
    (count_le_card_words hθ n x).trans (Nat.pow_le_pow_right (by norm_num) hn)

theorem maxCount_eq_zero_of_notMem_Icc (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {x : ℝ}
    (hx : x ∉ Icc 0 (sig θ)) : maxCount N θ x = 0 :=
  Nat.le_zero.mp (maxCount_le_iff.mpr fun n _ => (count_eq_zero_of_notMem_Icc hθ n hx).le)

/-- The running maximum of a sequence of measurable `ℕ`-valued functions is measurable. -/
theorem measurable_range_sup {f : ℕ → ℝ → ℕ} (hf : ∀ n, Measurable (f n)) (N : ℕ) :
    Measurable fun x => (Finset.range (N + 1)).sup fun n => f n x := by
  induction N with
  | zero => simpa using hf 0
  | succ N ih =>
    have : (fun x => (Finset.range (N + 1 + 1)).sup fun n => f n x) =
        fun x => max (f (N + 1) x) ((Finset.range (N + 1)).sup fun n => f n x) := by
      ext x
      rw [Finset.range_add_one (n := N + 1), Finset.sup_insert]
    rw [this]
    exact (hf (N + 1)).max ih

theorem measurable_maxCount (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) :
    Measurable fun x => maxCount N θ x :=
  measurable_range_sup (fun n => measurable_count' hθ n) N

theorem measurable_maxCount_real (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) :
    Measurable fun x => (maxCount N θ x : ℝ) :=
  measurable_from_nat.comp (measurable_maxCount hθ N)

/-- A bounded measurable function supported in `[0, σ]` is integrable. -/
theorem integrable_of_le_of_support {f : ℝ → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hsupp : ∀ x, x ∉ Icc 0 (sig θ) → f x = 0) : Integrable f := by
  have hg : Integrable ((Icc 0 (sig θ)).indicator fun _ => B) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  refine hg.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc 0 (sig θ)
  · simpa [hx] using hB x
  · simp [hx, hsupp x hx]

theorem integrable_maxCount_pow (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    Integrable fun x => (maxCount N θ x : ℝ) ^ k := by
  refine integrable_of_le_of_support (θ := θ) ((measurable_maxCount_real hθ N).pow_const k)
    (B := ((4 : ℝ) ^ N) ^ k) (fun x => ?_) (fun x hx => ?_)
  · rw [abs_of_nonneg (by positivity)]
    gcongr
    exact_mod_cast maxCount_le_four_pow hθ N x
  · rw [maxCount_eq_zero_of_notMem_Icc hθ N hx]
    simp [hk]

theorem integrable_count_pow (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    Integrable fun x => (count n θ x : ℝ) ^ k := by
  refine integrable_of_le_of_support (θ := θ)
    ((measurable_from_nat.comp (measurable_count' hθ n)).pow_const k)
    (B := ((4 : ℝ) ^ n) ^ k) (fun x => ?_) (fun x hx => ?_)
  · rw [abs_of_nonneg (by positivity)]
    gcongr
    exact_mod_cast count_le_card_words hθ n x
  · simp [count_eq_zero_of_notMem_Icc hθ n hx, hk]

/-- The energy of any generation `r ≤ N` is at most `∫ F_N²`. -/
theorem energy_le_integral_maxCount_sq (hθ : θ ∈ Icc 0 (π / 2)) {r N : ℕ} (h : r ≤ N) :
    energy r θ ≤ ∫ x, (maxCount N θ x : ℝ) ^ 2 := by
  refine integral_mono (integrable_count_pow hθ r two_ne_zero)
    (integrable_maxCount_pow hθ N two_ne_zero) fun x => ?_
  dsimp only
  gcongr
  exact_mod_cast count_le_maxCount h θ x

/-! ### Superlevel sets of the running maximum -/

/-- The superlevel set `{x : F_N(x) ≥ K}`; its measure is `μ_N(K)`. -/
def superLevel (N : ℕ) (θ K : ℝ) : Set ℝ :=
  {x | K ≤ (maxCount N θ x : ℝ)}

@[simp]
theorem mem_superLevel {N : ℕ} {K x : ℝ} : x ∈ superLevel N θ K ↔ K ≤ (maxCount N θ x : ℝ) :=
  Iff.rfl

theorem mem_superLevel_iff_exists {N : ℕ} {K x : ℝ} :
    x ∈ superLevel N θ K ↔ ∃ n ≤ N, K ≤ (count n θ x : ℝ) := by
  constructor
  · intro hx
    obtain ⟨n, hn, h⟩ := exists_count_eq_maxCount N θ x
    exact ⟨n, hn, by rw [h]; exact hx⟩
  · rintro ⟨n, hn, h⟩
    exact h.trans (by exact_mod_cast count_le_maxCount hn θ x)

theorem measurableSet_superLevel (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) (K : ℝ) :
    MeasurableSet (superLevel N θ K) :=
  measurableSet_le measurable_const (measurable_maxCount_real hθ N)

theorem superLevel_subset_Icc (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ} (hK : 0 < K) :
    superLevel N θ K ⊆ Icc 0 (sig θ) := by
  intro x hx
  by_contra h
  rw [mem_superLevel, maxCount_eq_zero_of_notMem_Icc hθ N h] at hx
  simp only [CharP.cast_eq_zero] at hx
  linarith

theorem volume_superLevel_le_sig (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ} (hK : 0 < K) :
    volume (superLevel N θ K) ≤ ENNReal.ofReal (sig θ) := by
  refine (measure_mono (superLevel_subset_Icc hθ N hK)).trans ?_
  simp

theorem volume_superLevel_ne_top (hθ : θ ∈ Icc 0 (π / 2)) (N : ℕ) {K : ℝ} (hK : 0 < K) :
    volume (superLevel N θ K) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_superLevel_le_sig hθ N hK)

theorem superLevel_antitone {N : ℕ} {K K' : ℝ} (h : K ≤ K') :
    superLevel N θ K' ⊆ superLevel N θ K :=
  fun _ hx => h.trans hx

theorem superLevel_mono {N N' : ℕ} (h : N ≤ N') (K : ℝ) :
    superLevel N θ K ⊆ superLevel N' θ K :=
  fun x hx => mem_superLevel.mpr <| (mem_superLevel.mp hx).trans
    (by exact_mod_cast maxCount_mono h θ x)

end Favard.Comb
