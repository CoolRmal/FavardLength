import FavardLength.Beyond.Exclusion.Defs
import FavardLength.Fourier.Bridge
import FavardLength.Fourier.Triangle

/-!
# Basic properties of the tail density

For the normalized tail density `f_{n,t} = ρ⁻¹ ∑_w 1_{[c_w - ρ4^{-n}/2, c_w + ρ4^{-n}/2]}`
(`ρ = 8/3`) we prove:

* nonnegativity, the bound `f_{n,t} ≤ ρ⁻¹ 4^n`, measurability and integrability;
* mass one, `∫ f_{n,t} = 1`;
* for `|t| ≤ 1`, `|c_w(t)| ≤ ρ/2 - ρ4^{-n}/2`, hence `f_{n,t}` vanishes outside `[-ρ/2, ρ/2]`;
* `∫ f_{n,t}² = normEnergy n t` (via the overlap formula and `Bridge.sum_sum_max_eq`);
* the **self-similar splitting** `f_{j+n,t}(y) = ∑_{u : SqCode j} f_{n,t}(4^j (y - c_u(t)))`;
* integrability of `g · f_{n,t}` for continuous `g`, and the mass of a sum of copies.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

open Bridge

/-- The box `[c - ρ4^{-n}/2, c + ρ4^{-n}/2]` around a centre. -/
lemma measurableSet_box (n : ℕ) (c : ℝ) :
    MeasurableSet (Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)) :=
  measurableSet_Icc

lemma volume_real_box (n : ℕ) (c : ℝ) :
    volume.real (Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)) = 8 / 3 / 4 ^ n := by
  have : (0 : ℝ) ≤ 4 / 3 / 4 ^ n := by positivity
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

lemma integrable_indicator_box (n : ℕ) (c : ℝ) :
    Integrable ((Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n)).indicator (1 : ℝ → ℝ)) :=
  (integrableOn_const (C := (1 : ℝ)) measure_Icc_lt_top.ne).integrable_indicator
    (measurableSet_box n c)

lemma tailDensity_nonneg (n : ℕ) (t x : ℝ) : 0 ≤ tailDensity n t x := by
  unfold tailDensity
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun w _ => ?_)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- `f_{n,t} ≤ ρ⁻¹ 4^n`. -/
lemma tailDensity_le (n : ℕ) (t x : ℝ) : tailDensity n t x ≤ 3 / 8 * 4 ^ n := by
  unfold tailDensity
  gcongr
  calc ∑ w : SqCode n, (Icc (code t w - 4 / 3 / 4 ^ n) (code t w + 4 / 3 / 4 ^ n)).indicator 1 x
      ≤ ∑ _w : SqCode n, (1 : ℝ) := Finset.sum_le_sum fun w _ =>
        Set.indicator_le_self' (fun _ _ => zero_le_one) x
    _ = 4 ^ n := by simp

lemma measurable_tailDensity (n : ℕ) (t : ℝ) : Measurable (tailDensity n t) := by
  unfold tailDensity
  exact (Finset.measurable_sum _ fun w _ =>
    measurable_one.indicator (measurableSet_box n _)).const_mul _

lemma integrable_tailDensity (n : ℕ) (t : ℝ) : Integrable (tailDensity n t) := by
  unfold tailDensity
  exact (integrable_finsetSum _ fun w _ => integrable_indicator_box n _).const_mul _

/-- **Mass one**: `∫ f_{n,t} = 1`. -/
theorem integral_tailDensity (n : ℕ) (t : ℝ) : ∫ x, tailDensity n t x = 1 := by
  unfold tailDensity
  rw [integral_const_mul, integral_finsetSum _ fun w _ => integrable_indicator_box n _]
  simp_rw [integral_indicator_one (measurableSet_box n _), volume_real_box]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- For `|t| ≤ 1` the normalized centres satisfy `|c_w(t)| ≤ ρ/2 - ρ4^{-n}/2`. -/
lemma abs_code_le {t : ℝ} (ht : |t| ≤ 1) {n : ℕ} (w : SqCode n) :
    |code t w| ≤ 4 / 3 - 4 / 3 / 4 ^ n := by
  have hd : ∀ p : Bool × Bool, |digit t p| ≤ 1 := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> simp [digit, abs_neg, ht]
  unfold code
  calc |∑ j : Fin n, digit t (w j) / 4 ^ (j : ℕ)|
      ≤ ∑ j : Fin n, |digit t (w j) / 4 ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, (1 / 4 : ℝ) ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (j : ℕ)), one_div_pow]
        exact div_le_div_of_nonneg_right (hd _) (by positivity)
    _ = ∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j := Fin.sum_univ_eq_sum_range (fun j => _) n
    _ = 4 / 3 - 4 / 3 / 4 ^ n := by
        rw [geom_sum_eq (by norm_num), one_div_pow]
        field_simp
        ring

/-- For `|t| ≤ 1`, `f_{n,t}` vanishes outside `[-ρ/2, ρ/2] = [-4/3, 4/3]`. -/
lemma tailDensity_eq_zero {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) {x : ℝ} (hx : 4 / 3 < |x|) :
    tailDensity n t x = 0 := by
  unfold tailDensity
  rw [Finset.sum_eq_zero fun w _ => ?_, mul_zero]
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  have hc := abs_code_le ht w
  rw [abs_le] at hc
  rcases lt_abs.mp hx with h | h <;> linarith [hmem.1, hmem.2]

lemma support_tailDensity_subset {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    Function.support (tailDensity n t) ⊆ Icc (-(4 / 3)) (4 / 3) := by
  intro x hx
  by_contra h
  exact hx (tailDensity_eq_zero ht n (by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)))

lemma hasCompactSupport_tailDensity {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    HasCompactSupport (tailDensity n t) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx =>
    Function.notMem_support.mp fun h => hx (support_tailDensity_subset ht n h)

/-- `g · f_{n,t}` is integrable for every bounded measurable complex function `g`; in
particular for every continuous `g` (see `integrable_mul_tailDensity`). -/
lemma integrable_bdd_mul_tailDensity (n : ℕ) (t : ℝ) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable fun x => g x * (tailDensity n t x : ℂ) :=
  (integrable_tailDensity n t).ofReal.bdd_mul hg (Filter.Eventually.of_forall hC)

/-- For `|t| ≤ 1`, `g · f_{n,t}` is integrable for every continuous complex function `g`. -/
lemma integrable_mul_tailDensity {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) {g : ℝ → ℂ}
    (hg : Continuous g) : Integrable fun x => g x * (tailDensity n t x : ℂ) := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := -(4 / 3 : ℝ))
    (b := 4 / 3)) hg.continuousOn
  have hint : Integrable fun x => ((tailDensity n t x : ℝ) : ℂ) :=
    (integrable_tailDensity n t).ofReal
  refine (hint.const_mul ((max C 0 : ℝ) : ℂ)).mono (hg.aestronglyMeasurable.mul
    hint.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tailDensity_nonneg n t x), abs_of_nonneg (le_max_right C 0)]
  by_cases hx : x ∈ Icc (-(4 / 3 : ℝ)) (4 / 3)
  · exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left _ _))
      (tailDensity_nonneg n t x)
  · have : tailDensity n t x = 0 := by
      by_contra h
      exact hx (support_tailDensity_subset ht n h)
    simp [this]

/-- For `|t| ≤ 1`, `g · f_{n,t}` is integrable for every continuous real function `g`. -/
lemma integrable_real_mul_tailDensity {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) : Integrable fun x => g x * tailDensity n t x := by
  have h := (integrable_mul_tailDensity ht n (Complex.continuous_ofReal.comp hg)).re
  simpa using h

/-! ### The energy -/

/-- The overlap of two boxes: `|B_c ∩ B_{c'}| = (ρ4^{-n} - |c - c'|)_+`. -/
lemma volume_real_box_inter (n : ℕ) (c c' : ℝ) :
    volume.real (Icc (c - 4 / 3 / 4 ^ n) (c + 4 / 3 / 4 ^ n) ∩
        Icc (c' - 4 / 3 / 4 ^ n) (c' + 4 / 3 / 4 ^ n)) =
      max 0 (8 / 3 / 4 ^ n - |c - c'|) := by
  rw [Icc_inter_Icc, Real.volume_real_Icc]
  have h := BasicProof.min_add_sub_max (c - 4 / 3 / 4 ^ n) (c' - 4 / 3 / 4 ^ n) (8 / 3 / 4 ^ n)
  have e1 : c - 4 / 3 / 4 ^ n + 8 / 3 / 4 ^ n = c + 4 / 3 / 4 ^ n := by ring
  have e2 : c' - 4 / 3 / 4 ^ n + 8 / 3 / 4 ^ n = c' + 4 / 3 / 4 ^ n := by ring
  rw [e1, e2] at h
  rw [h, max_comm, sub_sub_sub_cancel_right]

/-- **Energy identity**: `∫ f_{n,t}² = normEnergy n t`. -/
theorem integral_tailDensity_sq (n : ℕ) (t : ℝ) :
    ∫ x, tailDensity n t x ^ 2 = normEnergy n t := by
  have hsq : ∀ x, tailDensity n t x ^ 2 = (3 / 8) ^ 2 * ∑ w : SqCode n, ∑ w' : SqCode n,
      (Icc (code t w - 4 / 3 / 4 ^ n) (code t w + 4 / 3 / 4 ^ n) ∩
        Icc (code t w' - 4 / 3 / 4 ^ n) (code t w' + 4 / 3 / 4 ^ n)).indicator 1 x := by
    intro x
    rw [tailDensity, mul_pow, sq (∑ w : SqCode n, _), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [Set.inter_indicator_one]
    rfl
  have hint : ∀ w w' : SqCode n, Integrable
      ((Icc (code t w - 4 / 3 / 4 ^ n) (code t w + 4 / 3 / 4 ^ n) ∩
        Icc (code t w' - 4 / 3 / 4 ^ n) (code t w' + 4 / 3 / 4 ^ n)).indicator (1 : ℝ → ℝ)) :=
    fun w w' => (integrableOn_const (C := (1 : ℝ))
      (measure_ne_top_of_subset inter_subset_left measure_Icc_lt_top.ne)).integrable_indicator
        ((measurableSet_box n _).inter (measurableSet_box n _))
  simp_rw [hsq]
  rw [integral_const_mul, integral_finsetSum _ fun w _ =>
    integrable_finsetSum _ fun w' _ => hint w w']
  have h2 : ∀ w : SqCode n, ∫ x, ∑ w' : SqCode n,
      (Icc (code t w - 4 / 3 / 4 ^ n) (code t w + 4 / 3 / 4 ^ n) ∩
        Icc (code t w' - 4 / 3 / 4 ^ n) (code t w' + 4 / 3 / 4 ^ n)).indicator 1 x =
      ∑ w' : SqCode n, max 0 (8 / 3 / 4 ^ n - |code t w - code t w'|) := by
    intro w
    rw [integral_finsetSum _ fun w' _ => hint w w']
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [integral_indicator_one ((measurableSet_box n _).inter (measurableSet_box n _)),
      volume_real_box_inter]
  simp_rw [h2]
  rw [sum_sum_max_eq Favard.triangle]
  ring

/-! ### Self-similarity -/

/-- The centre of a concatenated code: `c_{uv}(t) = c_u(t) + 4^{-j} c_v(t)`. -/
lemma code_append {j n : ℕ} (t : ℝ) (u : SqCode j) (v : SqCode n) :
    code t (Fin.append u v) = code t u + code t v / 4 ^ j := by
  unfold code
  rw [Fin.sum_univ_add, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd, pow_add]
    field_simp

/-- **Self-similar splitting**: `f_{j+n,t}(y) = ∑_{u : SqCode j} f_{n,t}(4^j (y - c_u(t)))`.
The terms are the rescaled generation-`j` cylinders (Appendix D (7)). -/
theorem tailDensity_add (j n : ℕ) (t y : ℝ) :
    tailDensity (j + n) t y = ∑ u : SqCode j, tailDensity n t (4 ^ j * (y - code t u)) := by
  unfold tailDensity
  rw [← Finset.mul_sum]
  congr 1
  rw [← (Fin.appendEquiv j n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [show (Fin.appendEquiv j n) (u, v) = Fin.append u v from rfl, code_append]
  simp only [Set.indicator_apply, mem_Icc, Pi.one_apply]
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  have hiff : (code t u + code t v / 4 ^ j - 4 / 3 / 4 ^ (j + n) ≤ y ∧
        y ≤ code t u + code t v / 4 ^ j + 4 / 3 / 4 ^ (j + n)) ↔
      (code t v - 4 / 3 / 4 ^ n ≤ 4 ^ j * (y - code t u) ∧
        4 ^ j * (y - code t u) ≤ code t v + 4 / 3 / 4 ^ n) := by
    have e1 : code t u + code t v / 4 ^ j - 4 / 3 / 4 ^ (j + n) =
        code t u + (code t v - 4 / 3 / 4 ^ n) / 4 ^ j := by rw [pow_add]; field_simp; ring
    have e2 : code t u + code t v / 4 ^ j + 4 / 3 / 4 ^ (j + n) =
        code t u + (code t v + 4 / 3 / 4 ^ n) / 4 ^ j := by rw [pow_add]; field_simp; ring
    rw [e1, e2]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have := (div_le_iff₀ h4).1 (show (code t v - 4 / 3 / 4 ^ n) / 4 ^ j ≤ y - code t u by
          linarith)
        linarith
      · have := (le_div_iff₀ h4).1 (show y - code t u ≤ (code t v + 4 / 3 / 4 ^ n) / 4 ^ j by
          linarith)
        linarith
    · rintro ⟨h1, h2⟩
      constructor
      · have := (div_le_iff₀ h4).2 (show code t v - 4 / 3 / 4 ^ n ≤ (y - code t u) * 4 ^ j by
          linarith)
        linarith
      · have := (le_div_iff₀ h4).2 (show (y - code t u) * 4 ^ j ≤ code t v + 4 / 3 / 4 ^ n by
          linarith)
        linarith
  simp only [hiff]

/-- **Rescaled cylinders** (Appendix D (7), E §1): for `j ≤ N` and any base point `a`,
`f_{N,t}(a + 4^{-j} x) = ∑_{u : SqCode j} f_{N-j,t}(x - β_u)` with `β_u = 4^j (c_u(t) - a)`. -/
theorem tailDensity_rescale {j N : ℕ} (hjN : j ≤ N) (t a x : ℝ) :
    tailDensity N t (a + x / 4 ^ j) =
      ∑ u : SqCode j, tailDensity (N - j) t (x - 4 ^ j * (code t u - a)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjN
  rw [tailDensity_add, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

/-! ### Sums of copies -/

lemma copySum_nonneg (n : ℕ) (t : ℝ) {m : ℕ} (β : Fin m → ℝ) (x : ℝ) :
    0 ≤ copySum n t β x :=
  Finset.sum_nonneg fun _ _ => tailDensity_nonneg n t _

lemma integrable_copySum (n : ℕ) (t : ℝ) {m : ℕ} (β : Fin m → ℝ) :
    Integrable (copySum n t β) := by
  unfold copySum
  exact integrable_finsetSum _ fun i _ => (integrable_tailDensity n t).comp_sub_right (β i)

/-- A sum of `m` copies has mass `m`. -/
lemma integral_copySum (n : ℕ) (t : ℝ) {m : ℕ} (β : Fin m → ℝ) :
    ∫ x, copySum n t β x = m := by
  unfold copySum
  rw [integral_finsetSum _ fun i _ => (integrable_tailDensity n t).comp_sub_right (β i)]
  simp_rw [integral_sub_right_eq_self (fun x => tailDensity n t x), integral_tailDensity]
  simp

end Favard.Exclusion
