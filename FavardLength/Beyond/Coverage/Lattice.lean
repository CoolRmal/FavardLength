import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination

/-!
# A reduced basis of a planar lattice

Appendix I.3 of the beyond note. For real linear forms `f(q, p) = a q + b p` and
`g(q, p) = c q + e p` with `D = a e - b c > 0`, the image of `ℤ²` under `(f, g)` is a lattice of
determinant `D`. With `Q = f² + g²`, a shortest nonzero vector `w₁` is primitive; completing it by
Bezout and Gauss-reducing the second vector gives a unimodular basis `(w₁, w₂)` with
`Q w₁ ≤ Q w₂` and `|⟪w₁, w₂⟫| ≤ Q w₁ / 2`. The Lagrange identity
`Q w₁ Q w₂ = D² + ⟪w₁, w₂⟫²` then gives `Q w₁ Q w₂ ≤ 4 D² / 3`.
-/

open Finset

namespace Favard.Coverage

/-- The real linear form `(q, p) ↦ a q + b p` on integer vectors. -/
def linForm (a b : ℝ) (w : ℤ × ℤ) : ℝ :=
  a * w.1 + b * w.2

/-- The squared Euclidean length of the image of `w` under the pair of linear forms. -/
def quadForm (a b c e : ℝ) (w : ℤ × ℤ) : ℝ :=
  linForm a b w ^ 2 + linForm c e w ^ 2

/-- The determinant of a pair of integer vectors. -/
def det2 (w w' : ℤ × ℤ) : ℤ :=
  w.1 * w'.2 - w.2 * w'.1

/-- The quadratic form is nonnegative. -/
theorem quadForm_nonneg (a b c e : ℝ) (w : ℤ × ℤ) : 0 ≤ quadForm a b c e w := by
  unfold quadForm; positivity

/-- The coordinates are controlled by the quadratic form: `D² q² ≤ (b² + e²) Q`. -/
theorem sq_fst_le (a b c e : ℝ) (w : ℤ × ℤ) :
    (a * e - b * c) ^ 2 * (w.1 : ℝ) ^ 2 ≤ (b ^ 2 + e ^ 2) * quadForm a b c e w := by
  unfold quadForm linForm
  nlinarith [sq_nonneg (b * (a * w.1 + b * w.2) + e * (c * w.1 + e * w.2))]

/-- The coordinates are controlled by the quadratic form: `D² p² ≤ (a² + c²) Q`. -/
theorem sq_snd_le (a b c e : ℝ) (w : ℤ × ℤ) :
    (a * e - b * c) ^ 2 * (w.2 : ℝ) ^ 2 ≤ (a ^ 2 + c ^ 2) * quadForm a b c e w := by
  unfold quadForm linForm
  nlinarith [sq_nonneg (a * (a * w.1 + b * w.2) + c * (c * w.1 + e * w.2))]

/-- The quadratic form is positive definite on `ℤ²`. -/
theorem quadForm_pos (a b c e : ℝ) (hD : 0 < a * e - b * c) {w : ℤ × ℤ} (hw : w ≠ 0) :
    0 < quadForm a b c e w := by
  rcases (quadForm_nonneg a b c e w).lt_or_eq with h | h
  · exact h
  exfalso
  apply hw
  have h1 := sq_fst_le a b c e w
  have h2 := sq_snd_le a b c e w
  rw [← h, mul_zero] at h1 h2
  have hD2 : 0 < (a * e - b * c) ^ 2 := by positivity
  have e1 : (w.1 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (w.1 : ℝ)]
  have e2 : (w.2 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (w.2 : ℝ)]
  have f1 : w.1 = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e1
  have f2 : w.2 = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e2
  exact Prod.ext f1 f2

/-- A shortest nonzero lattice vector exists. -/
theorem exists_shortest (a b c e : ℝ) (hD : 0 < a * e - b * c) :
    ∃ w₁ : ℤ × ℤ, w₁ ≠ 0 ∧ ∀ w : ℤ × ℤ, w ≠ 0 → quadForm a b c e w₁ ≤ quadForm a b c e w := by
  set D := a * e - b * c with hD_def
  set T := quadForm a b c e (0, 1) with hT
  set X := (b ^ 2 + e ^ 2) * T / D ^ 2 + (a ^ 2 + c ^ 2) * T / D ^ 2 with hX
  set B : ℤ := (⌈X⌉₊ : ℤ) + 1 with hB
  -- vectors of length at most that of `(0, 1)` lie in the box `[-B, B]²`
  have hbox : ∀ w : ℤ × ℤ, quadForm a b c e w ≤ T → w ∈ Icc (-B) B ×ˢ Icc (-B) B := by
    intro w hw
    have hD2 : 0 < D ^ 2 := by positivity
    have hT0 : 0 ≤ T := quadForm_nonneg _ _ _ _ _
    have h1 : (w.1 : ℝ) ^ 2 ≤ X := by
      have := sq_fst_le a b c e w
      have h' : (w.1 : ℝ) ^ 2 ≤ (b ^ 2 + e ^ 2) * T / D ^ 2 := by
        rw [le_div_iff₀ hD2]
        nlinarith [sq_nonneg b, sq_nonneg e]
      have : 0 ≤ (a ^ 2 + c ^ 2) * T / D ^ 2 := by positivity
      linarith
    have h2 : (w.2 : ℝ) ^ 2 ≤ X := by
      have := sq_snd_le a b c e w
      have h' : (w.2 : ℝ) ^ 2 ≤ (a ^ 2 + c ^ 2) * T / D ^ 2 := by
        rw [le_div_iff₀ hD2]
        nlinarith [sq_nonneg a, sq_nonneg c]
      have : 0 ≤ (b ^ 2 + e ^ 2) * T / D ^ 2 := by positivity
      linarith
    have hXc : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have k1 : |w.1| ≤ (⌈X⌉₊ : ℤ) := by
      have : ((|w.1| : ℤ) : ℝ) ≤ (⌈X⌉₊ : ℝ) := by
        have habs : (|w.1| : ℤ) ≤ w.1 ^ 2 := by
          rw [← sq_abs]; exact Int.le_self_sq _
        have : ((|w.1| : ℤ) : ℝ) ≤ (w.1 : ℝ) ^ 2 := by exact_mod_cast habs
        linarith
      exact_mod_cast this
    have k2 : |w.2| ≤ (⌈X⌉₊ : ℤ) := by
      have : ((|w.2| : ℤ) : ℝ) ≤ (⌈X⌉₊ : ℝ) := by
        have habs : (|w.2| : ℤ) ≤ w.2 ^ 2 := by
          rw [← sq_abs]; exact Int.le_self_sq _
        have : ((|w.2| : ℤ) : ℝ) ≤ (w.2 : ℝ) ^ 2 := by exact_mod_cast habs
        linarith
      exact_mod_cast this
    rw [mem_product, mem_Icc, mem_Icc]
    rw [abs_le] at k1 k2
    omega
  set S := (Icc (-B) B ×ˢ Icc (-B) B).filter (· ≠ (0 : ℤ × ℤ)) with hS
  have h01 : ((0 : ℤ), (1 : ℤ)) ∈ S := by
    rw [hS, mem_filter]
    refine ⟨hbox _ le_rfl, ?_⟩
    simp
  obtain ⟨w₁, hw₁S, hmin⟩ := S.exists_min_image (quadForm a b c e) ⟨_, h01⟩
  refine ⟨w₁, (mem_filter.1 hw₁S).2, fun w hw => ?_⟩
  by_cases hwS : w ∈ S
  · exact hmin w hwS
  · have : ¬ quadForm a b c e w ≤ T := by
      intro h
      exact hwS (mem_filter.2 ⟨hbox w h, hw⟩)
    exact (hmin _ h01).trans (le_of_lt (not_le.1 this))

/-- The linear forms are homogeneous under integer scaling. -/
theorem linForm_smul (a b : ℝ) (k : ℤ) (w : ℤ × ℤ) :
    linForm a b (k * w.1, k * w.2) = k * linForm a b w := by
  unfold linForm; push_cast; ring

/-- A shortest nonzero vector is primitive. -/
theorem gcd_eq_one_of_shortest (a b c e : ℝ) (hD : 0 < a * e - b * c) {w₁ : ℤ × ℤ}
    (hw₁ : w₁ ≠ 0) (hmin : ∀ w : ℤ × ℤ, w ≠ 0 → quadForm a b c e w₁ ≤ quadForm a b c e w) :
    Int.gcd w₁.1 w₁.2 = 1 := by
  by_contra hg
  set g := Int.gcd w₁.1 w₁.2 with hg_def
  have hg0 : g ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    exact hw₁ (Prod.ext h0.1 h0.2)
  have hg2 : (2 : ℝ) ≤ g := by
    have : 2 ≤ g := by omega
    exact_mod_cast this
  obtain ⟨u, hu⟩ := Int.gcd_dvd_left w₁.1 w₁.2
  obtain ⟨v, hv⟩ := Int.gcd_dvd_right w₁.1 w₁.2
  set w' : ℤ × ℤ := (u, v) with hw'
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hw₁
    have hu0 : u = 0 := congrArg Prod.fst h
    have hv0 : v = 0 := congrArg Prod.snd h
    rw [hu0, mul_zero] at hu
    rw [hv0, mul_zero] at hv
    exact Prod.ext hu hv
  have hscale : quadForm a b c e w₁ = (g : ℝ) ^ 2 * quadForm a b c e w' := by
    have : w₁ = ((g : ℤ) * w'.1, (g : ℤ) * w'.2) := Prod.ext hu hv
    rw [this]
    unfold quadForm
    rw [linForm_smul, linForm_smul]
    push_cast
    ring
  have hpos := quadForm_pos a b c e hD hw'0
  have := hmin w' hw'0
  rw [hscale] at this
  have h4 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h4 hpos.le]

/-- **Reduced basis** (Appendix I, (8)). There is a unimodular integer basis `(w₁, w₂)` with
`Q w₁ ≤ Q w₂` and `Q w₁ Q w₂ ≤ 4 D² / 3`. -/
theorem exists_reduced_basis (a b c e : ℝ) (hD : 0 < a * e - b * c) :
    ∃ w₁ w₂ : ℤ × ℤ, det2 w₁ w₂ = 1 ∧ quadForm a b c e w₁ ≤ quadForm a b c e w₂ ∧
      quadForm a b c e w₁ * quadForm a b c e w₂ ≤ 4 / 3 * (a * e - b * c) ^ 2 := by
  obtain ⟨w₁, hw₁, hmin⟩ := exists_shortest a b c e hD
  have hgcd := gcd_eq_one_of_shortest a b c e hD hw₁ hmin
  have hbez := Int.gcd_eq_gcd_ab w₁.1 w₁.2
  rw [hgcd, Nat.cast_one] at hbez
  set s : ℤ := -Int.gcdB w₁.1 w₁.2
  set t : ℤ := Int.gcdA w₁.1 w₁.2
  have hQ1 := quadForm_pos a b c e hD hw₁
  set Q1 := quadForm a b c e w₁ with hQ1_def
  -- Gauss reduction of the Bezout completion `(s, t)`
  set τ : ℝ := (linForm a b w₁ * linForm a b (s, t) + linForm c e w₁ * linForm c e (s, t)) / Q1
  set k : ℤ := round τ
  set w₂ : ℤ × ℤ := (s - k * w₁.1, t - k * w₁.2) with hw₂
  have hdet : det2 w₁ w₂ = 1 := by
    simp only [det2, hw₂, s, t]
    linear_combination -hbez
  have hw₂0 : w₂ ≠ 0 := by
    intro h
    rw [h] at hdet
    simp [det2] at hdet
  have hip : |linForm a b w₁ * linForm a b w₂ + linForm c e w₁ * linForm c e w₂| ≤ Q1 / 2 := by
    have hexp : linForm a b w₁ * linForm a b w₂ + linForm c e w₁ * linForm c e w₂ =
        Q1 * (τ - k) := by
      have hl1 : linForm a b w₂ = linForm a b (s, t) - k * linForm a b w₁ := by
        simp only [hw₂, linForm]; push_cast; ring
      have hl2 : linForm c e w₂ = linForm c e (s, t) - k * linForm c e w₁ := by
        simp only [hw₂, linForm]; push_cast; ring
      rw [hl1, hl2]
      simp only [τ]
      rw [mul_sub Q1, mul_div_cancel₀ _ hQ1.ne']
      simp only [hQ1_def, quadForm]
      ring
    rw [hexp, abs_mul, abs_of_pos hQ1]
    have := abs_sub_round τ
    nlinarith
  have hle := hmin w₂ hw₂0
  -- Lagrange identity: `Q w₁ Q w₂ = D² + ⟪w₁, w₂⟫²`
  have hlag : Q1 * quadForm a b c e w₂ = (a * e - b * c) ^ 2 +
      (linForm a b w₁ * linForm a b w₂ + linForm c e w₁ * linForm c e w₂) ^ 2 := by
    have hdet' : ((w₁.1 : ℝ) * w₂.2 - w₁.2 * w₂.1) = 1 := by
      have : ((det2 w₁ w₂ : ℤ) : ℝ) = 1 := by rw [hdet]; simp
      simpa [det2] using this
    have key : linForm a b w₁ * linForm c e w₂ - linForm c e w₁ * linForm a b w₂ =
        (a * e - b * c) * ((w₁.1 : ℝ) * w₂.2 - w₁.2 * w₂.1) := by
      unfold linForm; ring
    rw [hdet', mul_one] at key
    rw [← key]
    simp only [hQ1_def, quadForm]
    ring
  refine ⟨w₁, w₂, hdet, hle, ?_⟩
  have hsq : (linForm a b w₁ * linForm a b w₂ + linForm c e w₁ * linForm c e w₂) ^ 2 ≤
      Q1 ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.1 hip).1 (abs_le.1 hip).2
    linarith
  have hQ1sq : Q1 ^ 2 ≤ 4 / 3 * (a * e - b * c) ^ 2 := by
    nlinarith
  nlinarith

end Favard.Coverage
