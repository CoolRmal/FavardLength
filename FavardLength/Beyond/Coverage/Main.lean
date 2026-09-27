import FavardLength.Beyond.Statements
import FavardLength.Beyond.Coverage.Primitive
import FavardLength.Beyond.Coverage.Lattice
import FavardLength.Beyond.Coverage.Exception
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Redundant odd/odd rational coverage

Appendix I of the beyond note: the contract `CoverageStatement`.

For `x ∈ [0, 1]` consider the lattice `{(q/R, (p - x q)/(rR)) : (q, p) ∈ ℤ²}` of determinant
`1/M`, `M = rR²`. Take a reduced basis `(w₁, w₂)` (`Lattice.lean`) with lengths `s₁ ≤ s₂` and
`s₁ s₂ < 2/M`. If `s₁ < A/M` then `x` lies in the exceptional set of `Exception.lean`, whose
measure is at most `4A²/M`. Otherwise the coefficient rectangle
`|m - m₀| ≤ η/s₁`, `|n - n₀| ≤ η/s₂` (`η = 1/32`) around the coordinates `(m₀, n₀)` of the target
centre `(3/4, 0)` maps into the ball of radius `1/16` about it, and every such point `(q, p)`
gives a fraction `p/q` with `11R/16 ≤ q ≤ 13R/16`, `0 ≤ p ≤ q` and `|x - p/q| ≤ r/11`. The odd/odd
condition on `(q, p)` is a fixed nonzero parity class of `(m, n)` because the basis is unimodular,
and `Primitive.lean` gives at least `L₁ L₂ / 2 ≥ M / 16384` coprime pairs of that class.
-/

open MeasureTheory Set

namespace Favard.Coverage

/-- Integers `j` of the parameter interval give points `α + 2j` within `ρ` of the centre `c₀`. -/
theorem abs_sub_le_of_mem_Ico {c₀ ρ : ℝ} (hρ : 0 ≤ ρ) (α j : ℤ)
    (hj : j ∈ Finset.Ico ⌈(c₀ - ρ - α) / 2⌉ (⌈(c₀ - ρ - α) / 2⌉ + ⌊ρ⌋₊)) :
    |((α + 2 * j : ℤ) : ℝ) - c₀| ≤ ρ := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
  have h1' : (c₀ - ρ - α) / 2 ≤ (j : ℝ) := Int.ceil_le.1 h1
  have h3 : (⌈(c₀ - ρ - α) / 2⌉ : ℝ) < (c₀ - ρ - α) / 2 + 1 := Int.ceil_lt_add_one _
  have h4 : (⌊ρ⌋₊ : ℝ) ≤ ρ := Nat.floor_le hρ
  have h2' : (j : ℝ) + 1 ≤ ⌈(c₀ - ρ - α) / 2⌉ + (⌊ρ⌋₊ : ℝ) := by
    have : j + 1 ≤ ⌈(c₀ - ρ - α) / 2⌉ + (⌊ρ⌋₊ : ℤ) := h2
    exact_mod_cast this
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- The integer combination `m w₁ + n w₂`. -/
def comb (w₁ w₂ : ℤ × ℤ) (m n : ℤ) : ℤ × ℤ :=
  (m * w₁.1 + n * w₂.1, m * w₁.2 + n * w₂.2)

/-- The linear forms are additive on integer combinations. -/
theorem linForm_comb (a b : ℝ) (w₁ w₂ : ℤ × ℤ) (m n : ℤ) :
    linForm a b (comb w₁ w₂ m n) = m * linForm a b w₁ + n * linForm a b w₂ := by
  simp only [linForm, comb]
  push_cast
  ring

/-- The first coordinate is bounded by the length. -/
theorem abs_linForm_le_sqrt_left (a b c e : ℝ) (w : ℤ × ℤ) :
    |linForm a b w| ≤ √(quadForm a b c e w) :=
  Real.abs_le_sqrt (by unfold quadForm; nlinarith [sq_nonneg (linForm c e w)])

/-- The second coordinate is bounded by the length. -/
theorem abs_linForm_le_sqrt_right (a b c e : ℝ) (w : ℤ × ℤ) :
    |linForm c e w| ≤ √(quadForm a b c e w) :=
  Real.abs_le_sqrt (by unfold quadForm; nlinarith [sq_nonneg (linForm a b w)])

/-- **The coefficient rectangle maps into the target ball** (Appendix I, (10)–(11)). With
`m₀ = (3/4) g(w₂)/D` and `n₀ = -(3/4) g(w₁)/D` the coordinates of `(3/4, 0)` in the basis, an
integer pair with `|m - m₀| √Q(w₁) ≤ η` and `|n - n₀| √Q(w₂) ≤ η` gives a lattice point within
`2η` of `(3/4, 0)` in each coordinate. -/
theorem comb_target (a b c e : ℝ) {w₁ w₂ : ℤ × ℤ} (hdet : det2 w₁ w₂ = 1)
    (hD : 0 < a * e - b * c) {η : ℝ} {m n : ℤ}
    (hm : |(m : ℝ) - 3 / 4 * linForm c e w₂ / (a * e - b * c)| * √(quadForm a b c e w₁) ≤ η)
    (hn : |(n : ℝ) + 3 / 4 * linForm c e w₁ / (a * e - b * c)| * √(quadForm a b c e w₂) ≤ η) :
    |linForm a b (comb w₁ w₂ m n) - 3 / 4| ≤ 2 * η ∧ |linForm c e (comb w₁ w₂ m n)| ≤ 2 * η := by
  set D := a * e - b * c with hD_def
  have hdet' : ((w₁.1 : ℝ) * w₂.2 - w₁.2 * w₂.1) = 1 := by
    have : ((det2 w₁ w₂ : ℤ) : ℝ) = 1 := by rw [hdet]; simp
    simpa [det2] using this
  have hkey : linForm a b w₁ * linForm c e w₂ - linForm c e w₁ * linForm a b w₂ = D := by
    have : linForm a b w₁ * linForm c e w₂ - linForm c e w₁ * linForm a b w₂ =
        D * ((w₁.1 : ℝ) * w₂.2 - w₁.2 * w₂.1) := by
      unfold linForm; ring
    rw [this, hdet', mul_one]
  set f₁ := linForm a b w₁
  set f₂ := linForm a b w₂
  set g₁ := linForm c e w₁
  set g₂ := linForm c e w₂
  set m₀ := 3 / 4 * g₂ / D
  set n₀ := -(3 / 4 * g₁ / D)
  have h34 : m₀ * f₁ + n₀ * f₂ = 3 / 4 := by
    have : m₀ * f₁ + n₀ * f₂ = 3 / 4 / D * (f₁ * g₂ - g₁ * f₂) := by
      simp only [m₀, n₀]; ring
    rw [this, hkey]
    field_simp
  have h0 : m₀ * g₁ + n₀ * g₂ = 0 := by
    simp only [m₀, n₀]; ring
  have hn' : |(n : ℝ) - n₀| * √(quadForm a b c e w₂) ≤ η := by
    simpa [n₀, sub_neg_eq_add] using hn
  have hf₁ := abs_linForm_le_sqrt_left a b c e w₁
  have hf₂ := abs_linForm_le_sqrt_left a b c e w₂
  have hg₁ := abs_linForm_le_sqrt_right a b c e w₁
  have hg₂ := abs_linForm_le_sqrt_right a b c e w₂
  have hA : 0 ≤ |(m : ℝ) - m₀| := abs_nonneg _
  have hB : 0 ≤ |(n : ℝ) - n₀| := abs_nonneg _
  rw [linForm_comb, linForm_comb]
  constructor
  · have e1 : (m : ℝ) * f₁ + n * f₂ - 3 / 4 = (m - m₀) * f₁ + (n - n₀) * f₂ := by
      linear_combination h34
    rw [e1]
    calc |((m : ℝ) - m₀) * f₁ + (n - n₀) * f₂| ≤ |((m : ℝ) - m₀) * f₁| + |((n : ℝ) - n₀) * f₂| :=
          abs_add_le _ _
      _ = |(m : ℝ) - m₀| * |f₁| + |(n : ℝ) - n₀| * |f₂| := by rw [abs_mul, abs_mul]
      _ ≤ |(m : ℝ) - m₀| * √(quadForm a b c e w₁) + |(n : ℝ) - n₀| * √(quadForm a b c e w₂) :=
          add_le_add (mul_le_mul_of_nonneg_left hf₁ hA) (mul_le_mul_of_nonneg_left hf₂ hB)
      _ ≤ 2 * η := by linarith
  · have e1 : (m : ℝ) * g₁ + n * g₂ = (m - m₀) * g₁ + (n - n₀) * g₂ := by
      linear_combination h0
    rw [e1]
    calc |((m : ℝ) - m₀) * g₁ + (n - n₀) * g₂| ≤ |((m : ℝ) - m₀) * g₁| + |((n : ℝ) - n₀) * g₂| :=
          abs_add_le _ _
      _ = |(m : ℝ) - m₀| * |g₁| + |(n : ℝ) - n₀| * |g₂| := by rw [abs_mul, abs_mul]
      _ ≤ |(m : ℝ) - m₀| * √(quadForm a b c e w₁) + |(n : ℝ) - n₀| * √(quadForm a b c e w₂) :=
          add_le_add (mul_le_mul_of_nonneg_left hg₁ hA) (mul_le_mul_of_nonneg_left hg₂ hB)
      _ ≤ 2 * η := by linarith

/-- **Target points give admissible fractions** (Appendix I, (9)). If `|q/R - 3/4| ≤ 1/16` and
`|p - x q| ≤ rR/16` with `rR ≤ 1` and `x ∈ [0, 1]`, then `0 ≤ p ≤ q`, `R/2 ≤ q ≤ R` and
`|x - p/q| ≤ r`. -/
theorem fraction_props {R r x : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r * R ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) {q p : ℤ} (hq : |(q : ℝ) / R - 3 / 4| ≤ 1 / 16)
    (hp : |((p : ℝ) - x * q) / (r * R)| ≤ 1 / 16) :
    0 ≤ p ∧ p ≤ q ∧ R / 2 ≤ q ∧ (q : ℝ) ≤ R ∧ |x - p / q| ≤ r := by
  obtain ⟨hx0, hx1⟩ := hx
  have hrRpos : 0 < r * R := by positivity
  rw [abs_le] at hq hp
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨hp1, hp2⟩ := hp
  have hq1' : 11 / 16 * R ≤ q := by
    have : 11 / 16 ≤ (q : ℝ) / R := by linarith
    rwa [le_div_iff₀ hR] at this
  have hq2' : (q : ℝ) ≤ 13 / 16 * R := by
    have : (q : ℝ) / R ≤ 13 / 16 := by linarith
    rwa [div_le_iff₀ hR] at this
  have hp1' : -(r * R) / 16 ≤ (p : ℝ) - x * q := by
    rw [le_div_iff₀ hrRpos] at hp1
    linarith
  have hp2' : (p : ℝ) - x * q ≤ r * R / 16 := by
    rw [div_le_iff₀ hrRpos] at hp2
    linarith
  have hqpos : (0 : ℝ) < q := by nlinarith
  have hp0 : 0 ≤ p := by
    have : (-1 : ℝ) < p := by nlinarith [mul_nonneg hx0 hqpos.le]
    have : (-1 : ℤ) < p := by exact_mod_cast this
    omega
  have hpq : p ≤ q := by
    have : (p : ℝ) < q + 1 := by nlinarith
    have : p < q + 1 := by exact_mod_cast this
    omega
  refine ⟨hp0, hpq, by linarith, by linarith, ?_⟩
  rw [show x - p / q = -((p - x * q) / q) by field_simp; ring, abs_neg, abs_div,
    abs_of_pos hqpos, div_le_iff₀ hqpos]
  have : |(p : ℝ) - x * q| ≤ r * R / 16 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

/-- A unimodular change of variables preserves coprimality. -/
theorem gcd_comb_eq_one {q₁ p₁ q₂ p₂ m n : ℤ} (hdet : q₁ * p₂ - p₁ * q₂ = 1)
    (h : Int.gcd m n = 1) : Int.gcd (m * p₁ + n * p₂) (m * q₁ + n * q₂) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at h ⊢
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v * q₁ - u * q₂, u * p₂ - v * p₁, ?_⟩
  linear_combination (u * m + v * n) * hdet + huv

/-- A unimodular change of variables is injective. -/
theorem comb_injective {q₁ p₁ q₂ p₂ m n m' n' : ℤ} (hdet : q₁ * p₂ - p₁ * q₂ = 1)
    (hq : m * q₁ + n * q₂ = m' * q₁ + n' * q₂) (hp : m * p₁ + n * p₂ = m' * p₁ + n' * p₂) :
    m = m' ∧ n = n' := by
  constructor
  · linear_combination p₂ * hq - q₂ * hp - (m - m') * hdet
  · linear_combination q₁ * hp - p₁ * hq - (n - n') * hdet

/-- Membership of an admissible fraction in the counted set of the contract. -/
theorem mem_target {R r x : ℝ} {p q : ℤ} (hp0 : 0 ≤ p) (hpq : p ≤ q) (hR2 : R / 2 ≤ q)
    (hqR : (q : ℝ) ≤ R) (hxpq : |x - p / q| ≤ r) (hpodd : Odd p) (hqodd : Odd q)
    (hcop : Int.gcd p q = 1) :
    (p.toNat, q.toNat) ∈ (Finset.range (⌊R⌋₊ + 1) ×ˢ Finset.range (⌊R⌋₊ + 1)).filter
      fun pq : ℕ × ℕ => Odd pq.1 ∧ Odd pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧ pq.1 ≤ pq.2 ∧
        R / 2 ≤ pq.2 ∧ |x - (pq.1 : ℝ) / pq.2| ≤ r := by
  have hpc : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hp0
  have hqc : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hp0.trans hpq)
  have hpR : (p : ℝ) ≤ R := (Int.cast_le.2 hpq).trans hqR
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor (by rw [hpc]; exact hpR)),
    Nat.lt_succ_of_le (Nat.le_floor (by rw [hqc]; exact hqR))⟩, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hpodd
    exact ⟨t.toNat, by omega⟩
  · obtain ⟨t, ht⟩ := hqodd
    exact ⟨t.toNat, by omega⟩
  · show Nat.gcd _ _ = 1
    rw [show p.toNat = p.natAbs by omega, show q.toNat = q.natAbs by omega]
    exact hcop
  · simp only
    rw [hqc]
    exact hR2
  · simp only
    rw [hpc, hqc]
    exact hxpq

/-- The conclusion of `card_coprime_parity_ge` with the location constant `98`. -/
def PrimitiveCount (L₀ : ℕ) : Prop :=
  ∀ L₁ L₂ : ℕ, L₀ ≤ L₂ → L₂ ≤ L₁ → ∀ j₀ k₀ α β : ℤ, (Odd α ∨ Odd β) →
    (∀ k ∈ Finset.Ico k₀ (k₀ + L₂), |((β + 2 * k : ℤ) : ℝ)| ≤ 98 * L₂) →
    (L₁ * L₂ : ℝ) / 2 ≤
      (((Finset.Ico j₀ (j₀ + L₁) ×ˢ Finset.Ico k₀ (k₀ + L₂)).filter
        fun jk : ℤ × ℤ => Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1).card : ℝ)

/-- **Redundant coverage outside the exceptional set** (Appendix I.3). With `A = 64 (L₀ + 2)`,
every `x ∈ [0, 1]` outside `exceptionalSet A R r` lies within `r` of at least `M / 16384`
reduced odd/odd fractions `p/q` with `p ≤ q` and `R/2 ≤ q ≤ R`. -/
theorem count_ge {L₀ : ℕ} (hL₀ : PrimitiveCount L₀) {R r x : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R⁻¹) (hAR : 64 * ((L₀ : ℝ) + 2) ≤ R) (hx : x ∈ Icc (0 : ℝ) 1)
    (hxU : x ∉ exceptionalSet (64 * ((L₀ : ℝ) + 2)) R r) :
    1 / 16384 * (r * R ^ 2) ≤
      (((Finset.range (⌊R⌋₊ + 1) ×ˢ Finset.range (⌊R⌋₊ + 1)).filter fun pq : ℕ × ℕ =>
          Odd pq.1 ∧ Odd pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧ pq.1 ≤ pq.2 ∧
            R / 2 ≤ pq.2 ∧ |x - (pq.1 : ℝ) / pq.2| ≤ r).card : ℝ) := by
  set A : ℝ := 64 * ((L₀ : ℝ) + 2) with hA_def
  set M := r * R ^ 2 with hM_def
  have hA : 0 < A := by positivity
  have hM : 0 < M := by positivity
  have hrR1 : r * R ≤ 1 := by
    calc r * R ≤ R⁻¹ * R := mul_le_mul_of_nonneg_right hrR hR.le
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hrRpos : 0 < r * R := by positivity
  set a : ℝ := R⁻¹ with ha
  set c : ℝ := -(x / (r * R)) with hc
  set e : ℝ := (r * R)⁻¹ with he
  have hD : a * e - 0 * c = M⁻¹ := by
    rw [ha, he, hM_def, zero_mul, sub_zero]
    field_simp
  have hDpos : 0 < a * e - 0 * c := by rw [hD]; positivity
  have hf : ∀ w : ℤ × ℤ, linForm a 0 w = w.1 / R := by
    intro w
    simp only [linForm, ha]
    ring
  have hg : ∀ w : ℤ × ℤ, linForm c e w = (w.2 - x * w.1) / (r * R) := by
    intro w
    simp only [linForm, hc, he]
    ring
  obtain ⟨w₁, w₂, hdet, hQle, hQprod⟩ := exists_reduced_basis a 0 c e hDpos
  rw [hD] at hQprod
  have hdet' : w₁.1 * w₂.2 - w₁.2 * w₂.1 = 1 := hdet
  have hw₁ : w₁ ≠ 0 := by
    intro h
    rw [h] at hdet'
    simp at hdet'
  set Q₁ := quadForm a 0 c e w₁ with hQ₁_def
  set Q₂ := quadForm a 0 c e w₂ with hQ₂_def
  -- there is no short lattice vector
  have hQ₁ : (A / M) ^ 2 ≤ Q₁ := by
    by_contra hlt
    rw [not_le] at hlt
    apply hxU
    have hf1 : |linForm a 0 w₁| < A / M := by
      refine abs_lt_of_sq_lt_sq ?_ (by positivity)
      have := sq_nonneg (linForm c e w₁)
      simp only [hQ₁_def, quadForm] at hlt
      linarith
    have hg1 : |linForm c e w₁| < A / M := by
      refine abs_lt_of_sq_lt_sq ?_ (by positivity)
      have := sq_nonneg (linForm a 0 w₁)
      simp only [hQ₁_def, quadForm] at hlt
      linarith
    rw [hf, abs_div, abs_of_pos hR, div_lt_iff₀ hR] at hf1
    rw [hg, abs_div, abs_of_pos hrRpos, div_lt_iff₀ hrRpos] at hg1
    refine mem_exceptionalSet hR hAR hx (q := w₁.1) (p := w₁.2) (by simpa using hw₁) ?_ ?_
    · calc |(w₁.1 : ℝ)| < A / M * R := hf1
        _ = A / (r * R) := by rw [hM_def]; field_simp
    · calc |(w₁.2 : ℝ) - x * w₁.1| < A / M * (r * R) := hg1
        _ = A / R := by rw [hM_def]; field_simp
  -- the lengths of the reduced basis
  have hQ₁0 : 0 ≤ Q₁ := quadForm_nonneg _ _ _ _ _
  have hQ₂0 : 0 ≤ Q₂ := quadForm_nonneg _ _ _ _ _
  set s₁ := √Q₁ with hs₁_def
  set s₂ := √Q₂ with hs₂_def
  have hs₁ : A / M ≤ s₁ := (Real.le_sqrt (by positivity) hQ₁0).2 hQ₁
  have hs₁pos : 0 < s₁ := lt_of_lt_of_le (by positivity) hs₁
  have hs₁₂ : s₁ ≤ s₂ := Real.sqrt_le_sqrt hQle
  have hs₂pos : 0 < s₂ := hs₁pos.trans_le hs₁₂
  have hprod : s₁ * s₂ * M < 2 := by
    have h1 : (s₁ * s₂) ^ 2 = Q₁ * Q₂ := by
      rw [mul_pow, Real.sq_sqrt hQ₁0, Real.sq_sqrt hQ₂0]
    have hMi : 0 < M⁻¹ ^ 2 := by positivity
    have h2 : (s₁ * s₂) ^ 2 < (2 / M) ^ 2 := by
      rw [h1]
      calc Q₁ * Q₂ ≤ 4 / 3 * M⁻¹ ^ 2 := hQprod
        _ < 4 * M⁻¹ ^ 2 := by linarith
        _ = (2 / M) ^ 2 := by ring
    have h3 := abs_lt_of_sq_lt_sq h2 (by positivity)
    rw [abs_of_pos (by positivity)] at h3
    rwa [lt_div_iff₀ hM] at h3
  set η : ℝ := 1 / 32 with hη
  set ρ₁ := η / s₁ with hρ₁
  set ρ₂ := η / s₂ with hρ₂
  have hs₂A : A * s₂ < 2 := by
    have h2 : A / M * s₂ ≤ s₁ * s₂ := mul_le_mul_of_nonneg_right hs₁ hs₂pos.le
    have h3 : A / M * s₂ * M ≤ s₁ * s₂ * M := mul_le_mul_of_nonneg_right h2 hM.le
    have h4 : A / M * s₂ * M = A * s₂ := by field_simp
    linarith
  have hρ₂big : (L₀ : ℝ) + 2 < ρ₂ := by
    rw [hρ₂, lt_div_iff₀ hs₂pos]
    have h5 : ((L₀ : ℝ) + 2) * s₂ * 64 = A * s₂ := by rw [hA_def]; ring
    rw [hη]
    linarith
  have hL₀0 : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _
  have hρ₁₂ : ρ₂ ≤ ρ₁ := div_le_div_of_nonneg_left (by norm_num) hs₁pos hs₁₂
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  set L₁ := ⌊ρ₁⌋₊ with hL₁
  set L₂ := ⌊ρ₂⌋₊ with hL₂
  have hL₀₂ : L₀ ≤ L₂ := Nat.le_floor (by linarith)
  have hL₂₁ : L₂ ≤ L₁ := Nat.floor_le_floor hρ₁₂
  have hL₂lt : ρ₂ < L₂ + 1 := Nat.lt_floor_add_one ρ₂
  have hL₁lt : ρ₁ < L₁ + 1 := Nat.lt_floor_add_one ρ₁
  -- the coefficient rectangle and the parity class
  set m₀ := 3 / 4 * linForm c e w₂ / (a * e - 0 * c) with hm₀
  set n₀ := -(3 / 4 * linForm c e w₁ / (a * e - 0 * c)) with hn₀
  set α : ℤ := w₂.2 - w₂.1 with hα
  set β : ℤ := w₁.1 - w₁.2 with hβ
  set j₀ : ℤ := ⌈(m₀ - ρ₁ - α) / 2⌉ with hj₀
  set k₀ : ℤ := ⌈(n₀ - ρ₂ - β) / 2⌉ with hk₀
  have hq_odd : ∀ j k : ℤ, (α + 2 * j) * w₁.1 + (β + 2 * k) * w₂.1 =
      2 * (j * w₁.1 + k * w₂.1) + 1 := by
    intro j k
    rw [hα, hβ]
    linear_combination hdet'
  have hp_odd : ∀ j k : ℤ, (α + 2 * j) * w₁.2 + (β + 2 * k) * w₂.2 =
      2 * (j * w₁.2 + k * w₂.2) + 1 := by
    intro j k
    rw [hα, hβ]
    linear_combination hdet'
  have hαβ : Odd α ∨ Odd β := by
    by_contra h
    rw [not_or, Int.not_odd_iff_even, Int.not_odd_iff_even] at h
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := h
    have h1 := hq_odd 0 0
    rw [hu, hv] at h1
    have : (2 : ℤ) ∣ 1 := ⟨u * w₁.1 + v * w₂.1, by linear_combination -h1⟩
    omega
  -- the location condition for the second coefficient
  have hsM : s₁ * M < 2 / s₂ := by
    rw [lt_div_iff₀ hs₂pos]
    linarith
  have hn₀le : |n₀| ≤ 48 * ρ₂ := by
    have hn₀' : n₀ = -(3 / 4 * linForm c e w₁ * M) := by
      rw [hn₀, hD]
      field_simp
    have hg₁ := abs_linForm_le_sqrt_right a 0 c e w₁
    rw [hn₀', abs_neg, abs_mul, abs_mul, abs_of_pos hM, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    rw [hρ₂, hη, show 48 * (1 / 32 / s₂) = 3 / 2 / s₂ by ring, le_div_iff₀ hs₂pos]
    have h1 : |linForm c e w₁| * (M * s₂) ≤ s₁ * (M * s₂) :=
      mul_le_mul_of_nonneg_right hg₁ (by positivity)
    nlinarith
  have hL₂1 : (1 : ℝ) ≤ L₂ := by
    have : 1 ≤ L₂ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hloc : ∀ k ∈ Finset.Ico k₀ (k₀ + L₂), |((β + 2 * k : ℤ) : ℝ)| ≤ 98 * L₂ := by
    intro k hk
    have h1 := abs_sub_le_of_mem_Ico hρ₂0 β k hk
    calc |((β + 2 * k : ℤ) : ℝ)| = |(((β + 2 * k : ℤ) : ℝ) - n₀) + n₀| := by ring_nf
      _ ≤ |((β + 2 * k : ℤ) : ℝ) - n₀| + |n₀| := abs_add_le _ _
      _ ≤ ρ₂ + 48 * ρ₂ := add_le_add h1 hn₀le
      _ ≤ 98 * L₂ := by linarith
  have hcount := hL₀ L₁ L₂ hL₀₂ hL₂₁ j₀ k₀ α β hαβ hloc
  -- the fractions attached to the coprime parameters
  set G := (Finset.Ico j₀ (j₀ + L₁) ×ˢ Finset.Ico k₀ (k₀ + L₂)).filter
    fun jk : ℤ × ℤ => Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1 with hG
  set qf : ℤ × ℤ → ℤ := fun jk => (α + 2 * jk.1) * w₁.1 + (β + 2 * jk.2) * w₂.1 with hqf
  set pf : ℤ × ℤ → ℤ := fun jk => (α + 2 * jk.1) * w₁.2 + (β + 2 * jk.2) * w₂.2 with hpf
  have hprop : ∀ jk ∈ G, 0 ≤ pf jk ∧ pf jk ≤ qf jk ∧ R / 2 ≤ qf jk ∧ (qf jk : ℝ) ≤ R ∧
      |x - pf jk / qf jk| ≤ r ∧ Int.gcd (pf jk) (qf jk) = 1 := by
    rintro ⟨j, k⟩ hjk
    obtain ⟨hmem, hgcd⟩ := Finset.mem_filter.1 hjk
    obtain ⟨hj, hk⟩ := Finset.mem_product.1 hmem
    have hm := abs_sub_le_of_mem_Ico hρ₁0 α j hj
    have hn := abs_sub_le_of_mem_Ico hρ₂0 β k hk
    have hm' : |((α + 2 * j : ℤ) : ℝ) - m₀| * s₁ ≤ η := by
      rw [hρ₁, le_div_iff₀ hs₁pos] at hm
      exact hm
    have hn' : |((β + 2 * k : ℤ) : ℝ) + 3 / 4 * linForm c e w₁ / (a * e - 0 * c)| * s₂ ≤ η := by
      rw [hρ₂, le_div_iff₀ hs₂pos] at hn
      rwa [hn₀, sub_neg_eq_add] at hn
    obtain ⟨h1, h2⟩ := comb_target a 0 c e hdet hDpos hm' hn'
    rw [hf] at h1
    rw [hg] at h2
    have h1' : |((qf (j, k) : ℤ) : ℝ) / R - 3 / 4| ≤ 1 / 16 := by
      have : 2 * η = 1 / 16 := by rw [hη]; norm_num
      rw [this] at h1
      simpa [comb, hqf] using h1
    have h2' : |(((pf (j, k) : ℤ) : ℝ) - x * qf (j, k)) / (r * R)| ≤ 1 / 16 := by
      have : 2 * η = 1 / 16 := by rw [hη]; norm_num
      rw [this] at h2
      simpa [comb, hqf, hpf] using h2
    obtain ⟨hp0, hpq, hR2, hqR, hxpq⟩ := fraction_props hR hr hrR1 hx h1' h2'
    exact ⟨hp0, hpq, hR2, hqR, hxpq, gcd_comb_eq_one hdet' hgcd⟩
  set T := (Finset.range (⌊R⌋₊ + 1) ×ˢ Finset.range (⌊R⌋₊ + 1)).filter fun pq : ℕ × ℕ =>
    Odd pq.1 ∧ Odd pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧ pq.1 ≤ pq.2 ∧
      R / 2 ≤ pq.2 ∧ |x - (pq.1 : ℝ) / pq.2| ≤ r with hT
  have hmaps : Set.MapsTo (fun jk => ((pf jk).toNat, (qf jk).toNat)) G T := by
    intro jk hjk
    obtain ⟨hp0, hpq, hR2, hqR, hxpq, hcop⟩ := hprop jk hjk
    exact mem_target hp0 hpq hR2 hqR hxpq ⟨_, hp_odd jk.1 jk.2⟩ ⟨_, hq_odd jk.1 jk.2⟩ hcop
  have hinj : Set.InjOn (fun jk => ((pf jk).toNat, (qf jk).toNat)) G := by
    intro jk hjk jk' hjk' heq
    obtain ⟨hp0, hpq, -⟩ := hprop jk hjk
    obtain ⟨hp0', hpq', -⟩ := hprop jk' hjk'
    simp only [Prod.mk.injEq] at heq
    have ep : pf jk = pf jk' := by omega
    have eq : qf jk = qf jk' := by omega
    obtain ⟨e1, e2⟩ := comb_injective hdet' eq ep
    exact Prod.ext (by omega) (by omega)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  -- the final count
  have hL₁' : ρ₁ / 2 ≤ L₁ := by linarith
  have hL₂' : ρ₂ / 2 ≤ L₂ := by linarith
  have hLL : ρ₁ / 2 * (ρ₂ / 2) ≤ (L₁ : ℝ) * L₂ :=
    mul_le_mul hL₁' hL₂' (by positivity) (by positivity)
  have hρρ : ρ₁ * ρ₂ = 1 / (1024 * (s₁ * s₂)) := by
    rw [hρ₁, hρ₂, hη]
    field_simp
    ring
  have hfin : 1 / 16384 * M ≤ 1 / (8192 * (s₁ * s₂)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc 1 / 16384 * M ≤ 1 / (8192 * (s₁ * s₂)) := hfin
    _ = ρ₁ / 2 * (ρ₂ / 2) / 2 := by
        rw [show ρ₁ / 2 * (ρ₂ / 2) / 2 = ρ₁ * ρ₂ / 8 by ring, hρρ]
        field_simp
        ring
    _ ≤ (L₁ * L₂ : ℝ) / 2 := by linarith
    _ ≤ (G.card : ℝ) := hcount
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard

end Favard.Coverage

namespace Favard

open Coverage

/-- **Redundant odd/odd rational coverage** (Appendix I.1): the contract `CoverageStatement`,
with `R₀ = A = 64 (L₀ + 2)`, `C = 4A²` and `c = 1/16384`. -/
theorem coverage : CoverageStatement := by
  obtain ⟨L₀, hL₀⟩ := card_coprime_parity_ge (K := 98) (by norm_num)
  refine ⟨64 * ((L₀ : ℝ) + 2), 1, 4 * (64 * ((L₀ : ℝ) + 2)) ^ 2, 1 / 16384, by positivity,
    by norm_num, ?_⟩
  intro R r hR₀ hr hrR _hM
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hR₀
  refine ⟨exceptionalSet (64 * ((L₀ : ℝ) + 2)) R r,
    volume_exceptionalSet_le (by positivity) hR hr, ?_⟩
  rintro x ⟨hx, hxU⟩
  exact count_ge hL₀ hR hr hrR hR₀ hx hxU

end Favard
