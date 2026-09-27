import FavardLength.Beyond.Exclusion.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

/-!
# The tangent sum near integers of even two-adic valuation

Let `α_j = π/4^{j+1}`. The zeros of the factor `cos(α_j x)` of `A_n(x) = ∏_{j<n} cos(α_j x)` are
the points `4^{j+1}(ℓ + 1/2) = 2·4^j(2ℓ + 1)`, integers of odd two-adic valuation. Hence an
integer `x₀ = 4^v h`, `h` odd, has distance at least one from each of them, and for real `x`
with `|x - x₀| ≤ 1/4` we get `|cos(α_j x)| ≥ (3/2)/4^{j+1}` (`Exclusion.abs_cos_ge`).

We then bound the **tangent sum** (Appendix G (4))

`tanSum n x = ∑_{j<n} α_j (1 + |tan(α_j x)|) ≤ 10 log(2 + x₀)`,

uniformly in `n` (`Exclusion.tanSum_le`): each tangent term is at most `2π/3` by the cosine
lower bound, and once `4^j > x₀` the angle is at most `π/4`, so the tangent is at most twice the
angle and the coefficients `α_j` are summable. There are only `log₄ x₀ + 1` earlier levels.
-/

open Real

namespace Favard.Exclusion

/-- The tangent sum `∑_{j<n} (π/4^{j+1}) (1 + |tan(πx/4^{j+1})|)` of Appendix G (4), the
logarithmic-derivative bound for `A_n` at the real point `x`. -/
noncomputable def tanSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, π / 4 ^ (j + 1) * (1 + |Real.tan (π * x / 4 ^ (j + 1))|)

lemma tanSum_nonneg (n : ℕ) (x : ℝ) : 0 ≤ tanSum n x :=
  Finset.sum_nonneg fun _ _ => by positivity

/-! ### Distance from the zeros -/

/-- An integer of even two-adic valuation, `4^v h` with `h` odd, is not of the form
`2·4^j(2ℓ + 1)`. -/
lemma four_pow_mul_odd_ne (v h j : ℕ) (hh : Odd h) (ℓ : ℤ) :
    (4 : ℤ) ^ v * h ≠ 2 * 4 ^ j * (2 * ℓ + 1) := by
  intro heq
  obtain ⟨c, rfl⟩ := hh
  rcases le_or_gt v j with hvj | hvj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvj
    have h4 : (4 : ℤ) ^ v ≠ 0 := by positivity
    have e : (((2 * c + 1 : ℕ) : ℤ)) = 2 * (4 ^ d * (2 * ℓ + 1)) := by
      apply mul_left_cancel₀ h4
      rw [heq, pow_add]
      ring
    push_cast at e
    generalize (4 : ℤ) ^ d * (2 * ℓ + 1) = X at e
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hvj
    have h4 : (2 : ℤ) * 4 ^ j ≠ 0 := by positivity
    have e : 2 * (4 ^ d * ((2 * c + 1 : ℕ) : ℤ)) = 2 * ℓ + 1 := by
      apply mul_left_cancel₀ h4
      rw [← heq]
      ring
    generalize (4 : ℤ) ^ d * ((2 * c + 1 : ℕ) : ℤ) = X at e
    omega

/-- An integer of even two-adic valuation has distance at least one from every zero
`4^{j+1}(ℓ + 1/2)` of `cos(πx/4^{j+1})`. -/
lemma one_le_abs_sub_zero (v h j : ℕ) (hh : Odd h) (ℓ : ℤ) :
    1 ≤ |(4 ^ v * h : ℝ) - 4 ^ (j + 1) * (ℓ + 1 / 2)| := by
  have hne : (4 : ℤ) ^ v * h - 2 * 4 ^ j * (2 * ℓ + 1) ≠ 0 :=
    sub_ne_zero.mpr (four_pow_mul_odd_ne v h j hh ℓ)
  have e : (4 ^ v * h : ℝ) - 4 ^ (j + 1) * (ℓ + 1 / 2) =
      (((4 : ℤ) ^ v * h - 2 * 4 ^ j * (2 * ℓ + 1) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [e]
  exact_mod_cast Int.one_le_abs hne

/-- If `s` has distance at least `d` from every half-integer, then `|cos(πs)| ≥ 2d`. -/
lemma two_mul_le_abs_cos_pi_mul {s d : ℝ} (h : ∀ ℓ : ℤ, d ≤ |s - (ℓ + 1 / 2)|) :
    2 * d ≤ |Real.cos (π * s)| := by
  set u : ℝ := s - ⌊s⌋ - 1 / 2 with hu
  have hu1 : |u| ≤ 1 / 2 := by
    have := Int.floor_le s
    have := Int.lt_floor_add_one s
    rw [abs_le]
    constructor <;> linarith
  have hdu : d ≤ |u| := by
    have := h ⌊s⌋
    rwa [show s - ((⌊s⌋ : ℝ) + 1 / 2) = u by rw [hu]; ring] at this
  have hcos : Real.cos (π * s) = (-1) ^ ⌊s⌋ * -Real.sin (π * u) := by
    rw [← Real.cos_add_pi_div_two, ← Real.cos_add_int_mul_pi]
    congr 1
    rw [hu]
    ring
  have hsin : 2 * |u| ≤ |Real.sin (π * u)| := by
    have h1 := Real.mul_le_sin (x := π * |u|) (by positivity)
      (by nlinarith [pi_pos, abs_nonneg u])
    have h2 : Real.sin (π * |u|) ≤ |Real.sin (π * u)| := by
      rcases abs_cases u with ⟨hu', _⟩ | ⟨hu', _⟩
      · rw [hu']
        exact le_abs_self _
      · rw [hu', mul_neg, Real.sin_neg]
        exact neg_le_abs _
    have h3 : 2 / π * (π * |u|) = 2 * |u| := by field_simp
    linarith
  rw [hcos, abs_mul, abs_neg]
  simp only [abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  linarith

/-- **Cosine lower bound near an integer of even valuation**: if `|x - 4^v h| ≤ 1/4` with `h`
odd, then `|cos(πx/4^{j+1})| ≥ (3/2)/4^{j+1}`. -/
lemma abs_cos_ge (v h j : ℕ) (hh : Odd h) {x : ℝ} (hx : |x - 4 ^ v * h| ≤ 1 / 4) :
    3 / 2 / 4 ^ (j + 1) ≤ |Real.cos (π * x / 4 ^ (j + 1))| := by
  have hm : (0 : ℝ) < 4 ^ (j + 1) := by positivity
  have key := two_mul_le_abs_cos_pi_mul (s := x / 4 ^ (j + 1)) (d := 3 / 4 / 4 ^ (j + 1))
    fun ℓ => by
      have h1 := one_le_abs_sub_zero v h j hh ℓ
      have e : x / 4 ^ (j + 1) - (ℓ + 1 / 2) = (x - 4 ^ (j + 1) * (ℓ + 1 / 2)) / 4 ^ (j + 1) := by
        field_simp
      rw [e, abs_div, abs_of_pos hm]
      gcongr
      have := abs_sub_abs_le_abs_sub ((4 ^ v * h : ℝ) - 4 ^ (j + 1) * (ℓ + 1 / 2))
        (x - 4 ^ (j + 1) * (ℓ + 1 / 2))
      rw [show (4 ^ v * h : ℝ) - 4 ^ (j + 1) * (ℓ + 1 / 2) - (x - 4 ^ (j + 1) * (ℓ + 1 / 2)) =
        -(x - 4 ^ v * h) by ring, abs_neg] at this
      linarith
  rw [mul_div_assoc]
  convert key using 1
  ring

lemma cos_ne_zero_of_near (v h j : ℕ) (hh : Odd h) {x : ℝ} (hx : |x - 4 ^ v * h| ≤ 1 / 4) :
    Real.cos (π * x / 4 ^ (j + 1)) ≠ 0 := by
  have := abs_cos_ge v h j hh hx
  have hpos : (0 : ℝ) < 3 / 2 / 4 ^ (j + 1) := by positivity
  intro h0
  rw [h0, abs_zero] at this
  linarith

/-! ### The tangent terms -/

/-- `|tan θ| ≤ 1/|cos θ|`. -/
lemma abs_tan_le_inv_abs_cos (θ : ℝ) : |Real.tan θ| ≤ 1 / |Real.cos θ| := by
  rw [Real.tan_eq_sin_div_cos, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one θ) (abs_nonneg _)

/-- Every tangent term near an integer of even valuation is at most `3`. -/
lemma tan_term_le_three (v h j : ℕ) (hh : Odd h) {x : ℝ} (hx : |x - 4 ^ v * h| ≤ 1 / 4) :
    π / 4 ^ (j + 1) * |Real.tan (π * x / 4 ^ (j + 1))| ≤ 3 := by
  have hc := abs_cos_ge v h j hh hx
  have hm : (0 : ℝ) < 4 ^ (j + 1) := by positivity
  have hpos : (0 : ℝ) < 3 / 2 / 4 ^ (j + 1) := by positivity
  have ht : |Real.tan (π * x / 4 ^ (j + 1))| ≤ 2 / 3 * 4 ^ (j + 1) := by
    refine (abs_tan_le_inv_abs_cos _).trans ?_
    rw [div_le_iff₀ (hpos.trans_le hc)]
    calc (1 : ℝ) = 2 / 3 * 4 ^ (j + 1) * (3 / 2 / 4 ^ (j + 1)) := by field_simp
      _ ≤ 2 / 3 * 4 ^ (j + 1) * |Real.cos (π * x / 4 ^ (j + 1))| := by gcongr
  calc π / 4 ^ (j + 1) * |Real.tan (π * x / 4 ^ (j + 1))|
      ≤ π / 4 ^ (j + 1) * (2 / 3 * 4 ^ (j + 1)) := by gcongr
    _ = 2 / 3 * π := by field_simp
    _ ≤ 3 := by nlinarith [pi_le_four]

/-- `|tan θ| ≤ 2|θ|` for `|θ| ≤ 1`. -/
lemma abs_tan_le_two_mul {θ : ℝ} (hθ : |θ| ≤ 1) : |Real.tan θ| ≤ 2 * |θ| := by
  have hc : 1 / 2 ≤ Real.cos θ := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    have : θ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg θ]
    linarith
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos (a := Real.cos θ) (by linarith),
    div_le_iff₀ (by linarith)]
  nlinarith [Real.abs_sin_le_abs (x := θ), abs_nonneg θ]

/-- The geometric sum `∑_{j<n} 4^{-(j+1)} ≤ 1/3`. -/
lemma sum_inv_four_pow_le (n : ℕ) : ∑ j ∈ Finset.range n, (1 : ℝ) / 4 ^ (j + 1) ≤ 1 / 3 := by
  have e : ∀ n : ℕ, ∑ j ∈ Finset.range n, (1 : ℝ) / 4 ^ (j + 1) = (1 - 1 / 4 ^ n) / 3 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring
  rw [e]
  have : (0 : ℝ) ≤ 1 / 4 ^ n := by positivity
  linarith

/-- `1 ≤ log(2 + x)` for `x ≥ 1`, since `e < 3`. -/
lemma one_le_log_two_add {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (2 + x) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **The tangent sum** (Appendix G (4)): near an integer `x₀ = 4^v h ≥ 1` of even two-adic
valuation, `∑_{j<n} (π/4^{j+1})(1 + |tan(πx/4^{j+1})|) ≤ 10 log(2 + x₀)`, uniformly in `n`. -/
theorem tanSum_le (n v h : ℕ) (hh : Odd h) {x : ℝ} (hx : |x - 4 ^ v * h| ≤ 1 / 4) :
    tanSum n x ≤ 10 * Real.log (2 + 4 ^ v * h) := by
  set m : ℕ := 4 ^ v * h with hmdef
  have hm0 : m ≠ 0 := by
    rw [hmdef]
    exact mul_ne_zero (by positivity) (Nat.pos_of_ne_zero (by rintro rfl; simp at hh)).ne'
  have hmR : ((m : ℕ) : ℝ) = 4 ^ v * h := by rw [hmdef]; push_cast; ring
  rw [← hmR] at hx ⊢
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  set J : ℕ := Nat.log 4 m + 1 with hJ
  have hJm : (m : ℝ) + 1 ≤ 4 ^ J := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) m
    exact_mod_cast this
  -- the term bound
  have hterm : ∀ j ∈ Finset.range n, π / 4 ^ (j + 1) * (1 + |Real.tan (π * x / 4 ^ (j + 1))|) ≤
      3 * π * (1 / 4 ^ (j + 1)) + if j < J then 3 else 0 := by
    intro j _
    have hα : (0 : ℝ) ≤ π / 4 ^ (j + 1) := by positivity
    split_ifs with hj
    · have := tan_term_le_three v h j hh (hmR ▸ hx)
      have h3 : π / 4 ^ (j + 1) ≤ 3 * π * (1 / 4 ^ (j + 1)) := by
        rw [mul_one_div]
        gcongr
        linarith [pi_pos]
      calc π / 4 ^ (j + 1) * (1 + |Real.tan (π * x / 4 ^ (j + 1))|)
          = π / 4 ^ (j + 1) + π / 4 ^ (j + 1) * |Real.tan (π * x / 4 ^ (j + 1))| := by ring
        _ ≤ 3 * π * (1 / 4 ^ (j + 1)) + 3 := by linarith
    · push Not at hj
      have hθ : |π * x / 4 ^ (j + 1)| ≤ π / 4 := by
        have hx' : |x| ≤ m + 1 := by
          have := abs_sub_abs_le_abs_sub x m
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ m)] at this
          linarith
        have h4 : (4 : ℝ) * (m + 1) ≤ 4 ^ (j + 1) := by
          rw [pow_succ]
          have : (4 : ℝ) ^ J ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj
          nlinarith
        rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (j + 1)),
          div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pi_pos]
      have ht := abs_tan_le_two_mul (hθ.trans (by linarith [pi_le_four]))
      have ht2 : 1 + |Real.tan (π * x / 4 ^ (j + 1))| ≤ 3 := by
        nlinarith [pi_le_four]
      calc π / 4 ^ (j + 1) * (1 + |Real.tan (π * x / 4 ^ (j + 1))|)
          ≤ π / 4 ^ (j + 1) * 3 := by gcongr
        _ = 3 * π * (1 / 4 ^ (j + 1)) + 0 := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgeo := sum_inv_four_pow_le n
  have hcount : ∑ j ∈ Finset.range n, (if j < J then (3 : ℝ) else 0) ≤ 3 * J := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.filter (fun j => j < J) (Finset.range n)).card ≤ J := by
      calc (Finset.filter (fun j => j < J) (Finset.range n)).card
          ≤ (Finset.range J).card := by
            refine Finset.card_le_card fun j hj => ?_
            simp only [Finset.mem_filter] at hj
            exact Finset.mem_range.mpr hj.2
        _ = J := Finset.card_range J
    have : ((Finset.filter (fun j => j < J) (Finset.range n)).card : ℝ) ≤ J := by
      exact_mod_cast this
    linarith
  -- `J ≤ log m + 1`
  have hlogm : (Nat.log 4 m : ℝ) ≤ Real.log m := by
    have h1 : ((4 ^ Nat.log 4 m : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.pow_log_le_self 4 hm0
    have h2 := Real.log_le_log (by positivity) h1
    push_cast at h2
    rw [Real.log_pow] at h2
    have h4 : 1 ≤ Real.log 4 := by
      have := one_le_log_two_add (x := 2) (by norm_num)
      norm_num at this
      exact this
    have hn0 : (0 : ℝ) ≤ Nat.log 4 m := Nat.cast_nonneg _
    nlinarith
  have hlog2 : Real.log m ≤ Real.log (2 + m) := Real.log_le_log (by positivity) (by linarith)
  have hL := one_le_log_two_add hm1
  have hJR : (J : ℝ) = Nat.log 4 m + 1 := by rw [hJ]; push_cast; ring
  have hpi : 3 * π * ∑ j ∈ Finset.range n, (1 : ℝ) / 4 ^ (j + 1) ≤ 4 := by
    nlinarith [pi_pos, pi_le_four]
  linarith

/-- Near an integer of even valuation no factor of `A_n` vanishes. -/
lemma cos_ne_zero_of_isFourPowOdd {m : ℕ} (hm : IsFourPowOdd m) {x : ℝ} (hx : |x - m| ≤ 1 / 4)
    (j : ℕ) : Real.cos (π * x / 4 ^ (j + 1)) ≠ 0 := by
  obtain ⟨v, h, hh, rfl⟩ := hm
  push_cast at hx
  exact cos_ne_zero_of_near v h j hh hx

/-- The tangent sum near `m` with `IsFourPowOdd m`: `tanSum n x ≤ 10 log(2 + m)`. -/
lemma tanSum_le_of_isFourPowOdd (n : ℕ) {m : ℕ} (hm : IsFourPowOdd m) {x : ℝ}
    (hx : |x - m| ≤ 1 / 4) : tanSum n x ≤ 10 * Real.log (2 + m) := by
  obtain ⟨v, h, hh, rfl⟩ := hm
  push_cast at hx ⊢
  exact tanSum_le n v h hh hx

end Favard.Exclusion
