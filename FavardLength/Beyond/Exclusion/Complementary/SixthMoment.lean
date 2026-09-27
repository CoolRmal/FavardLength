import FavardLength.Beyond.Exclusion.Transform

/-!
# The exact odd-grid sixth moment of the cosine products

For an odd multiplier `h` and every depth `m`,

`∑_{p odd, p < 2·4^m} A_m(ph/2)^6 = (5/4)^m`

(Appendix H (17) with `r = 3`), where `A_m(x) = ∏_{j=1}^m cos(πx/4^j)` is `cosProd m x`.

Instead of the Fourier-digit argument of the manuscript we argue by induction on the depth,
splitting off the finest factor `cos(πx/4^{m+1})`: writing `p = p' + 2·4^m s` with `p'` odd,
`p' < 2·4^m` and `s < 4`, the old factors are unchanged (their arguments move by integer
multiples of `π`, and `cos²` is `π`-periodic), while the new factor sums to
`∑_{s<4} cos⁶(θ + πsh/4) = 5/4` for odd `h` (`sum_range_four_cos_pow_six`).

Since `|A(x)| ≤ |A_m(x)|`, this gives the moment bound (Appendix H (18))

`∑_{p odd, p ≤ B} |A(ph/2)|^6 ≤ (5/4) B^d`, `d = log₄(5/4)`, `B ≥ 1`,

uniformly in the odd multiplier `h` (`sum_absCosProd_pow_six_le`).
-/

open Real Finset

namespace Favard.Exclusion

/-! ### Elementary trigonometric identities -/

/-- `cos²` is `π`-periodic. -/
lemma cos_sq_add_nat_mul_pi (y : ℝ) (n : ℕ) : cos (y + n * π) ^ 2 = cos y ^ 2 := by
  rw [cos_add_nat_mul_pi, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow,
    one_mul]

/-- For odd `h`, a shift by `πh/2` exchanges `cos²` and `sin²`. -/
lemma cos_add_pi_mul_odd_div_two_sq {h : ℕ} (hh : Odd h) (y : ℝ) :
    cos (y + π * h / 2) ^ 2 = sin y ^ 2 := by
  obtain ⟨k, rfl⟩ := hh
  rw [show y + π * ((2 * k + 1 : ℕ) : ℝ) / 2 = (y + π / 2) + k * π by push_cast; ring,
    cos_sq_add_nat_mul_pi, cos_add_pi_div_two, neg_sq]

/-- For odd `h`, a shift by `πh/2` exchanges `sin²` and `cos²`. -/
lemma sin_add_pi_mul_odd_div_two_sq {h : ℕ} (hh : Odd h) (y : ℝ) :
    sin (y + π * h / 2) ^ 2 = cos y ^ 2 := by
  obtain ⟨k, rfl⟩ := hh
  rw [show y + π * ((2 * k + 1 : ℕ) : ℝ) / 2 = (y + π / 2) + k * π by push_cast; ring,
    sin_add_nat_mul_pi, sin_add_pi_div_two, mul_pow, ← pow_mul, mul_comm k 2, pow_mul,
    neg_one_sq, one_pow, one_mul]

/-- `cos⁶ y + sin⁶ y = 1 - (3/4) sin²(2y)`. -/
lemma cos_pow_six_add_sin_pow_six (y : ℝ) :
    cos y ^ 6 + sin y ^ 6 = 1 - 3 / 4 * sin (2 * y) ^ 2 := by
  rw [sin_two_mul]
  linear_combination ((sin y ^ 2 + cos y ^ 2) ^ 2 + (sin y ^ 2 + cos y ^ 2) + 1 -
    3 * cos y ^ 2 * sin y ^ 2) * sin_sq_add_cos_sq y

/-- **The new factor of the sixth moment**: for odd `h`,
`∑_{s<4} cos⁶(θ + πsh/4) = 5/4`. -/
lemma sum_range_four_cos_pow_six {h : ℕ} (hh : Odd h) (θ : ℝ) :
    ∑ s ∈ range 4, cos (θ + π * s * h / 4) ^ 6 = 5 / 4 := by
  set φ := θ + π * h / 4 with hφ
  have e2 : cos (θ + π * ((2 : ℕ) : ℝ) * h / 4) ^ 6 = sin θ ^ 6 := by
    rw [show θ + π * ((2 : ℕ) : ℝ) * h / 4 = θ + π * h / 2 by push_cast; ring,
      show (6 : ℕ) = 2 * 3 from rfl, pow_mul, cos_add_pi_mul_odd_div_two_sq hh, ← pow_mul]
  have e3 : cos (θ + π * ((3 : ℕ) : ℝ) * h / 4) ^ 6 = sin φ ^ 6 := by
    rw [show θ + π * ((3 : ℕ) : ℝ) * h / 4 = φ + π * h / 2 by rw [hφ]; push_cast; ring,
      show (6 : ℕ) = 2 * 3 from rfl, pow_mul, cos_add_pi_mul_odd_div_two_sq hh, ← pow_mul]
  have e1 : cos (θ + π * ((1 : ℕ) : ℝ) * h / 4) = cos φ := by
    rw [hφ]; push_cast; ring_nf
  have e0 : cos (θ + π * ((0 : ℕ) : ℝ) * h / 4) = cos θ := by
    push_cast; ring_nf
  have hsφ : sin (2 * φ) ^ 2 = cos (2 * θ) ^ 2 := by
    rw [show 2 * φ = 2 * θ + π * h / 2 by rw [hφ]; ring, sin_add_pi_mul_odd_div_two_sq hh]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [e0, e1, e2, e3]
  linear_combination cos_pow_six_add_sin_pow_six θ + cos_pow_six_add_sin_pow_six φ -
    3 / 4 * hsφ - 3 / 4 * sin_sq_add_cos_sq (2 * θ)

/-! ### Periodicity and the sum splitting -/

/-- The first `m` factors are unchanged, up to sign, by a shift of `4^m N`:
`A_m(x + 4^m N)² = A_m(x)²`. -/
lemma cosProd_add_four_pow_mul_sq (m N : ℕ) (x : ℝ) :
    cosProd m (x + 4 ^ m * N) ^ 2 = cosProd m x ^ 2 := by
  unfold cosProd
  rw [← prod_pow, ← prod_pow]
  refine prod_congr rfl fun j hj => ?_
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (mem_range.mp hj)
  rw [show π * (x + 4 ^ (j + r + 1) * N) / 4 ^ (j + 1) =
      π * x / 4 ^ (j + 1) + ((4 ^ r * N : ℕ) : ℝ) * π by
    push_cast
    rw [show j + r + 1 = (j + 1) + r by ring, pow_add]
    field_simp,
    cos_sq_add_nat_mul_pi]

/-- Splitting a sum over `[0, n b)` into `b` blocks of length `n`. -/
lemma sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n b : ℕ) :
    ∑ i ∈ range (n * b), f i = ∑ i ∈ range n, ∑ s ∈ range b, f (i + n * s) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    exact sum_congr rfl fun i _ => by rw [add_comm]

/-! ### The sixth moment -/

/-- **The exact odd-grid sixth moment** (Appendix H (17), `r = 3`): for odd `h`,
`∑_{i < 4^m} A_m((2i+1)h/2)^6 = (5/4)^m`, i.e. the sum of `A_m(ph/2)^6` over the odd
`p < 2·4^m` is `(5/4)^m`. -/
theorem sum_cosProd_pow_six {h : ℕ} (hh : Odd h) (m : ℕ) :
    ∑ i ∈ range (4 ^ m), cosProd m (((2 * i + 1 : ℕ) : ℝ) * h / 2) ^ 6 = (5 / 4) ^ m := by
  induction m with
  | zero => simp [cosProd_zero]
  | succ m ih =>
    rw [pow_succ 4 m, sum_range_mul_eq, pow_succ, ← ih, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    set x : ℝ := ((2 * i + 1 : ℕ) : ℝ) * h / 2 with hx
    have hshift : ∀ s : ℕ, ((2 * (i + 4 ^ m * s) + 1 : ℕ) : ℝ) * h / 2 =
        x + 4 ^ m * ((s * h : ℕ) : ℝ) := fun s => by rw [hx]; push_cast; ring
    have hterm : ∀ s : ℕ, cosProd (m + 1) (((2 * (i + 4 ^ m * s) + 1 : ℕ) : ℝ) * h / 2) ^ 6 =
        cosProd m x ^ 6 * cos (π * x / 4 ^ (m + 1) + π * s * h / 4) ^ 6 := fun s => by
      rw [hshift, cosProd_succ, mul_pow, show (6 : ℕ) = 2 * 3 from rfl, pow_mul,
        cosProd_add_four_pow_mul_sq, ← pow_mul]
      congr 3
      push_cast
      rw [pow_succ]
      field_simp
    simp_rw [hterm]
    rw [← mul_sum, sum_range_four_cos_pow_six hh]

/-- **The sixth-moment bound** (Appendix H (18)): for odd `h` and `B ≥ 1`,
`∑_{p odd, p ≤ B} |A(ph/2)|^6 ≤ (5/4) B^d` with `d = log₄(5/4)`. -/
theorem sum_absCosProd_pow_six_le {h : ℕ} (hh : Odd h) {B : ℝ} (hB : 1 ≤ B) :
    ∑ p ∈ (range (⌊B⌋₊ + 1)).filter Odd, absCosProd ((p : ℝ) * h / 2) ^ 6 ≤
      5 / 4 * B ^ sixthMomentDim := by
  set L := Nat.log 4 ⌊B⌋₊ with hL
  have hfloor : ⌊B⌋₊ ≠ 0 := (Nat.floor_pos.mpr hB).ne'
  have hlt : ⌊B⌋₊ < 4 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hsub : (range (⌊B⌋₊ + 1)).filter Odd ⊆
      (range (4 ^ (L + 1))).image fun i : ℕ => 2 * i + 1 := by
    intro p hp
    obtain ⟨hpB, i, rfl⟩ := mem_filter.mp hp
    rw [mem_range] at hpB
    exact mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩
  have hd : 0 ≤ sixthMomentDim := Real.logb_nonneg (by norm_num) (by norm_num)
  have h4L : ((4 : ℝ) ^ L) ≤ B := by
    have := Nat.pow_log_le_self 4 hfloor
    rw [← hL] at this
    calc ((4 : ℝ) ^ L) = ((4 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ B := Nat.floor_le (by linarith)
  have hpow : ((5 : ℝ) / 4) ^ L = ((4 : ℝ) ^ L) ^ sixthMomentDim := by
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num),
      sixthMomentDim, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  have hinj : Set.InjOn (fun i : ℕ => 2 * i + 1) (range (4 ^ (L + 1)) : Set ℕ) :=
    fun a _ b _ hab => by simp only at hab; omega
  calc ∑ p ∈ (range (⌊B⌋₊ + 1)).filter Odd, absCosProd ((p : ℝ) * h / 2) ^ 6
      ≤ ∑ p ∈ (range (4 ^ (L + 1))).image (fun i : ℕ => 2 * i + 1),
          absCosProd ((p : ℝ) * h / 2) ^ 6 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg (absCosProd_nonneg _) _
    _ = ∑ i ∈ range (4 ^ (L + 1)), absCosProd (((2 * i + 1 : ℕ) : ℝ) * h / 2) ^ 6 :=
        sum_image hinj
    _ ≤ ∑ i ∈ range (4 ^ (L + 1)), cosProd (L + 1) (((2 * i + 1 : ℕ) : ℝ) * h / 2) ^ 6 := by
        refine sum_le_sum fun i _ => ?_
        set y : ℝ := ((2 * i + 1 : ℕ) : ℝ) * h / 2
        calc absCosProd y ^ 6 ≤ |cosProd (L + 1) y| ^ 6 :=
              pow_le_pow_left₀ (absCosProd_nonneg y) (absCosProd_le (L + 1) y) 6
          _ = cosProd (L + 1) y ^ 6 := Even.pow_abs ⟨3, rfl⟩ _
    _ = (5 / 4) ^ (L + 1) := sum_cosProd_pow_six hh (L + 1)
    _ = 5 / 4 * ((4 : ℝ) ^ L) ^ sixthMomentDim := by rw [pow_succ, hpow, mul_comm]
    _ ≤ 5 / 4 * B ^ sixthMomentDim := by
        gcongr

end Favard.Exclusion
