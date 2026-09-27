import FavardLength.Beyond.Exclusion.Statements
import Mathlib.Algebra.Order.Chebyshev

/-!
# A noncancelling harmonic for positive weights

Proof of the sub-contract `Favard.Exclusion.HarmonicStatement` (Appendix G §3 of
`references/beyond/favard-beyond-quarter-complete.md`, the weighted positive-kernel lemma).

For nonnegative weights `w_i` with `W₂ = ∑ w_i² > 0` and real phases `θ_i`, write
`S(k) = ∑_i w_i e^{ikθ_i}`. Choose `d` with `2m ≤ 2^d ≤ 4m` and use the Riesz kernel
`K_d(x) = ∏_{r<d} (1 + cos(4^r x)) = ∑_e c(e) e^{iκ(e)x}`, the sum over digit vectors
`e ∈ {0, 1, -1}^d` with `c(e) = 2^{-|e|} ≥ 0` and `κ(e) = ∑_r e_r 4^r`. Then

* `∑_{i,l} w_i w_l K_d(θ_i - θ_l) = ∑_e c(e) |S(κ(e))|²`;
* the left side is at least its diagonal `2^d W₂`, since `K_d ≥ 0` and `K_d(0) = 2^d`;
* the term `e = 0` is `|S(0)|² ≤ (∑ w_i)² ≤ m W₂ ≤ 2^{d-1} W₂` (Cauchy–Schwarz);
* `∑_e c(e) = 2^d`.

Hence some `e ≠ 0` has `|S(κ(e))|² ≥ W₂/4`. The lowest nonzero digit gives `κ(e) = ±4^v h` with
`h` odd, and `3|κ(e)| < 4^d ≤ 16m²`, so `k = |κ(e)|` satisfies `k < 6m²`; finally
`|S(-k)| = |S(k)|` by conjugation.
-/

open Finset Complex
open scoped ComplexConjugate

namespace Favard.Exclusion

namespace Harmonic

/-- The signed digits `0, 1, -1` indexed by `Fin 3`. -/
def digit : Fin 3 → ℤ := ![0, 1, -1]

/-- The Fourier coefficients `1, 1/2, 1/2` of `1 + cos y` at the frequencies `0, 1, -1`. -/
noncomputable def digitCoef : Fin 3 → ℝ := ![1, 1 / 2, 1 / 2]

/-- The frequency `κ(e) = ∑_{r<d} e_r 4^r` of a digit vector `e ∈ {0, 1, -1}^d`. -/
def freq {d : ℕ} (e : Fin d → Fin 3) : ℤ :=
  ∑ r, digit (e r) * 4 ^ (r : ℕ)

/-- The Fourier coefficient `c(e) = ∏_{r<d} c_{e_r} = 2^{-|e|}` of the Riesz kernel `K_d` at the
digit vector `e`. -/
noncomputable def coef {d : ℕ} (e : Fin d → Fin 3) : ℝ :=
  ∏ r, digitCoef (e r)

/-- The Riesz kernel `K_d(x) = ∏_{r<d} (1 + cos(4^r x))`. -/
noncomputable def kernel (d : ℕ) (x : ℝ) : ℝ :=
  ∏ r : Fin d, (1 + Real.cos (4 ^ (r : ℕ) * x))

/-- The weighted phase sum `S(k) = ∑_i w_i e^{ikθ_i}` at a real frequency `k`. -/
noncomputable def phaseSum {m : ℕ} (w θ : Fin m → ℝ) (k : ℝ) : ℂ :=
  ∑ i, (w i : ℂ) * exp (↑(k * θ i) * I)

/-! ### The Riesz kernel and its Fourier expansion -/

lemma digitCoef_nonneg (j : Fin 3) : 0 ≤ digitCoef j := by
  fin_cases j <;> norm_num [digitCoef]

lemma coef_nonneg {d : ℕ} (e : Fin d → Fin 3) : 0 ≤ coef e :=
  prod_nonneg fun r _ => digitCoef_nonneg (e r)

@[simp] lemma coef_zero (d : ℕ) : coef (0 : Fin d → Fin 3) = 1 := by
  simp [coef, digitCoef]

@[simp] lemma freq_zero (d : ℕ) : freq (0 : Fin d → Fin 3) = 0 := by
  simp [freq, digit]

/-- The coefficients of `K_d` sum to `K_d(0) = 2^d`. -/
lemma sum_coef (d : ℕ) : ∑ e : Fin d → Fin 3, coef e = 2 ^ d := by
  simp only [coef]
  rw [← Fintype.prod_sum]
  norm_num [Fin.sum_univ_three, digitCoef]

lemma kernel_nonneg (d : ℕ) (x : ℝ) : 0 ≤ kernel d x :=
  prod_nonneg fun r _ => by linarith [Real.neg_one_le_cos (4 ^ (r : ℕ) * x)]

@[simp] lemma kernel_zero (d : ℕ) : kernel d 0 = 2 ^ d := by
  norm_num [kernel]

/-- `1 + cos y = 1 + e^{iy}/2 + e^{-iy}/2`. -/
lemma one_add_cos_eq (y : ℝ) :
    ((1 + Real.cos y : ℝ) : ℂ) =
      ∑ j : Fin 3, (digitCoef j : ℂ) * exp (↑((digit j : ℝ) * y) * I) := by
  rw [Fin.sum_univ_three]
  simp only [digitCoef, digit]
  push_cast
  simp [Complex.cos]
  ring_nf

/-- The Fourier expansion `K_d(x) = ∑_e c(e) e^{iκ(e)x}`. -/
lemma kernel_eq_sum (d : ℕ) (x : ℝ) :
    ((kernel d x : ℝ) : ℂ) =
      ∑ e : Fin d → Fin 3, (coef e : ℂ) * exp (↑((freq e : ℝ) * x) * I) := by
  rw [kernel, ofReal_prod]
  simp_rw [one_add_cos_eq]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [prod_mul_distrib, ← Complex.exp_sum, coef, freq, ofReal_prod]
  congr 2
  push_cast
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun r _ => ?_
  ring

/-! ### The frequencies: size and four-adic form -/

lemma freq_succ {d : ℕ} (e : Fin (d + 1) → Fin 3) :
    freq e = digit (e 0) + 4 * freq (Fin.tail e) := by
  rw [freq, Fin.sum_univ_succ, freq, mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, Fin.tail]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  ring

lemma odd_digit {j : Fin 3} (hj : j ≠ 0) : Odd (digit j) := by
  fin_cases j
  · exact absurd rfl hj
  · exact ⟨0, by simp [digit]⟩
  · exact ⟨-1, by simp [digit]⟩

/-- A nonzero digit vector has frequency `4^v h` with `h` odd (read off the lowest nonzero
digit). -/
lemma exists_freq_eq_four_pow_mul_odd :
    ∀ {d : ℕ} (e : Fin d → Fin 3), e ≠ 0 → ∃ (v : ℕ) (h : ℤ), Odd h ∧ freq e = 4 ^ v * h
  | 0, e, he => absurd (Subsingleton.elim e 0) he
  | d + 1, e, he => by
    by_cases h0 : e 0 = 0
    · have htail : Fin.tail e ≠ 0 := by
        intro ht
        apply he
        funext r
        refine Fin.cases h0 (fun r => ?_) r
        exact congrFun ht r
      obtain ⟨v, h, hh, hv⟩ := exists_freq_eq_four_pow_mul_odd (Fin.tail e) htail
      refine ⟨v + 1, h, hh, ?_⟩
      rw [freq_succ, h0, hv]
      simp [digit, pow_succ]
      ring
    · refine ⟨0, freq e, ?_, by ring⟩
      rw [freq_succ]
      exact (odd_digit h0).add_even ⟨2 * freq (Fin.tail e), by ring⟩

lemma isFourPowOdd_natAbs_freq {d : ℕ} {e : Fin d → Fin 3} (he : e ≠ 0) :
    IsFourPowOdd (freq e).natAbs := by
  obtain ⟨v, h, hh, hv⟩ := exists_freq_eq_four_pow_mul_odd e he
  exact ⟨v, h.natAbs, Int.natAbs_odd.2 hh, by rw [hv, Int.natAbs_mul, Int.natAbs_pow]; rfl⟩

lemma three_mul_sum_four_pow_add_one (d : ℕ) :
    3 * ∑ r ∈ range d, (4 : ℤ) ^ r + 1 = 4 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [sum_range_succ, pow_succ]; linarith

/-- `3|κ(e)| < 4^d`. -/
lemma three_mul_abs_freq_lt {d : ℕ} (e : Fin d → Fin 3) : 3 * |freq e| < 4 ^ d := by
  have hdig : ∀ j : Fin 3, |digit j| ≤ 1 := by
    intro j; fin_cases j <;> simp [digit]
  have hle : |freq e| ≤ ∑ r ∈ range d, (4 : ℤ) ^ r := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => (4 : ℤ) ^ r)]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    rw [abs_mul, abs_pow]
    norm_num
    exact hdig _
  linarith [three_mul_sum_four_pow_add_one d]

/-! ### Phase sums and the quadratic identity -/

lemma conj_phaseSum {m : ℕ} (w θ : Fin m → ℝ) (k : ℝ) :
    conj (phaseSum w θ k) = phaseSum w θ (-k) := by
  simp only [phaseSum, map_sum, map_mul, conj_ofReal, ← exp_conj, conj_I]
  refine sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

lemma norm_phaseSum_neg {m : ℕ} (w θ : Fin m → ℝ) (k : ℝ) :
    ‖phaseSum w θ (-k)‖ = ‖phaseSum w θ k‖ := by
  rw [← conj_phaseSum, RCLike.norm_conj]

lemma norm_phaseSum_abs {m : ℕ} (w θ : Fin m → ℝ) (k : ℝ) :
    ‖phaseSum w θ |k|‖ = ‖phaseSum w θ k‖ := by
  rcases abs_choice k with h | h <;> rw [h]
  exact norm_phaseSum_neg w θ k

lemma phaseSum_mul_conj {m : ℕ} (w θ : Fin m → ℝ) (k : ℝ) :
    ((‖phaseSum w θ k‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ l, (w i : ℂ) * w l * exp (↑(k * (θ i - θ l)) * I) := by
  push_cast
  rw [← mul_conj', conj_phaseSum, phaseSum, phaseSum, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
  rw [mul_mul_mul_comm, ← exp_add]
  push_cast
  ring_nf

/-- `∑_{i,l} w_i w_l K_d(θ_i - θ_l) = ∑_e c(e) |S(κ(e))|²`. -/
lemma sum_kernel_eq {m : ℕ} (w θ : Fin m → ℝ) (d : ℕ) :
    ∑ i, ∑ l, w i * w l * kernel d (θ i - θ l) =
      ∑ e : Fin d → Fin 3, coef e * ‖phaseSum w θ (freq e)‖ ^ 2 := by
  apply ofReal_injective
  simp only [ofReal_sum, ofReal_mul]
  simp_rw [kernel_eq_sum, phaseSum_mul_conj, mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun e _ => ?_
  ring

/-- The diagonal lower bound `∑_{i,l} w_i w_l K_d(θ_i - θ_l) ≥ 2^d W₂` for nonnegative
weights. -/
lemma le_sum_kernel {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (θ : Fin m → ℝ) (d : ℕ) :
    2 ^ d * ∑ i, w i ^ 2 ≤ ∑ i, ∑ l, w i * w l * kernel d (θ i - θ l) := by
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have hnn : ∀ l ∈ (univ : Finset (Fin m)), 0 ≤ w i * w l * kernel d (θ i - θ l) :=
    fun l _ => mul_nonneg (mul_nonneg (hw i) (hw l)) (kernel_nonneg d _)
  refine le_of_eq_of_le ?_ (single_le_sum hnn (mem_univ i))
  simp
  ring

/-- `|S(0)|² ≤ (∑ |w_i|)² ≤ m W₂`. -/
lemma norm_phaseSum_zero_sq_le {m : ℕ} (w θ : Fin m → ℝ) :
    ‖phaseSum w θ 0‖ ^ 2 ≤ m * ∑ i, w i ^ 2 := by
  have h1 : ‖phaseSum w θ 0‖ ≤ ∑ i, |w i| := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    simp
  have h2 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m))) (f := fun i => |w i|)
  simp only [sq_abs, card_univ, Fintype.card_fin] at h2
  calc ‖phaseSum w θ 0‖ ^ 2 ≤ (∑ i, |w i|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-! ### The choice of the kernel depth -/

/-- For `m ≥ 1` there is `d` with `2m ≤ 2^d ≤ 4m`. -/
lemma exists_two_pow_between {m : ℕ} (hm : m ≠ 0) : ∃ d : ℕ, 2 * m ≤ 2 ^ d ∧ 2 ^ d ≤ 4 * m := by
  refine ⟨Nat.log 2 m + 2, ?_, ?_⟩
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    rw [pow_succ] at h
    rw [pow_succ, pow_succ]
    omega
  · have h := Nat.pow_log_le_self 2 hm
    rw [pow_succ, pow_succ]
    omega

/-- The frequency `k = |κ(e)|` of a digit vector of depth `d` with `2^d ≤ 4m` is below `6m²`. -/
lemma natAbs_freq_lt {m d : ℕ} (hd : 2 ^ d ≤ 4 * m) (e : Fin d → Fin 3) :
    (freq e).natAbs < 6 * m ^ 2 := by
  have h3 : ((3 * (freq e).natAbs : ℕ) : ℤ) < ((4 ^ d : ℕ) : ℤ) := by
    push_cast
    exact three_mul_abs_freq_lt e
  have h4 : 4 ^ d ≤ 16 * m ^ 2 := by
    calc 4 ^ d = (2 ^ d) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (4 * m) ^ 2 := Nat.pow_le_pow_left hd 2
      _ = 16 * m ^ 2 := by ring
  have h5 : 3 * (freq e).natAbs < 4 ^ d := by exact_mod_cast h3
  omega

end Harmonic

open Harmonic in
/-- **(c) A noncancelling harmonic for positive weights** (Appendix G (8)): for nonnegative
weights with `W₂ = ∑ w_i² > 0` and real phases there is `k = 4^v h`, `h` odd, with `k < 6m²`
and `|∑_i w_i e^{ikθ_i}|² ≥ W₂/4`. -/
theorem harmonic : HarmonicStatement := by
  intro m w θ hw hW
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hW
  obtain ⟨d, hd1, hd2⟩ := exists_two_pow_between hm
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ e : Fin d → Fin 3, e ≠ 0 →
      ‖phaseSum w θ (freq e)‖ ^ 2 < (∑ i, w i ^ 2) / 4 := by
    intro e he
    have hlt : ((freq e).natAbs : ℝ) < 6 * (m : ℝ) ^ 2 := by
      exact_mod_cast natAbs_freq_lt hd2 e
    have h := hcon _ (isFourPowOdd_natAbs_freq he) hlt
    change ‖phaseSum w θ ((freq e).natAbs : ℝ)‖ ^ 2 < _ at h
    rwa [Nat.cast_natAbs, Int.cast_abs, norm_phaseSum_abs] at h
  have hlow := le_sum_kernel hw θ d
  rw [sum_kernel_eq, ← add_sum_erase (univ : Finset (Fin d → Fin 3)) _ (mem_univ 0),
    coef_zero, freq_zero, Int.cast_zero, one_mul] at hlow
  have hzero := norm_phaseSum_zero_sq_le w θ
  have hrest : ∑ e ∈ (univ : Finset (Fin d → Fin 3)).erase 0,
      coef e * ‖phaseSum w θ (freq e)‖ ^ 2 ≤
      2 ^ d * ((∑ i, w i ^ 2) / 4) := by
    calc _ ≤ ∑ e ∈ univ.erase 0, coef e * ((∑ i, w i ^ 2) / 4) :=
          sum_le_sum fun e he =>
            mul_le_mul_of_nonneg_left (hsmall e (ne_of_mem_erase he)).le (coef_nonneg e)
      _ ≤ ∑ e, coef e * ((∑ i, w i ^ 2) / 4) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun e _ _ => mul_nonneg (coef_nonneg e) (by positivity)
      _ = 2 ^ d * ((∑ i, w i ^ 2) / 4) := by rw [← sum_mul, sum_coef]
  have hd1' : (2 * m : ℝ) ≤ 2 ^ d := by exact_mod_cast hd1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  nlinarith [mul_le_mul_of_nonneg_right hd1' hW.le, mul_pos hmpos hW]

end Favard.Exclusion
