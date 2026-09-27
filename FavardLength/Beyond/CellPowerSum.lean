import FavardLength.Beyond.Statements
import FavardLength.Beyond.CellPowerSum.Certificate
import FavardLength.Beyond.CellPowerSum.Transfer
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The improved cell-power sum (Appendix B.1, discrete form)

We prove `Favard.cellPowerSum : CellPowerSumStatement (1/2 - 1/10^7) (3071/10000)`, and more
generally `Favard.CellPowerSum.cellPowerSum_of`: for `1/4 ≤ s ≤ 1/2` and
`261313/400000 + (1 - 2s) ≤ 4^{-β}`, `CellPowerSumStatement s β` holds. No complex analysis is
used: the sampling inequality of B.1.2 is replaced by a transfer operator on the 4-adic grid of
cell centres (`FavardLength.Beyond.CellPowerSum.Transfer`).

Write `L = 4^m`, `c_i = (i + 1/2)π/L` and `ε_k = (π/2) 4^k/L` for `k < m`.

* **Majorants.** For `w ∈ I_i = [iπ/L, (i+1)π/L]`, `|4^k w - 4^k c_i| ≤ ε_k`, and `cos` is
  `1`-Lipschitz, so `|cos(4^k w)| ≤ |cos(4^k c_i)| + ε_k`. Hence `D_m(w)² ≤ b_i` with
  `b_i = ∏_{k<m} (|cos(4^k c_i)| + ε_k)² > 0`.
* **Powers.** For `a = 2s ∈ [1/2, 1]`: `(x + y)^a ≤ x^a + y^a`, and `x^a ≤ a x + (1 - a) ≤ x + κ`
  with `κ = 1 - 2s` (weighted AM-GM against `1`). Hence
  `b_i^s ≤ ∏_k (|cos(4^k c_i)| + κ + ε_k^{2s})`.
* **Transfer.** With `r = 261313/400000 ≥ ρ_* = √(4 + 2√2)/4`, the transfer bound gives
  `∑_i b_i^s ≤ 4^m ∏_k (q + ε_k^{2s})`, `q = r + κ`.
* **Tails.** `∏_k (q + e_k) ≤ q^m exp(∑_k e_k/q)`, and `ε_k^{2s} ≤ √ε_k ≤ 2 · 2^k/2^m` (as
  `ε_k ≤ 1` and `2s ≥ 1/2`), so `∑_k ε_k^{2s} ≤ 2`.
* **Certificate.** `q ≤ 4^{-β}` gives `4^m q^m ≤ (4^m)^{1-β}`; for `s = 1/2 - 10⁻⁷`,
  `β = 3071/10000` this is `0.6532827 ≤ 653285/10^6 ≤ 4^{-β}` (`CellPowerSum.certificate`).
-/

open Finset Real

namespace Favard

namespace CellPowerSum

/-- Weighted AM-GM against `1`: `x^a ≤ a x + (1 - a) ≤ x + (1 - a)` for `x ≥ 0`, `0 ≤ a ≤ 1`. -/
lemma rpow_le_add_one_sub {x a : ℝ} (hx : 0 ≤ x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    x ^ a ≤ x + (1 - a) := by
  have h := geom_mean_le_arith_mean2_weighted ha0 (sub_nonneg.2 ha1) hx zero_le_one
    (by ring : a + (1 - a) = 1)
  rw [one_rpow, mul_one, mul_one] at h
  nlinarith

/-- `∏_{k<m} (q + e_k) ≤ q^m exp(∑_{k<m} e_k / q)` for `q > 0`, `e_k ≥ 0`. -/
lemma prod_add_le_pow_mul_exp {q : ℝ} (hq : 0 < q) (m : ℕ) (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) :
    ∏ k ∈ range m, (q + e k) ≤ q ^ m * exp ((∑ k ∈ range m, e k) / q) := by
  calc ∏ k ∈ range m, (q + e k) ≤ ∏ k ∈ range m, (q * exp (e k / q)) := by
        refine prod_le_prod₀ (fun k _ => by linarith [he k]) fun k _ => ?_
        have h2 : q + e k = q * (e k / q + 1) := by
          field_simp
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left (add_one_le_exp _) hq.le
    _ = q ^ m * exp ((∑ k ∈ range m, e k) / q) := by
        rw [prod_mul_distrib, prod_const, card_range, ← exp_sum, sum_div]

/-- The geometric sum `∑_{k<m} 2^k ≤ 2^m`. -/
lemma sum_two_pow_le (m : ℕ) : ∑ k ∈ range m, (2 : ℝ) ^ k ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ]
    linarith

/-- `(2^k)² = 4^k`. -/
lemma sq_two_pow (k : ℕ) : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The radii `ε_k = (π/2) 4^k/4^m` satisfy `∑_{k<m} ε_k^a ≤ 2` for `a ≥ 1/2`. -/
lemma sum_rpow_radius_le {a : ℝ} (ha : 1 / 2 ≤ a) (m : ℕ) :
    ∑ k ∈ range m, (π / 2 * 4 ^ k / 4 ^ m) ^ a ≤ 2 := by
  have key : ∀ k ∈ range m, (π / 2 * 4 ^ k / 4 ^ m : ℝ) ^ a ≤ 2 * 2 ^ k / 2 ^ m := by
    intro k hk
    have hkm : k + 1 ≤ m := mem_range.1 hk
    have h4 : (4 : ℝ) ^ k * 4 ≤ 4 ^ m := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) hkm
    have hε0 : 0 < (π / 2 * 4 ^ k / 4 ^ m : ℝ) := by positivity
    have hε4 : (π / 2 * 4 ^ k / 4 ^ m : ℝ) ≤ 4 * 4 ^ k / 4 ^ m := by
      gcongr
      linarith [pi_le_four]
    have hε1 : (π / 2 * 4 ^ k / 4 ^ m : ℝ) ≤ 1 := by
      refine hε4.trans ?_
      rw [div_le_one (by positivity)]
      linarith
    calc (π / 2 * 4 ^ k / 4 ^ m : ℝ) ^ a ≤ (π / 2 * 4 ^ k / 4 ^ m) ^ (1 / 2 : ℝ) :=
          rpow_le_rpow_of_exponent_ge hε0 hε1 ha
      _ = √(π / 2 * 4 ^ k / 4 ^ m) := (sqrt_eq_rpow _).symm
      _ ≤ 2 * 2 ^ k / 2 ^ m := by
        rw [sqrt_le_iff]
        refine ⟨by positivity, hε4.trans (le_of_eq ?_)⟩
        rw [div_pow, mul_pow, sq_two_pow, sq_two_pow]
        norm_num
  calc ∑ k ∈ range m, (π / 2 * 4 ^ k / 4 ^ m : ℝ) ^ a ≤ ∑ k ∈ range m, 2 * 2 ^ k / 2 ^ m :=
        sum_le_sum key
    _ = 2 * (∑ k ∈ range m, (2 : ℝ) ^ k) / 2 ^ m := by rw [← sum_div, ← mul_sum]
    _ ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith [sum_two_pow_le m]

/-- A point of the cell `I_i` is within half a cell width of the centre `c_i`. -/
lemma abs_sub_centre_le {m i : ℕ} {w : ℝ}
    (hw : w ∈ Set.Icc ((i : ℝ) * π / 4 ^ m) ((i + 1) * π / 4 ^ m)) :
    |w - centre m i| ≤ π / 4 ^ m / 2 := by
  obtain ⟨h1, h2⟩ := hw
  rw [mul_div_assoc] at h1 h2
  unfold centre
  rw [mul_div_assoc, abs_le]
  constructor <;> nlinarith

/-- The cosine factors on a cell: `|cos(4^k w)| ≤ |cos(4^k c_i)| + (π/2) 4^k/4^m`. -/
lemma abs_cos_le_abs_cos_centre_add {m i k : ℕ} {w : ℝ}
    (hw : w ∈ Set.Icc ((i : ℝ) * π / 4 ^ m) ((i + 1) * π / 4 ^ m)) :
    |cos (4 ^ k * w)| ≤ |cos (4 ^ k * centre m i)| + π / 2 * 4 ^ k / 4 ^ m := by
  calc |cos (4 ^ k * w)| ≤
        |cos (4 ^ k * centre m i)| + |cos (4 ^ k * w) - cos (4 ^ k * centre m i)| := by
        linarith [abs_sub_abs_le_abs_sub (cos (4 ^ k * w)) (cos (4 ^ k * centre m i))]
    _ ≤ |cos (4 ^ k * centre m i)| + |4 ^ k * w - 4 ^ k * centre m i| := by
        linarith [abs_cos_sub_cos_le (4 ^ k * w) (4 ^ k * centre m i)]
    _ ≤ |cos (4 ^ k * centre m i)| + π / 2 * 4 ^ k / 4 ^ m := by
        gcongr
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k)]
        calc (4 : ℝ) ^ k * |w - centre m i| ≤ 4 ^ k * (π / 4 ^ m / 2) := by
              gcongr
              exact abs_sub_centre_le hw
          _ = π / 2 * 4 ^ k / 4 ^ m := by ring

/-- **The cell-power sum from the transfer bound**: if `1/4 ≤ s ≤ 1/2` and
`261313/400000 + (1 - 2s) ≤ 4^{-β}`, then `CellPowerSumStatement s β`, with the majorants
`b_i = ∏_{k<m} (|cos(4^k c_i)| + (π/2) 4^k/4^m)²`. -/
theorem cellPowerSum_of {s β : ℝ} (hs : 1 / 4 ≤ s) (hs' : s ≤ 1 / 2)
    (hq : 261313 / 400000 + (1 - 2 * s) ≤ (4 : ℝ) ^ (-β)) : CellPowerSumStatement s β := by
  set r : ℝ := 261313 / 400000 with hr
  set q : ℝ := r + (1 - 2 * s) with hq_def
  have hq0 : 0 < q := by
    rw [hq_def, hr]
    linarith
  refine ⟨exp (2 / q), exp_pos _, fun m => ?_⟩
  set ε : ℕ → ℝ := fun k => π / 2 * 4 ^ k / 4 ^ m with hε
  have hε0 : ∀ k, 0 < ε k := fun k => by positivity
  have hfac : ∀ i k, 0 < |cos (4 ^ k * centre m i)| + ε k := fun i k =>
    add_pos_of_nonneg_of_pos (abs_nonneg _) (hε0 k)
  refine ⟨fun i => (∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + ε k)) ^ 2, fun i => ?_,
    fun i _ w hw => ?_, ?_⟩
  · exact pow_pos (prod_pos fun k _ => hfac i k) 2
  · -- the majorant property
    unfold lowD
    rw [← sq_abs, abs_prod]
    exact pow_le_pow_left₀ (prod_nonneg fun k _ => abs_nonneg _)
      (prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => abs_cos_le_abs_cos_centre_add hw) 2
  · -- the power sum
    set d : ℕ → ℝ := fun k => (1 - 2 * s) + ε k ^ (2 * s) with hd_def
    have hd : ∀ k, 0 ≤ d k := fun k => add_nonneg (by linarith) (rpow_nonneg (hε0 k).le _)
    have hterm : ∀ i ∈ range (4 ^ m),
        ((∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + ε k)) ^ 2) ^ s ≤
          ∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + d k) := by
      intro i _
      have hnn : ∀ k ∈ range m, 0 ≤ |cos (4 ^ k * centre m i)| + ε k := fun k _ =>
        (hfac i k).le
      rw [← rpow_natCast, ← rpow_mul (prod_nonneg hnn), ← finsetProd_rpow _ _ hnn]
      refine prod_le_prod₀ (fun k hk => rpow_nonneg (hnn k hk) _) fun k _ => ?_
      push_cast
      calc (|cos (4 ^ k * centre m i)| + ε k) ^ ((2 : ℝ) * s) ≤
            |cos (4 ^ k * centre m i)| ^ (2 * s) + ε k ^ (2 * s) :=
            rpow_add_le_add_rpow (abs_nonneg _) (hε0 k).le (by linarith) (by linarith)
        _ ≤ (|cos (4 ^ k * centre m i)| + (1 - 2 * s)) + ε k ^ (2 * s) := by
            gcongr
            exact rpow_le_add_one_sub (abs_nonneg _) (by linarith) (by linarith)
        _ = |cos (4 ^ k * centre m i)| + d k := by
            rw [hd_def]
            ring
    have hsum := sum_prod_le (r := r) (by positivity)
      (fun x hx => by linarith [sum_abs_cos_le hx]) m d hd
    have hpow : q ^ m ≤ ((4 : ℝ) ^ m) ^ (-β) := by
      calc q ^ m ≤ ((4 : ℝ) ^ (-β)) ^ m := pow_le_pow_left₀ hq0.le hq m
        _ = ((4 : ℝ) ^ m) ^ (-β) := by
            rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (by norm_num),
              ← rpow_mul (by norm_num), mul_comm]
    have hexp : exp ((∑ k ∈ range m, ε k ^ (2 * s)) / q) ≤ exp (2 / q) :=
      exp_le_exp.2 (div_le_div_of_nonneg_right (sum_rpow_radius_le (by linarith) m) hq0.le)
    calc ∑ i ∈ range (4 ^ m), ((∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + ε k)) ^ 2) ^ s
        ≤ ∑ i ∈ range (4 ^ m), ∏ k ∈ range m, (|cos (4 ^ k * centre m i)| + d k) :=
          sum_le_sum hterm
      _ ≤ ∏ k ∈ range m, (4 * (r + d k)) := hsum
      _ = 4 ^ m * ∏ k ∈ range m, (q + ε k ^ (2 * s)) := by
          rw [prod_mul_distrib, prod_const, card_range]
          congr 1
          refine prod_congr rfl fun k _ => ?_
          rw [hd_def, hq_def]
          ring
      _ ≤ 4 ^ m * (q ^ m * exp ((∑ k ∈ range m, ε k ^ (2 * s)) / q)) := by
          gcongr
          exact prod_add_le_pow_mul_exp hq0 m _ fun k => rpow_nonneg (hε0 k).le _
      _ ≤ 4 ^ m * (((4 : ℝ) ^ m) ^ (-β) * exp (2 / q)) := by
          gcongr
      _ = exp (2 / q) * ((4 : ℝ) ^ m) ^ (1 - β) := by
          rw [sub_eq_add_neg, rpow_add (by positivity), rpow_one]
          ring

end CellPowerSum

/-- **The improved cell-power sum** (Appendix B.1): `CellPowerSumStatement (1/2 - 10⁻⁷) β₀` with
`β₀ = 3071/10000`. The transfer constant is `261313/400000 + 2/10^7 ≤ 653285/10^6 ≤ 4^{-β₀}`. -/
theorem cellPowerSum : CellPowerSumStatement (1 / 2 - 1 / 10 ^ 7) (3071 / 10000) :=
  CellPowerSum.cellPowerSum_of (by norm_num) (by norm_num)
    (le_trans (by norm_num) CellPowerSum.certificate)

end Favard
