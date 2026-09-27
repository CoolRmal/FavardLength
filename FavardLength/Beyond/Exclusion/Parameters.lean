import FavardLength.Beyond.Exclusion.Transform
import FavardLength.Beyond.Exclusion.Cutoff
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical lemmas for the exclusion assembly

Elementary estimates used when choosing the parameters of the smooth-window argument
(Appendix G §§5, 8; Appendix H §4): powers of four versus logarithms, and the window chain
(G (16)–(20)) that splits the Taylor-expanded window into its main term and relative-derivative
corrections.
-/

open MeasureTheory Set Real
open scoped Nat

namespace Favard.Exclusion

lemma exp_one_le_four : Real.exp 1 ≤ 4 := by
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

lemma one_le_log_four : 1 ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact exp_one_le_four

lemma one_le_log_of_four_le {Z : ℝ} (hZ : 4 ≤ Z) : 1 ≤ Real.log Z :=
  one_le_log_four.trans (Real.log_le_log (by norm_num) hZ)

/-- `Z^a ≤ 4^n` as soon as `a log Z ≤ n`. -/
lemma pow_le_four_pow {Z : ℝ} (hZ : 0 < Z) {a n : ℕ} (h : (a : ℝ) * Real.log Z ≤ n) :
    Z ^ a ≤ 4 ^ n :=
  calc Z ^ a = Real.exp (a * Real.log Z) := by rw [Real.exp_nat_mul, Real.exp_log hZ]
    _ ≤ Real.exp n := Real.exp_le_exp.2 h
    _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 4 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_four n

/-- If `4^n ≤ x` then `n ≤ log x`. -/
lemma natCast_le_log_of_four_pow_le {x : ℝ} {n : ℕ} (h : (4 : ℝ) ^ n ≤ x) :
    (n : ℝ) ≤ Real.log x :=
  calc (n : ℝ) ≤ n * Real.log 4 := le_mul_of_one_le_right (Nat.cast_nonneg n) one_le_log_four
    _ = Real.log (4 ^ n) := by rw [Real.log_pow]
    _ ≤ Real.log x := Real.log_le_log (by positivity) h

/-- A power of four in `(x, 4x]`, with logarithmic exponent. -/
lemma exists_four_pow_between {x : ℝ} (hx : 1 ≤ x) :
    ∃ r : ℕ, x < 4 ^ r ∧ (4 : ℝ) ^ r ≤ 4 * x ∧ (r : ℝ) ≤ 1 + Real.log x := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  refine ⟨n + 1, h2, by rw [pow_succ]; linarith, ?_⟩
  push_cast
  linarith [natCast_le_log_of_four_pow_le h1]

/-- `log x ≤ x` for `x > 0`. -/
lemma log_le_self' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  linarith [Real.log_le_sub_one_of_pos hx]

/-! ### The window chain -/

/-- The phase sums `∑_i χ^{(j)}(β_i/T) e^{-2πiξβ_i}` are bounded by `m C_χ` for `j ≤ J`. -/
lemma norm_phaseSum_le {J m : ℕ} {T ξ Cχ : ℝ} (β : Fin m → ℝ)
    (hχ : ∀ j ≤ J, ∀ x, |iteratedDeriv j cutoff x| ≤ Cχ) {j : ℕ} (hj : j ≤ J) :
    ‖∑ i, ((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
        Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)‖ ≤ m * Cχ := by
  calc ‖∑ i, ((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
        Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)‖
      ≤ ∑ i, ‖((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
        Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, Cχ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        exact hχ j hj _
    _ = m * Cχ := by simp

/-- **The window chain** (Appendix G (14)–(20)): the main term `ψ_{n,t}(ξ) S₀` of the
Taylor-expanded window is bounded by the window bound plus the relative-derivative corrections.
Here `ℓ'` is the logarithm controlling the moments, `M_j ≤ C_j ℓ'^j |ψ|`, and `ℓ' ≤ T`. -/
lemma window_chain {J n m : ℕ} {t T ξ α e h ψ ℓ' CE Cχ : ℝ} (β : Fin m → ℝ) (Cm : ℕ → ℝ)
    (hT : 1 ≤ T) (hξ : 1 / 4 ≤ ξ) (hα : 0 ≤ α) (hh : 0 ≤ h) (hℓ' : 0 ≤ ℓ') (hℓT : ℓ' ≤ T)
    (hCE : 0 ≤ CE)
    (hCm : ∀ j, 0 ≤ Cm j) (hCχ : 0 ≤ Cχ) (hχ : ∀ j ≤ J, ∀ x, |iteratedDeriv j cutoff x| ≤ Cχ)
    (hψ : ψ = |tailFT n t ξ|) (hM : ∀ j, ‖tailMoment n t j ξ‖ ≤ Cm j * ℓ' ^ j * ψ)
    (hαT : α * T ≤ 16 * m)
    (hwin : ‖expandedWindow J n t T ξ β‖ ≤
      CE * m / T ^ (J + 1) + CE * α * T * (√e + h * ξ + 1 / (T * ξ) ^ J)) :
    ψ * ‖∑ i, ((cutoff (β i / T) : ℝ) : ℂ) * Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)‖ ≤
      17 * CE * m * (4 ^ J / T ^ J) + 16 * CE * m * (√e + h * ξ) +
        (∑ j ∈ Finset.range J, Cm (j + 1)) * ψ * m * Cχ * (ℓ' / T) := by
  have hT0 : 0 < T := by linarith
  set S : ℕ → ℂ := fun j => ∑ i, ((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
    Complex.exp (↑(-2 * π * ξ * β i) * Complex.I) with hS
  set a : ℕ → ℂ := fun j => tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) * S j with ha
  have hEW : expandedWindow J n t T ξ β = ∑ j ∈ Finset.range J, a (j + 1) + a 0 := by
    rw [expandedWindow, Finset.sum_range_succ']
  have ha0 : a 0 = (tailFT n t ξ : ℂ) *
      ∑ i, ((cutoff (β i / T) : ℝ) : ℂ) * Complex.exp (↑(-2 * π * ξ * β i) * Complex.I) := by
    simp only [ha, hS, tailMoment_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
      div_one, iteratedDeriv_zero]
  -- the corrections
  have hℓT' : ℓ' / T ≤ 1 := (div_le_one hT0).2 hℓT
  have hψ0 : 0 ≤ ψ := hψ ▸ abs_nonneg _
  have hterm : ∀ j < J, ‖a (j + 1)‖ ≤ Cm (j + 1) * ψ * m * Cχ * (ℓ' / T) := by
    intro j hj
    have hfac : (1 : ℝ) ≤ ((j + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (j + 1)
    have hpow : (ℓ' / T) ^ (j + 1) ≤ ℓ' / T :=
      pow_le_of_le_one (div_nonneg hℓ' hT0.le) hℓT' (Nat.succ_ne_zero j)
    calc ‖a (j + 1)‖ = ‖tailMoment n t (j + 1) ξ‖ / (((j + 1)! : ℝ) * T ^ (j + 1)) *
          ‖S (j + 1)‖ := by
          simp only [ha, norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hT0]
      _ ≤ Cm (j + 1) * ℓ' ^ (j + 1) * ψ / (1 * T ^ (j + 1)) * (m * Cχ) := by
          refine mul_le_mul (div_le_div₀ (mul_nonneg (mul_nonneg (hCm _) (pow_nonneg hℓ' _))
            hψ0) (hM _) (by rw [one_mul]; exact pow_pos hT0 _)
            (mul_le_mul_of_nonneg_right hfac (pow_nonneg hT0.le _)))
            (norm_phaseSum_le β hχ (by omega)) (norm_nonneg _)
            (div_nonneg (mul_nonneg (mul_nonneg (hCm _) (pow_nonneg hℓ' _)) hψ0)
              (by rw [one_mul]; exact (pow_pos hT0 _).le))
      _ = Cm (j + 1) * ψ * m * Cχ * (ℓ' / T) ^ (j + 1) := by
          rw [div_pow]; field_simp
      _ ≤ Cm (j + 1) * ψ * m * Cχ * (ℓ' / T) := by
          gcongr
          exact mul_nonneg (mul_nonneg (mul_nonneg (hCm _) hψ0) (Nat.cast_nonneg _)) hCχ
  have hrest : ‖∑ j ∈ Finset.range J, a (j + 1)‖ ≤
      (∑ j ∈ Finset.range J, Cm (j + 1)) * ψ * m * Cχ * (ℓ' / T) := by
    calc ‖∑ j ∈ Finset.range J, a (j + 1)‖ ≤ ∑ j ∈ Finset.range J, ‖a (j + 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range J, Cm (j + 1) * ψ * m * Cχ * (ℓ' / T) :=
          Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.1 hj)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  -- the window bound
  have hTJ : (0 : ℝ) < T ^ J := pow_pos hT0 J
  have h1' : 1 / T ^ (J + 1) ≤ 4 ^ J / T ^ J :=
    calc 1 / T ^ (J + 1) ≤ 1 / T ^ J :=
          one_div_le_one_div_of_le hTJ (pow_le_pow_right₀ hT (by omega))
      _ ≤ 4 ^ J / T ^ J := div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) hTJ.le
  have h1 : CE * m / T ^ (J + 1) ≤ CE * m * (4 ^ J / T ^ J) := by
    rw [show CE * m / T ^ (J + 1) = CE * m * (1 / T ^ (J + 1)) by ring]
    exact mul_le_mul_of_nonneg_left h1' (mul_nonneg hCE (Nat.cast_nonneg m))
  have h2 : 1 / (T * ξ) ^ J ≤ 4 ^ J / T ^ J := by
    rw [mul_pow, div_le_div_iff₀ (by positivity) hTJ, one_mul]
    calc T ^ J = 4 ^ J * (T ^ J * (1 / 4) ^ J) := by
          rw [one_div_pow]; field_simp
      _ ≤ 4 ^ J * (T ^ J * ξ ^ J) := by gcongr
  have hwin' : ‖expandedWindow J n t T ξ β‖ ≤
      17 * CE * m * (4 ^ J / T ^ J) + 16 * CE * m * (√e + h * ξ) := by
    refine hwin.trans ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hαT0 : 0 ≤ α * T := mul_nonneg hα hT0.le
    have hY : 0 ≤ (4 : ℝ) ^ J / T ^ J := by positivity
    have hsq : 0 ≤ √e + h * ξ := add_nonneg (Real.sqrt_nonneg e) (mul_nonneg hh (by linarith))
    calc CE * m / T ^ (J + 1) + CE * α * T * (√e + h * ξ + 1 / (T * ξ) ^ J)
        = CE * m / T ^ (J + 1) + CE * (α * T) * (√e + h * ξ) +
            CE * (α * T) * (1 / (T * ξ) ^ J) := by ring
      _ ≤ CE * m * (4 ^ J / T ^ J) + CE * (α * T) * (√e + h * ξ) +
            CE * (16 * m) * (4 ^ J / T ^ J) := by
          gcongr
      _ ≤ 17 * CE * m * (4 ^ J / T ^ J) + 16 * CE * m * (√e + h * ξ) := by
          nlinarith [mul_le_mul_of_nonneg_left hαT hCE, mul_nonneg hCE hsq]
  have hmain : ‖a 0‖ ≤ ‖expandedWindow J n t T ξ β‖ + ‖∑ j ∈ Finset.range J, a (j + 1)‖ := by
    rw [hEW]
    calc ‖a 0‖ = ‖(∑ j ∈ Finset.range J, a (j + 1) + a 0) -
          ∑ j ∈ Finset.range J, a (j + 1)‖ := by rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  rw [ha0, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hψ] at hmain
  linarith

/-! ### The four error ratios of the window comparison -/

/-- The relative-derivative correction: `√m ℓ'/T ≤ δ₅` when `m ≤ 12HT`, `T ≥ κ⁴Hℓ²` and
`ℓ' ≤ 200018 κ ℓ`, for `κ ≥ 12 · 200018²/δ₅²` (Appendix G (23), H §4). -/
lemma corr_small {m ℓ' T H κ ℓ δ₅ : ℝ} (hm0 : 0 ≤ m) (hT0 : 0 < T) (hm12 : m ≤ 12 * H * T)
    (hx : κ ^ 4 * H * ℓ ^ 2 ≤ T) (hℓ' : ℓ' ≤ 200018 * κ * ℓ) (hℓ'0 : 0 ≤ ℓ') (hκ1 : 1 ≤ κ)
    (hH : 1 ≤ H) (hℓ1 : 1 ≤ ℓ) (hδ₅ : 0 < δ₅) (hκδ : 12 * 200018 ^ 2 / δ₅ ^ 2 ≤ κ) :
    √m * ℓ' / T ≤ δ₅ := by
  have hsq : (√m * ℓ' / T) ^ 2 ≤ δ₅ ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hm0]
    have hκ0 : 0 < κ := by linarith
    have hH0 : 0 < H := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have h1 : m * ℓ' ^ 2 / T ^ 2 ≤ 12 * H * ℓ' ^ 2 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      have := mul_le_mul_of_nonneg_right hm12 (by positivity : (0 : ℝ) ≤ ℓ' ^ 2 * T)
      nlinarith
    have h2 : 12 * H * ℓ' ^ 2 / T ≤ 12 * H * ℓ' ^ 2 / (κ ^ 4 * H * ℓ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hx
    have h3 : 12 * H * ℓ' ^ 2 / (κ ^ 4 * H * ℓ ^ 2) ≤
        12 * H * (200018 * κ * ℓ) ^ 2 / (κ ^ 4 * H * ℓ ^ 2) := by
      gcongr
    have h4 : 12 * H * (200018 * κ * ℓ) ^ 2 / (κ ^ 4 * H * ℓ ^ 2) = 12 * 200018 ^ 2 / κ ^ 2 := by
      field_simp
    have h5 : 12 * 200018 ^ 2 / κ ^ 2 ≤ δ₅ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hκκ : κ ≤ κ ^ 2 := le_self_pow₀ hκ1 (by norm_num)
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < δ₅ ^ 2)).1 hκδ
      nlinarith [sq_nonneg δ₅]
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hδ₅.le hsq

/-- The logarithm of the selected frequency: if `0 ≤ x ≤ 12 · 128² κ⁸ Z^{10}` with `κ ≥ 1` and
`Z ≥ 4`, then `log(2 + x) ≤ 200018 κ log Z`. -/
lemma log_two_add_le {x κ Z : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 12 * 128 ^ 2 * κ ^ 8 * Z ^ 10)
    (hκ1 : 1 ≤ κ) (hZ4 : 4 ≤ Z) : Real.log (2 + x) ≤ 200018 * κ * Real.log Z := by
  have hℓ1 := one_le_log_of_four_le hZ4
  have hκ8 : 1 ≤ κ ^ 8 := one_le_pow₀ hκ1
  have hZ10 : 1 ≤ Z ^ 10 := one_le_pow₀ (by linarith)
  have h1 : 2 + x ≤ 200000 * κ ^ 8 * Z ^ 10 := by nlinarith
  have h2 : Real.log (200000 * κ ^ 8 * Z ^ 10) =
      Real.log 200000 + 8 * Real.log κ + 10 * Real.log Z := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have h3 : Real.log 200000 ≤ 200000 := log_le_self' (by norm_num)
  have h4 : Real.log κ ≤ κ := log_le_self' (by linarith)
  have h5 : Real.log (2 + x) ≤ Real.log (200000 * κ ^ 8 * Z ^ 10) :=
    Real.log_le_log (by linarith) h1
  have hκℓ1 : 1 ≤ κ * Real.log Z := one_le_mul_of_one_le_of_one_le hκ1 hℓ1
  have hκℓκ : κ ≤ κ * Real.log Z := le_mul_of_one_le_right (by linarith) hℓ1
  have hκℓℓ : Real.log Z ≤ κ * Real.log Z := le_mul_of_one_le_left (by linarith) hκ1
  linarith

/-- The perturbation condition (Appendix G (40), H §4): with `τ = |t - t₀| ≤ c_rad/D` and
`ξ ℓ' ≤ (3/2) 128² · 200018 κ⁹ D`, `4 τ ξ ℓ' ≤ c₀` for `c_rad = c₀/(6 · 128² · 200018 κ⁹)`. -/
lemma pert_le {τ ξ ℓ' crad D c₀ κ : ℝ} (hτ : 0 ≤ τ) (hτD : τ ≤ crad / D) (hD : 0 < D)
    (hξℓ : ξ * ℓ' ≤ 3 / 2 * 128 ^ 2 * 200018 * κ ^ 9 * D) (hξℓ0 : 0 ≤ ξ * ℓ')
    (hcrad : crad = c₀ / (6 * 128 ^ 2 * 200018 * κ ^ 9)) (hκ : 0 < κ) :
    4 * τ * ξ * ℓ' ≤ c₀ := by
  have hcrad0 : 0 ≤ crad / D := hτ.trans hτD
  calc 4 * τ * ξ * ℓ' = 4 * τ * (ξ * ℓ') := by ring
    _ ≤ 4 * (crad / D) * (3 / 2 * 128 ^ 2 * 200018 * κ ^ 9 * D) := by gcongr
    _ = c₀ := by rw [hcrad]; field_simp; ring

/-- The box condition `ρ4^{-n} ξ ≤ 1/4` (Appendix G (6)) at depth `n ≥ (a₀ + 11) log Z`. -/
lemma box_le {n a₀ : ℕ} {ξ Z κ : ℝ} (hZ4 : 4 ≤ Z) (hn : ((a₀ : ℝ) + 11) * Real.log Z ≤ n)
    (ha₀ : 16 * 128 ^ 2 * κ ^ 8 ≤ 4 ^ a₀) (hξ : 32 / 3 * ξ ≤ 16 * 128 ^ 2 * κ ^ 8 * Z ^ 11) :
    8 / 3 / 4 ^ n * ξ ≤ 1 / 4 := by
  have hZ0 : 0 < Z := by linarith
  have h4n : Z ^ (a₀ + 11) ≤ 4 ^ n := pow_le_four_pow hZ0 (by push_cast; exact hn)
  have hZa : (4 : ℝ) ^ a₀ ≤ Z ^ a₀ := pow_le_pow_left₀ (by norm_num) hZ4 a₀
  have h4 : 16 * 128 ^ 2 * κ ^ 8 * Z ^ 11 ≤ 4 ^ n := by
    calc 16 * 128 ^ 2 * κ ^ 8 * Z ^ 11 ≤ 4 ^ a₀ * Z ^ 11 := by gcongr
      _ ≤ Z ^ a₀ * Z ^ 11 := by gcongr
      _ = Z ^ (a₀ + 11) := by ring
      _ ≤ 4 ^ n := h4n
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- The main-term constant: from `c₁ · 4B^{γ-2}/(π²k²) ≤ ψ` and `k² ≤ 36 m⁴`,
`c₁/(9π²) ≤ ψ · m⁴ B^{2-γ}`. -/
lemma psi_lower {c₁ B γ k m ψ : ℝ} (hc₁ : 0 < c₁) (hB1 : 1 ≤ B) (hk : 0 < k) (hm : 0 < m)
    (hk2 : k ^ 2 ≤ 36 * m ^ 4) (hψ : c₁ * (4 * B ^ (γ - 2) / (π ^ 2 * k ^ 2)) ≤ ψ) :
    c₁ / (9 * π ^ 2) ≤ ψ * (m ^ 4 * B ^ (2 - γ)) := by
  have hBγ : B ^ (γ - 2) * B ^ (2 - γ) = 1 := by
    rw [← Real.rpow_add (by linarith)]
    simp
  have hP0 : 0 < m ^ 4 * B ^ (2 - γ) := by positivity
  have h2 : c₁ / (9 * π ^ 2) ≤
      c₁ * (4 * B ^ (γ - 2) / (π ^ 2 * k ^ 2)) * (m ^ 4 * B ^ (2 - γ)) := by
    have e : c₁ * (4 * B ^ (γ - 2) / (π ^ 2 * k ^ 2)) * (m ^ 4 * B ^ (2 - γ)) =
        4 * c₁ * m ^ 4 / (π ^ 2 * k ^ 2) * (B ^ (γ - 2) * B ^ (2 - γ)) := by ring
    rw [e, hBγ, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ c₁ * π ^ 2)
    nlinarith
  exact le_trans h2 (mul_le_mul_of_nonneg_right hψ hP0.le)

/-- The Taylor-remainder and constant-mode ratios (Appendix G (35)–(36), H (13)):
`m⁴ B^{2-γ} √m · 4^J/T^J ≤ δ₁` when `m ≤ 12HT`, `T ≥ x₀ = κ⁴ H B^ε ℓ²`,
`ε(J - 5) ≥ 2 - γ` and `κ ≥ 12⁵ 4^J/δ₁`. -/
lemma taylor_small {m H T B κ ℓ ε γ δ₁ : ℝ} {J : ℕ} (hJ : 10 ≤ J) (hm1 : 1 ≤ m)
    (hm12 : m ≤ 12 * H * T) (hTx : κ ^ 4 * H * B ^ ε * ℓ ^ 2 ≤ T) (hH : 1 ≤ H) (hB1 : 1 ≤ B)
    (hℓ1 : 1 ≤ ℓ) (hκ1 : 1 ≤ κ) (hJε : 2 - γ ≤ ε * ((J : ℝ) - 5)) (hε0 : 0 < ε)
    (hδ : 0 < δ₁) (hκY : 12 ^ 5 * 4 ^ J / δ₁ ≤ κ) :
    m ^ 4 * B ^ (2 - γ) * √m * (4 ^ J / T ^ J) ≤ δ₁ := by
  have hm0 : 0 ≤ m := by linarith
  have hH0 : 0 < H := by linarith
  have hBε1 : 1 ≤ B ^ ε := Real.one_le_rpow hB1 hε0.le
  have hx1 : 1 ≤ κ ^ 4 * H * B ^ ε * ℓ ^ 2 := by
    have : (1 : ℝ) ≤ κ ^ 4 := one_le_pow₀ hκ1
    have : (1 : ℝ) ≤ ℓ ^ 2 := one_le_pow₀ hℓ1
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ κ ^ 4 * H * B ^ ε * ℓ ^ 2 := by gcongr
  have hT0 : 0 < T := by linarith
  have hB0 : 0 < B ^ (2 - γ) := by positivity
  -- `κ H⁵ B^{2-γ} ≤ x₀^{J-5} ≤ T^{J-5}`
  have hJ5 : ((J - 5 : ℕ) : ℝ) = (J : ℝ) - 5 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hpow : κ * H ^ 5 * B ^ (2 - γ) ≤ T ^ (J - 5) := by
    have h1 : κ ≤ (κ ^ 4) ^ (J - 5) := by
      rw [← pow_mul]; exact le_self_pow₀ hκ1 (by omega)
    have h2 : H ^ 5 ≤ H ^ (J - 5) := pow_le_pow_right₀ hH (by omega)
    have h3 : B ^ (2 - γ) ≤ (B ^ ε) ^ (J - 5) := by
      rw [← Real.rpow_mul_natCast (by linarith), hJ5]
      exact Real.rpow_le_rpow_of_exponent_le hB1 hJε
    have h4 : 1 ≤ (ℓ ^ 2) ^ (J - 5) := one_le_pow₀ (one_le_pow₀ hℓ1)
    calc κ * H ^ 5 * B ^ (2 - γ) = κ * H ^ 5 * B ^ (2 - γ) * 1 := by ring
      _ ≤ (κ ^ 4) ^ (J - 5) * H ^ (J - 5) * (B ^ ε) ^ (J - 5) * (ℓ ^ 2) ^ (J - 5) := by
          gcongr
      _ = (κ ^ 4 * H * B ^ ε * ℓ ^ 2) ^ (J - 5) := by ring
      _ ≤ T ^ (J - 5) := pow_le_pow_left₀ (by linarith) hTx _
  have hsqm : √m ≤ m := by
    rw [Real.sqrt_le_left hm0]
    nlinarith
  have hTJ : T ^ J = T ^ 5 * T ^ (J - 5) := by rw [← pow_add]; congr 1; omega
  have hm5 : m ^ 5 ≤ (12 * H * T) ^ 5 := pow_le_pow_left₀ hm0 hm12 5
  calc m ^ 4 * B ^ (2 - γ) * √m * (4 ^ J / T ^ J)
      ≤ m ^ 4 * B ^ (2 - γ) * m * (4 ^ J / T ^ J) := by gcongr
    _ = m ^ 5 * B ^ (2 - γ) * 4 ^ J / T ^ J := by ring
    _ ≤ (12 * H * T) ^ 5 * B ^ (2 - γ) * 4 ^ J / T ^ J := by gcongr
    _ = 12 ^ 5 * 4 ^ J * (H ^ 5 * B ^ (2 - γ)) / T ^ (J - 5) := by
        rw [hTJ]; field_simp
    _ ≤ 12 ^ 5 * 4 ^ J * (H ^ 5 * B ^ (2 - γ)) / (κ * H ^ 5 * B ^ (2 - γ)) := by
        gcongr
    _ = 12 ^ 5 * 4 ^ J / κ := by field_simp
    _ ≤ δ₁ := by
        rw [div_le_iff₀ (by linarith)]
        rw [div_le_iff₀ hδ] at hκY
        linarith

/-- The flatness ratio (Appendix G (39), H (15)): `(m⁴ B^{2-γ} √m √e)² ≤ δ₁²` from
`m ≤ 128 κ⁴ H² B^ε ℓ²`, `e ≤ (512/3) H C ℓ/N` and `N ≥ C_N H^{19} B^{4-2γ+9ε} ℓ^{19}`. -/
lemma flat_small {m H B κ ℓ ε γ δ₁ e N CrL CN : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ 128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2) (he0 : 0 ≤ e)
    (he : e ≤ 512 / 3 * H * CrL * ℓ / N) (hN0 : 0 < N) (hH : 1 ≤ H) (hB1 : 1 ≤ B)
    (hℓ1 : 1 ≤ ℓ) (hκ1 : 1 ≤ κ) (hδ : 0 < δ₁)
    (hNV : CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) ≤ N)
    (hCN3 : (128 * κ ^ 4) ^ 9 * (512 / 3) * CrL / δ₁ ^ 2 ≤ CN) :
    m ^ 4 * B ^ (2 - γ) * √m * √e ≤ δ₁ := by
  have hB0 : 0 < B := by linarith
  have hBε0 : 0 < B ^ ε := by positivity
  have hsq : (m ^ 4 * B ^ (2 - γ) * √m * √e) ^ 2 ≤ δ₁ ^ 2 := by
    have e1 : (m ^ 4 * B ^ (2 - γ) * √m * √e) ^ 2 = m ^ 9 * (B ^ (2 - γ)) ^ 2 * e := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hm0, Real.sq_sqrt he0]; ring
    have hBexp : (B ^ (2 - γ)) ^ 2 * (B ^ ε) ^ 9 = B ^ (4 - 2 * γ + 9 * ε) := by
      rw [← Real.rpow_mul_natCast hB0.le, ← Real.rpow_mul_natCast hB0.le,
        ← Real.rpow_add hB0]
      congr 1; push_cast; ring
    have hm9 : m ^ 9 ≤ (128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2) ^ 9 := pow_le_pow_left₀ hm0 hm 9
    have hV0 : 0 < H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19 := by positivity
    rw [e1]
    calc m ^ 9 * (B ^ (2 - γ)) ^ 2 * e
        ≤ (128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2) ^ 9 * (B ^ (2 - γ)) ^ 2 *
            (512 / 3 * H * CrL * ℓ / N) := by gcongr
      _ = (128 * κ ^ 4) ^ 9 * (512 / 3) * CrL *
            (H ^ 19 * ((B ^ (2 - γ)) ^ 2 * (B ^ ε) ^ 9) * ℓ ^ 19) / N := by ring
      _ = (128 * κ ^ 4) ^ 9 * (512 / 3) * CrL *
            (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) / N := by rw [hBexp]
      _ ≤ δ₁ ^ 2 := by
          rw [div_le_iff₀ hN0]
          rw [div_le_iff₀ (pow_pos hδ 2)] at hCN3
          have := mul_le_mul_of_nonneg_right hCN3 hV0.le
          nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hδ.le hsq

/-- The averaging ratio (Appendix G (38), H (14)): with `h = ρ4^{-L}`, `ξ ≤ (3/2) B m²`,
`m ≤ 128 κ⁴ Z⁵`, `B ≤ Z` and `4^L > Λ Z^{38}`, `m⁴ B^{2-γ} √m (h ξ) ≤ δ₁`. -/
lemma avg_small {m B Z κ γ δ₁ Λ ξ : ℝ} {L : ℕ} (hm1 : 1 ≤ m) (hκ1 : 1 ≤ κ)
    (hmZ : m ≤ 128 * κ ^ 4 * Z ^ 5)
    (hB1 : 1 ≤ B) (hBZ : B ≤ Z) (hγ0 : 0 < γ) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 3 / 2 * B * m ^ 2)
    (hL : Λ * Z ^ 38 < 4 ^ L) (hδ : 0 < δ₁) (hΛ : 4 * (128 * κ ^ 4) ^ 7 / δ₁ ≤ Λ) :
    m ^ 4 * B ^ (2 - γ) * √m * (8 / 3 / 4 ^ L * ξ) ≤ δ₁ := by
  have hm0 : 0 ≤ m := by linarith
  have hZ1 : 1 ≤ Z := hB1.trans hBZ
  have hB2 : B ^ (2 - γ) ≤ B ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hB1 (show 2 - γ ≤ (2 : ℕ) by push_cast; linarith)
    rwa [Real.rpow_natCast] at this
  have hsqm : √m ≤ m := by
    rw [Real.sqrt_le_left hm0]
    nlinarith
  have hm7 : m ^ 7 ≤ (128 * κ ^ 4 * Z ^ 5) ^ 7 := pow_le_pow_left₀ hm0 hmZ 7
  have hB3 : B ^ 3 ≤ Z ^ 3 := pow_le_pow_left₀ (by linarith) hBZ 3
  have h4L : 0 < (4 : ℝ) ^ L := by positivity
  have hκ0 : 0 < κ := by linarith
  have hΛ0 : 0 < Λ := lt_of_lt_of_le
    (div_pos (mul_pos (by norm_num) (pow_pos (mul_pos (by norm_num) (pow_pos hκ0 4)) 7)) hδ) hΛ
  calc m ^ 4 * B ^ (2 - γ) * √m * (8 / 3 / 4 ^ L * ξ)
      ≤ m ^ 4 * B ^ 2 * m * (8 / 3 / 4 ^ L * (3 / 2 * B * m ^ 2)) := by gcongr
    _ = 4 * m ^ 7 * B ^ 3 / 4 ^ L := by field_simp; ring
    _ ≤ 4 * (128 * κ ^ 4 * Z ^ 5) ^ 7 * Z ^ 3 / 4 ^ L := by gcongr
    _ = 4 * (128 * κ ^ 4) ^ 7 * Z ^ 38 / 4 ^ L := by ring
    _ ≤ 4 * (128 * κ ^ 4) ^ 7 * Z ^ 38 / (Λ * Z ^ 38) := by
        gcongr
    _ = 4 * (128 * κ ^ 4) ^ 7 / Λ := by field_simp
    _ ≤ δ₁ := by
        rw [div_le_iff₀ hΛ0]
        rw [div_le_iff₀ hδ] at hΛ
        linarith

/-- A main-term comparison: if `Q √M X ≤ c_ψ/(1088 C_E)` and `c_ψ ≤ ψ Q`, then
`17 C_E M X ≤ ψ √M / 64`. -/
lemma term_le_of_small {CE ψ M X Q cψ : ℝ} (hCE : 0 < CE) (hM : 0 ≤ M) (hQ : 0 < Q)
    (hψ : cψ ≤ ψ * Q) (hsmall : Q * √M * X ≤ cψ / (1088 * CE)) :
    17 * CE * M * X ≤ ψ * √M / 64 := by
  have h1 : 1088 * CE * (Q * √M * X) ≤ ψ * Q := by
    calc 1088 * CE * (Q * √M * X) ≤ 1088 * CE * (cψ / (1088 * CE)) := by gcongr
      _ = cψ := by field_simp
      _ ≤ ψ * Q := hψ
  have h2 : 1088 * CE * (√M * X) ≤ ψ := by
    have : Q * (1088 * CE * (√M * X)) ≤ Q * ψ := by nlinarith
    exact le_of_mul_le_mul_left this hQ
  have hMM : M = √M * √M := (Real.mul_self_sqrt hM).symm
  have hsq : 0 ≤ √M := Real.sqrt_nonneg M
  calc 17 * CE * M * X = 17 * CE * (√M * √M) * X := by rw [← hMM]
    _ = √M * (1088 * CE * (√M * X)) / 64 := by ring
    _ ≤ √M * ψ / 64 := by gcongr
    _ = ψ * √M / 64 := by ring

/-- **The final comparison** (Appendix G §5): the main term `ψ √m/8 ≤ ψ ‖S₀‖` cannot be bounded
by the four error terms when each is at most `ψ √m/64`. -/
lemma window_contra {ψ S m CE Csum Cχ Y e A ρ' cψ P : ℝ} (hψP : cψ ≤ ψ * P) (hcψ : 0 < cψ)
    (hP : 0 < P) (hm1 : 1 ≤ m) (hCE : 0 < CE) (hCsum : 0 ≤ Csum) (hCχ : 0 ≤ Cχ)
    (hS : √m / 8 ≤ S)
    (hchain : ψ * S ≤ 17 * CE * m * Y + 16 * CE * m * (√e + A) + Csum * ψ * m * Cχ * ρ')
    (hsY : P * √m * Y ≤ cψ / (1088 * CE)) (hse : P * √m * √e ≤ cψ / (1088 * CE))
    (hsA : P * √m * A ≤ cψ / (1088 * CE)) (hsρ : √m * ρ' ≤ 1 / (64 * (Csum * Cχ + 1))) :
    False := by
  have hm0 : 0 ≤ m := by linarith
  have hψ0 : 0 < ψ := by
    by_contra h0
    push Not at h0
    have : ψ * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hP.le
    linarith
  have hsqm1 : 1 ≤ √m := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hm1
  have h1 := term_le_of_small hCE hm0 hP hψP hsY
  have h2 := term_le_of_small hCE hm0 hP hψP hse
  have h3 := term_le_of_small hCE hm0 hP hψP hsA
  have hsq : √m * √m = m := Real.mul_self_sqrt hm0
  have h4 : Csum * ψ * m * Cχ * ρ' ≤ ψ * √m / 64 := by
    have hCC : 0 ≤ Csum * Cχ := mul_nonneg hCsum hCχ
    have hd : Csum * Cχ * (1 / (64 * (Csum * Cχ + 1))) ≤ 1 / 64 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc Csum * ψ * m * Cχ * ρ' = Csum * Cχ * (ψ * √m) * (√m * ρ') := by
          conv_lhs => rw [← hsq]
          ring
      _ ≤ Csum * Cχ * (ψ * √m) * (1 / (64 * (Csum * Cχ + 1))) := by
          gcongr
      _ = Csum * Cχ * (1 / (64 * (Csum * Cχ + 1))) * (ψ * √m) := by ring
      _ ≤ 1 / 64 * (ψ * √m) := by gcongr
      _ = ψ * √m / 64 := by ring
  have hmain : ψ * (√m / 8) ≤ ψ * S := mul_le_mul_of_nonneg_left hS hψ0.le
  have hsqe : 0 ≤ √e := Real.sqrt_nonneg e
  have hmCE : 0 ≤ CE * m := mul_nonneg hCE.le hm0
  have h2' : 16 * CE * m * √e ≤ 17 * CE * m * √e := by nlinarith
  have h3' : 16 * CE * m * A ≤ 17 * CE * m * A := by nlinarith
  have hpos : 0 < ψ * √m := mul_pos hψ0 (by linarith)
  nlinarith

end Favard.Exclusion
