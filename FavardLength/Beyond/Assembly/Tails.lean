import FavardLength.Beyond.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The old and the new exceptional-slope tails

Both estimates bound the measure of the low-energy slope set
`{t ∈ [0, 1] : normEnergy r t ≤ A K for 1 ≤ r ≤ N}` produced by the geometric step
(`Favard.Assembly.volume_projLength_gt_le_slope`), where `K ≥ 2` is the multiplicity threshold
and the depth `N ≥ 1` satisfies `P ≤ 2 C₃ K^{1+κ} N`.

* **Old tail** (beyond note (4)). The improved exceptional-direction estimate with `H = A K`
  gives `C_O (H^{4-2β/s} (2 + log H)/N)^{s/2}`; with `2 + log H ≤ (2 + 1/κ) H^κ` this is at most
  a constant times `P^{-s/2} K^{(5 - 2β/s + 2κ) s/2}`.
* **New tail** (beyond note (21)–(22)). The new exceptional-energy estimate at the terminal depth
  `N`, with `H = A K` and the denominator scale `R = P^{(1-η)/D} K^{-20/D}`, gives a constant
  times `P^{5τ - (1-η) c₁/D} K^{4 + 20 c₁/D}`. The logarithm `ℓ = log(2 + H R)` is at most
  `L P^τ` with `L = (2 + A)^τ/τ`. The size condition `R ≥ 2`, the redundancy condition
  `C H⁸ ℓ⁹ ≤ R^μ` and the depth condition `C H¹⁹ R^D ℓ¹⁹ ≤ N` hold uniformly in
  `2 ≤ K ≤ P^z` once `P` is so large that three explicit powers of `P` dominate constants.
-/

open MeasureTheory Set Real

namespace Favard.Assembly

/-- **Old tail** (beyond note (4)): the improved exceptional-direction estimate at `H = A K`. -/
theorem volume_lowEnergy_le_old {s β CO : ℝ} (hs : 0 < s) (hCO : 0 ≤ CO)
    (hOld : ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
      volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} ≤
        ENNReal.ofReal (CO * (H ^ (4 - 2 * β / s) * (2 + Real.log H) / N) ^ (s / 2)))
    {A K C₃ κ : ℝ} (hA : 1 ≤ A) (hK : 2 ≤ K) (hC₃ : 0 < C₃) (hκ : 0 < κ)
    {P N : ℕ} (hP : 0 < P) (hN : 1 ≤ N) (hPN : (P : ℝ) ≤ 2 * (C₃ * K ^ (1 + κ)) * N) :
    volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ A * K} ≤
      ENNReal.ofReal (CO * (2 * C₃ * (2 + 1 / κ) * A ^ (4 - 2 * β / s + κ)) ^ (s / 2) *
        (P : ℝ) ^ (-(s / 2)) * K ^ ((5 - 2 * β / s + 2 * κ) * (s / 2))) := by
  set q := 4 - 2 * β / s with hq_def
  set H := A * K with hH
  have hK0 : 0 < K := by linarith
  have hH2 : 2 ≤ H := by nlinarith
  have hH0 : 0 < H := by linarith
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine (hOld H hH2 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
  have hHe : 1 ≤ H ^ κ := one_le_rpow (by linarith) hκ.le
  have hlogH : 2 + Real.log H ≤ (2 + 1 / κ) * H ^ κ := by
    have := log_le_rpow_div hH0.le hκ
    have h' : H ^ κ / κ = 1 / κ * H ^ κ := by ring
    nlinarith
  have hinvN : (N : ℝ)⁻¹ ≤ 2 * (C₃ * K ^ (1 + κ)) / P := by
    rw [inv_eq_one_div, div_le_div_iff₀ hNpos hPpos]
    linarith
  have hHq : H ^ q * H ^ κ = A ^ (q + κ) * K ^ (q + κ) := by
    rw [← rpow_add hH0, mul_rpow (by linarith) hK0.le]
  have hKexp : K ^ (q + κ) * K ^ (1 + κ) = K ^ (5 - 2 * β / s + 2 * κ) := by
    rw [← rpow_add hK0]
    congr 1
    rw [hq_def]
    ring
  set X := 2 * C₃ * (2 + 1 / κ) * A ^ (q + κ) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ A ^ (q + κ) := rpow_nonneg (by linarith) _
    positivity
  have hbound : H ^ q * (2 + Real.log H) / N ≤
      X * (P : ℝ)⁻¹ * K ^ (5 - 2 * β / s + 2 * κ) := by
    have hHq0 : 0 ≤ H ^ q := rpow_nonneg hH0.le _
    calc H ^ q * (2 + Real.log H) / N
        ≤ H ^ q * ((2 + 1 / κ) * H ^ κ) * (2 * (C₃ * K ^ (1 + κ)) / P) := by
          rw [div_eq_mul_inv]
          gcongr
      _ = 2 * C₃ * (2 + 1 / κ) * (H ^ q * H ^ κ) * K ^ (1 + κ) * (P : ℝ)⁻¹ := by ring
      _ = X * (P : ℝ)⁻¹ * K ^ (5 - 2 * β / s + 2 * κ) := by
          rw [hHq, ← hKexp, hX]
          ring
  have hlhs0 : 0 ≤ H ^ q * (2 + Real.log H) / N := by
    have : 0 ≤ 2 + Real.log H := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ H)]
    have : 0 ≤ H ^ q := rpow_nonneg hH0.le _
    positivity
  calc CO * (H ^ q * (2 + Real.log H) / N) ^ (s / 2)
      ≤ CO * (X * (P : ℝ)⁻¹ * K ^ (5 - 2 * β / s + 2 * κ)) ^ (s / 2) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow hlhs0 hbound (by linarith)) hCO
    _ = CO * X ^ (s / 2) * (P : ℝ) ^ (-(s / 2)) *
          K ^ ((5 - 2 * β / s + 2 * κ) * (s / 2)) := by
        rw [mul_rpow (by positivity) (rpow_nonneg hK0.le _), mul_rpow hX0 (by positivity),
          inv_rpow hPpos.le, ← rpow_neg hPpos.le, ← rpow_mul hK0.le]
        ring

/-- **New tail** (beyond note (21)–(22)): the new exceptional-energy estimate at the terminal
depth `N`, with `H = A K` and the denominator scale `R = P^{(1-η)/D} K^{-20/D}`. -/
theorem volume_lowEnergy_le_new {μ D c₁ CN : ℝ} (hCN : 0 < CN)
    (hNew : ∀ H : ℝ, 1 ≤ H → ∀ R : ℝ, 2 ≤ R →
      CN * H ^ 8 * Real.log (2 + H * R) ^ 9 ≤ R ^ μ →
      ∀ N : ℕ, CN * H ^ 19 * R ^ D * Real.log (2 + H * R) ^ 19 ≤ N →
        volume {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} ≤
          ENNReal.ofReal (CN * H ^ 4 * Real.log (2 + H * R) ^ 5 / R ^ c₁))
    (hD1 : 1 ≤ D) (hD20 : D ≤ 20) (hμ : 0 ≤ μ)
    {A K C₃ κ z η τ : ℝ} (hA : 1 ≤ A) (hK : 2 ≤ K) (hC₃ : 0 < C₃) (hκ : 0 ≤ κ)
    (hη : 0 ≤ η) (hτ : 0 < τ) {P N : ℕ} (hP : 1 ≤ (P : ℝ)) (hN : 1 ≤ N)
    (hPN : (P : ℝ) ≤ 2 * (C₃ * K ^ (1 + κ)) * N)
    (hKP : K ≤ (P : ℝ) ^ z)
    (hR : 2 ≤ (P : ℝ) ^ ((1 - η - 20 * z) / D))
    (hred : CN * A ^ 8 * ((2 + A) ^ τ / τ) ^ 9 ≤
      (P : ℝ) ^ ((1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ))
    (hdepth : 2 * C₃ * CN * A ^ 19 * ((2 + A) ^ τ / τ) ^ 19 ≤
      (P : ℝ) ^ (η - 19 * τ - z * κ)) :
    volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ A * K} ≤
      ENNReal.ofReal (CN * A ^ 4 * ((2 + A) ^ τ / τ) ^ 5 *
        (P : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) * K ^ (4 + 20 * (c₁ / D))) := by
  set L := (2 + A) ^ τ / τ with hL
  set H := A * K with hH
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hD0 : 0 < D := by linarith
  have hH1 : 1 ≤ H := by nlinarith
  have hH0 : 0 < H := by linarith
  have hL0 : 0 < L := by positivity
  have hPr : ∀ x : ℝ, 0 < (P : ℝ) ^ x := fun x => rpow_pos_of_pos hP0 x
  have hKr : ∀ x : ℝ, 0 < K ^ x := fun x => rpow_pos_of_pos hK0 x
  -- the denominator scale `R`
  set R := (P : ℝ) ^ ((1 - η) / D) * K ^ (-(20 / D)) with hRdef
  have hR0 : 0 < R := mul_pos (hPr _) (hKr _)
  have hRpow : ∀ x : ℝ, R ^ x = (P : ℝ) ^ ((1 - η) / D * x) * K ^ (-(20 / D) * x) := by
    intro x
    rw [hRdef, mul_rpow (hPr _).le (hKr _).le, ← rpow_mul hP0.le, ← rpow_mul hK0.le]
  have hKneg : ∀ y : ℝ, 0 ≤ y → (P : ℝ) ^ (-(z * y)) ≤ K ^ (-y) := by
    intro y hy
    calc (P : ℝ) ^ (-(z * y)) = ((P : ℝ) ^ z) ^ (-y) := by
          rw [← rpow_mul hP0.le]
          ring_nf
      _ ≤ K ^ (-y) := rpow_le_rpow_of_nonpos hK0 hKP (by linarith)
  have hKpos : ∀ y : ℝ, 0 ≤ y → K ^ y ≤ (P : ℝ) ^ (z * y) := by
    intro y hy
    calc K ^ y ≤ ((P : ℝ) ^ z) ^ y := rpow_le_rpow hK0.le hKP hy
      _ = (P : ℝ) ^ (z * y) := by rw [← rpow_mul hP0.le]
  have hR2 : 2 ≤ R := by
    calc (2 : ℝ) ≤ (P : ℝ) ^ ((1 - η - 20 * z) / D) := hR
      _ = (P : ℝ) ^ ((1 - η) / D) * (P : ℝ) ^ (-(z * (20 / D))) := by
          rw [← rpow_add hP0]
          congr 1
          field_simp
          ring
      _ ≤ R := mul_le_mul_of_nonneg_left (hKneg _ (by positivity)) (hPr _).le
  -- the logarithm `ℓ = log(2 + H R) ≤ L P^τ`
  have hHR : H * R ≤ A * P := by
    have h1 : K * K ^ (-(20 / D)) ≤ 1 := by
      have h20 : 1 ≤ 20 / D := (le_div_iff₀ hD0).2 (by linarith)
      have := rpow_le_one_of_one_le_of_nonpos hK1 (show 1 + -(20 / D) ≤ 0 by linarith)
      rwa [rpow_add hK0, rpow_one] at this
    have h2 : (P : ℝ) ^ ((1 - η) / D) ≤ P :=
      rpow_le_self_of_one_le hP ((div_le_one hD0).2 (by linarith))
    calc H * R = A * (K * K ^ (-(20 / D))) * (P : ℝ) ^ ((1 - η) / D) := by
          rw [hH, hRdef]
          ring
      _ ≤ A * 1 * P := by gcongr
      _ = A * P := by ring
  set ℓ := Real.log (2 + H * R) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith)
  have hℓL : ℓ ≤ L * (P : ℝ) ^ τ := by
    calc ℓ ≤ Real.log ((2 + A) * P) := Real.log_le_log (by positivity) (by nlinarith)
      _ ≤ ((2 + A) * P) ^ τ / τ := log_le_rpow_div (by positivity) hτ
      _ = L * (P : ℝ) ^ τ := by
          rw [mul_rpow (by positivity) hP0.le, hL]
          ring
  have hℓpow : ∀ n : ℕ, ℓ ^ n ≤ L ^ n * (P : ℝ) ^ (n * τ) := by
    intro n
    calc ℓ ^ n ≤ (L * (P : ℝ) ^ τ) ^ n := pow_le_pow_left₀ hℓ0 hℓL n
      _ = L ^ n * (P : ℝ) ^ (n * τ) := by
          rw [mul_pow, mul_comm (n : ℝ) τ, rpow_mul_natCast hP0.le]
  -- the redundancy condition `C H⁸ ℓ⁹ ≤ R^μ`
  have hredR : CN * H ^ 8 * ℓ ^ 9 ≤ R ^ μ := by
    have hK8 : K ^ 8 = K ^ (8 + 20 * μ / D) * K ^ (-(20 / D) * μ) := by
      rw [← rpow_add hK0, ← rpow_natCast]
      congr 1
      push_cast
      ring
    have hsum : (P : ℝ) ^ ((1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ) *
        (P : ℝ) ^ (z * (8 + 20 * μ / D)) * (P : ℝ) ^ ((9 : ℕ) * τ) =
          (P : ℝ) ^ ((1 - η) / D * μ) := by
      rw [← rpow_add hP0, ← rpow_add hP0]
      congr 1
      push_cast
      ring
    have hKy : K ^ (8 + 20 * μ / D) ≤ (P : ℝ) ^ (z * (8 + 20 * μ / D)) :=
      hKpos _ (by positivity)
    calc CN * H ^ 8 * ℓ ^ 9 ≤ CN * H ^ 8 * (L ^ 9 * (P : ℝ) ^ ((9 : ℕ) * τ)) := by
          gcongr
          exact hℓpow 9
      _ = CN * A ^ 8 * L ^ 9 * K ^ (8 + 20 * μ / D) * (P : ℝ) ^ ((9 : ℕ) * τ) *
            K ^ (-(20 / D) * μ) := by
          rw [hH, mul_pow, hK8]
          ring
      _ ≤ (P : ℝ) ^ ((1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ) *
            (P : ℝ) ^ (z * (8 + 20 * μ / D)) * (P : ℝ) ^ ((9 : ℕ) * τ) *
            K ^ (-(20 / D) * μ) := by
          gcongr
      _ = R ^ μ := by rw [hsum, hRpow]
  -- the depth condition `C H¹⁹ R^D ℓ¹⁹ ≤ N`
  have hdepthN : CN * H ^ 19 * R ^ D * ℓ ^ 19 ≤ N := by
    have hy : 0 < 2 * (C₃ * K ^ (1 + κ)) := by have := hKr (1 + κ); positivity
    refine le_of_mul_le_mul_right ?_ hy
    have hRD : R ^ D = (P : ℝ) ^ (1 - η) * K ^ (-20 : ℝ) := by
      rw [hRpow]
      congr 2 <;> field_simp
    have hKk : K ^ 19 * K ^ (-20 : ℝ) * K ^ (1 + κ) = K ^ κ := by
      rw [← rpow_natCast, ← rpow_add hK0, ← rpow_add hK0]
      congr 1
      push_cast
      ring
    have hsum : (P : ℝ) ^ (η - 19 * τ - z * κ) * (P : ℝ) ^ (z * κ) * (P : ℝ) ^ (1 - η) *
        (P : ℝ) ^ ((19 : ℕ) * τ) = P := by
      rw [← rpow_add hP0, ← rpow_add hP0, ← rpow_add hP0]
      conv_rhs => rw [← rpow_one (P : ℝ)]
      congr 1
      push_cast
      ring
    calc CN * H ^ 19 * R ^ D * ℓ ^ 19 * (2 * (C₃ * K ^ (1 + κ)))
        ≤ CN * H ^ 19 * R ^ D * (L ^ 19 * (P : ℝ) ^ ((19 : ℕ) * τ)) *
            (2 * (C₃ * K ^ (1 + κ))) := by
          have : 0 ≤ R ^ D := (rpow_pos_of_pos hR0 _).le
          gcongr
          exact hℓpow 19
      _ = 2 * C₃ * CN * A ^ 19 * L ^ 19 * (K ^ 19 * K ^ (-20 : ℝ) * K ^ (1 + κ)) *
            (P : ℝ) ^ (1 - η) * (P : ℝ) ^ ((19 : ℕ) * τ) := by
          rw [hH, hRD, mul_pow]
          ring
      _ = 2 * C₃ * CN * A ^ 19 * L ^ 19 * K ^ κ * (P : ℝ) ^ (1 - η) *
            (P : ℝ) ^ ((19 : ℕ) * τ) := by rw [hKk]
      _ ≤ (P : ℝ) ^ (η - 19 * τ - z * κ) * (P : ℝ) ^ (z * κ) * (P : ℝ) ^ (1 - η) *
            (P : ℝ) ^ ((19 : ℕ) * τ) := by
          gcongr
          exact hKpos κ hκ
      _ = P := hsum
      _ ≤ N * (2 * (C₃ * K ^ (1 + κ))) := by linarith
  -- apply the new exceptional-energy estimate at the terminal depth
  have hsub : {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} ⊆
      {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} :=
    fun t ht => ⟨ht.1, ht.2 N hN le_rfl⟩
  refine (measure_mono hsub).trans
    ((hNew H hH1 R hR2 hredR N hdepthN).trans (ENNReal.ofReal_le_ofReal ?_))
  have hK4 : K ^ 4 * K ^ (-(-(20 / D) * c₁)) = K ^ (4 + 20 * (c₁ / D)) := by
    rw [← rpow_natCast, ← rpow_add hK0]
    congr 1
    push_cast
    ring
  have hP5 : (P : ℝ) ^ ((5 : ℕ) * τ) * (P : ℝ) ^ (-((1 - η) / D * c₁)) =
      (P : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) := by
    rw [← rpow_add hP0]
    congr 1
    push_cast
    ring
  calc CN * H ^ 4 * ℓ ^ 5 / R ^ c₁
      = CN * A ^ 4 * ℓ ^ 5 * (K ^ 4 * K ^ (-(-(20 / D) * c₁))) *
          (P : ℝ) ^ (-((1 - η) / D * c₁)) := by
        rw [hRpow, rpow_neg hP0.le, rpow_neg hK0.le, hH, mul_pow]
        field_simp
    _ ≤ CN * A ^ 4 * (L ^ 5 * (P : ℝ) ^ ((5 : ℕ) * τ)) *
          (K ^ 4 * K ^ (-(-(20 / D) * c₁))) * (P : ℝ) ^ (-((1 - η) / D * c₁)) := by
        have := hKr (-(-(20 / D) * c₁))
        have := hPr (-((1 - η) / D * c₁))
        gcongr
        exact hℓpow 5
    _ = CN * A ^ 4 * L ^ 5 * ((P : ℝ) ^ ((5 : ℕ) * τ) * (P : ℝ) ^ (-((1 - η) / D * c₁))) *
          (K ^ 4 * K ^ (-(-(20 / D) * c₁))) := by ring
    _ = CN * A ^ 4 * L ^ 5 * (P : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) *
          K ^ (4 + 20 * (c₁ / D)) := by rw [hP5, hK4]

end Favard.Assembly
