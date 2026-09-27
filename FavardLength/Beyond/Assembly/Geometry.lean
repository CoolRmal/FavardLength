import FavardLength.Basic
import FavardLength.Fourier.Angle

/-!
# From long projections to low-energy slopes

Fix the data of the combinatorial dichotomy (constants `A`, `B ≥ 3`, `c > 0`) and an exponent
`κ > 0` used to absorb the logarithm in the block length. For a projection threshold
`0 < u ≤ √2` we set (beyond note §5, with the dichotomy in place of linear propagation)

* `K = B / u ≥ 2`, `J = ⌈c K log K⌉ ≤ (c/κ + 1) K^{1+κ}`, `N = ⌊P / J⌋`.

If `(c/κ + 1) K^{1+κ} ≤ P`, then `N ≥ 1` and `P ≤ 2 (c/κ + 1) K^{1+κ} N`. Nesting of the
approximants (`N J ≤ P`) and the dichotomy show that every direction `θ ∈ [0, π/4]` with
`λ(π_θ K_P) > u` has geometric energy at most `A K` at every generation `r ≤ N`. The
normalization bridge turns this into the normalized bound `normEnergy r t ≤ A K` at the slope
`t = tan(π/4 - θ)`, and the `1`-Lipschitz inverse slope map `t ↦ π/4 - arctan t`
(`Favard.AngleTransfer.volume_image_le`) moves the measure estimate to slopes.
-/

open MeasureTheory Set Real

namespace Favard.Assembly

/-- **Geometric step.** Long projections at depth `P` have low energy at every generation up to
a depth `N ≥ P / (2 (c/κ + 1) K^{1+κ})`, measured in the slope variable. -/
theorem volume_projLength_gt_le_slope {A B c : ℝ} (hB : 3 ≤ B) (hc : 0 < c)
    (hD : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K)
    (hBr : BridgeStatement) {κ : ℝ} (hκ : 0 < κ) {P : ℕ} {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ √2) (hJP : (c / κ + 1) * (B / u) ^ (1 + κ) ≤ P) :
    ∃ N : ℕ, 1 ≤ N ∧ (P : ℝ) ≤ 2 * ((c / κ + 1) * (B / u) ^ (1 + κ)) * N ∧
      volume {θ ∈ Icc 0 (π / 4) | u < projLength P θ} ≤
        volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ A * (B / u)} := by
  set K := B / u with hK
  have hsqrt2 : √2 ≤ 3 / 2 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  have hK2 : 2 ≤ K := by
    rw [hK, le_div_iff₀ hu0]
    linarith
  have hK0 : 0 < K := by linarith
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  set C₃ := c / κ + 1 with hC₃
  -- the block length `J = ⌈c K log K⌉`
  set J := ⌈c * K * Real.log K⌉₊ with hJ
  have hJge : c * K * Real.log K ≤ J := Nat.le_ceil _
  have hJlt : (J : ℝ) < c * K * Real.log K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJpos : 0 < J := by
    have : (0 : ℝ) < J := lt_of_lt_of_le (by positivity) hJge
    exact_mod_cast this
  have hKe1 : 1 ≤ K ^ (1 + κ) := one_le_rpow hK1 (by linarith)
  have hlog_le : Real.log K ≤ K ^ κ / κ := log_le_rpow_div hK0.le hκ
  have hKK : K * K ^ κ = K ^ (1 + κ) := by rw [rpow_add hK0, rpow_one]
  have hJle : (J : ℝ) ≤ C₃ * K ^ (1 + κ) := by
    calc (J : ℝ) ≤ c * K * Real.log K + 1 := hJlt.le
      _ ≤ c * K * (K ^ κ / κ) + K ^ (1 + κ) := by gcongr
      _ = C₃ * K ^ (1 + κ) := by
          rw [hC₃, ← hKK]
          field_simp
  have hJP' : J ≤ P := by exact_mod_cast hJle.trans hJP
  -- the number of blocks `N = ⌊P / J⌋`
  set N := P / J with hN
  have hNJ : N * J ≤ P := Nat.div_mul_le_self P J
  have hN1 : 1 ≤ N := (Nat.le_div_iff_mul_le hJpos).2 (by simpa using hJP')
  have hP2 : (P : ℝ) ≤ 2 * (C₃ * K ^ (1 + κ)) * N := by
    have h1 : P < N * J + J := Nat.lt_div_mul_add hJpos
    have h2 : (P : ℝ) < N * J + J := by exact_mod_cast h1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hJ0 : (0 : ℝ) ≤ J := by positivity
    have h3 : (J : ℝ) ≤ N * J := by nlinarith
    have h4 : (N : ℝ) * J ≤ N * (C₃ * K ^ (1 + κ)) :=
      mul_le_mul_of_nonneg_left hJle (by positivity)
    linarith
  refine ⟨N, hN1, hP2, ?_⟩
  -- the superlevel set lies in the image of the low-energy slope set
  refine le_trans (measure_mono ?_) (AngleTransfer.volume_image_le _)
  rintro θ ⟨hθ, hlt⟩
  refine ⟨tan (π / 4 - θ), ⟨AngleTransfer.tan_mem_Icc hθ, fun r _ hr => ?_⟩,
    AngleTransfer.sub_arctan_tan hθ⟩
  have hθ2 : θ ∈ Icc 0 (π / 2) := ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
  have hBK : B / K = u := by
    rw [hK]
    field_simp
  have hE := hD θ hθ2 K hK2 N J hJge
    (by rw [hBK]; exact hlt.trans_le (projLength_antitone hNJ θ)) r hr
  have hσ := AngleTransfer.one_le_cos_add_sin hθ
  have hc' : 3 / (8 * (cos θ + sin θ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [hBr θ hθ r]
  calc 3 / (8 * (cos θ + sin θ)) * energy r θ ≤ 1 * energy r θ := by
        gcongr
        exact energy_nonneg r θ
    _ = energy r θ := one_mul _
    _ ≤ A * K := hE

end Favard.Assembly
