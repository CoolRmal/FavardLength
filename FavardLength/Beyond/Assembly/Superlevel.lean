import FavardLength.Beyond.Assembly.Geometry
import FavardLength.Beyond.Assembly.Tails

/-!
# Superlevel-set estimates for the projection length

Combining the geometric step (`Favard.Assembly.volume_projLength_gt_le_slope`) with the two
slope tails (`Favard.Assembly.volume_lowEnergy_le_old`, `Favard.Assembly.volume_lowEnergy_le_new`)
at the multiplicity threshold `K = B / u` bounds the measure of
`{θ ∈ [0, π/4] : λ(π_θ K_P) > u}`:

* for `P^{-1/3} ≤ u ≤ √2`, by a constant times `P^{-s/2} u^{-σ₁}` with
  `σ₁ = (5 - 2β/s + 2κ) s/2` (old tail);
* for `max(P^{-1/3}, B P^{-z}) ≤ u ≤ √2`, i.e. `K ≤ P^z`, by a constant times
  `P^{5τ - (1-η) c₁/D} u^{-(4 + 20 c₁/D)}` (new tail, beyond note (22)).

The lower bound `u ≥ P^{-1/3}` guarantees that the block length fits into the depth:
`(c/κ + 1) K^{1+κ} ≤ P` once `(c/κ + 1) B^{3/2} ≤ √P`.
-/

open MeasureTheory Set Real

namespace Favard.Assembly

lemma sqrt_two_le_three_halves : √2 ≤ 3 / 2 := by
  rw [sqrt_le_left (by norm_num)]
  norm_num

/-- For thresholds `P^{-1/3} ≤ u ≤ √2` the block condition `C₃ (B/u)^{1+κ} ≤ P` holds as soon as
`C₃ B^{3/2} ≤ √P`. -/
lemma blockLength_le {B C₃ κ u : ℝ} {P : ℕ} (hB : 3 ≤ B) (hC₃ : 0 ≤ C₃) (hκ2 : κ ≤ 1 / 2)
    (hP : 1 ≤ (P : ℝ)) (hPB : C₃ * B ^ (3 / 2 : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ))
    (hu0 : (P : ℝ) ^ (-(1 / 3 : ℝ)) ≤ u) (hu1 : u ≤ √2) :
    C₃ * (B / u) ^ (1 + κ) ≤ P := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu : 0 < u := lt_of_lt_of_le (rpow_pos_of_pos hP0 _) hu0
  have hK1 : 1 ≤ B / u := by
    rw [le_div_iff₀ hu]
    linarith [sqrt_two_le_three_halves]
  have hKle : B / u ≤ B * (P : ℝ) ^ (1 / 3 : ℝ) := by
    rw [div_le_iff₀ hu]
    have h13 : (P : ℝ) ^ (1 / 3 : ℝ) * (P : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← rpow_add hP0]
      norm_num
    have hB0 : 0 ≤ B * (P : ℝ) ^ (1 / 3 : ℝ) := by
      have := rpow_pos_of_pos hP0 (1 / 3 : ℝ)
      positivity
    calc B = B * ((P : ℝ) ^ (1 / 3 : ℝ) * (P : ℝ) ^ (-(1 / 3 : ℝ))) := by rw [h13, mul_one]
      _ = B * (P : ℝ) ^ (1 / 3 : ℝ) * (P : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ B * (P : ℝ) ^ (1 / 3 : ℝ) * u := mul_le_mul_of_nonneg_left hu0 hB0
  have hsq : (P : ℝ) ^ (1 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) = P := by
    rw [← rpow_add hP0]
    norm_num
  calc C₃ * (B / u) ^ (1 + κ) ≤ C₃ * (B / u) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hK1 (by linarith)) hC₃
    _ ≤ C₃ * (B * (P : ℝ) ^ (1 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow (by linarith) hKle (by norm_num)) hC₃
    _ = C₃ * B ^ (3 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) := by
        rw [mul_rpow (by linarith) (rpow_pos_of_pos hP0 _).le, ← rpow_mul hP0.le]
        norm_num
        ring
    _ ≤ (P : ℝ) ^ (1 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hPB (rpow_pos_of_pos hP0 _).le
    _ = P := hsq

/-- **Old superlevel estimate**: for `P^{-1/3} ≤ u ≤ √2`,
`|{θ ∈ [0, π/4] : λ(π_θ K_P) > u}| ≤ C P^{-s/2} B^{σ₁} u^{-σ₁}` with
`σ₁ = (5 - 2β/s + 2κ) s/2`. -/
theorem volume_superlevel_old {A B c : ℝ} (hA : 1 ≤ A) (hB : 3 ≤ B) (hc : 0 < c)
    (hD : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K)
    (hBr : BridgeStatement) {s β CO : ℝ} (hs : 0 < s) (hCO : 0 ≤ CO)
    (hOld : ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
      volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} ≤
        ENNReal.ofReal (CO * (H ^ (4 - 2 * β / s) * (2 + Real.log H) / N) ^ (s / 2)))
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) {P : ℕ} (hP : 1 ≤ (P : ℝ))
    (hPB : (c / κ + 1) * B ^ (3 / 2 : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ))
    {u : ℝ} (hu0 : (P : ℝ) ^ (-(1 / 3 : ℝ)) ≤ u) (hu1 : u ≤ √2) :
    volume {θ ∈ Icc 0 (π / 4) | u < projLength P θ} ≤
      ENNReal.ofReal (CO * (2 * (c / κ + 1) * (2 + 1 / κ) * A ^ (4 - 2 * β / s + κ)) ^ (s / 2) *
        (P : ℝ) ^ (-(s / 2)) * B ^ ((5 - 2 * β / s + 2 * κ) * (s / 2)) *
        u ^ (-((5 - 2 * β / s + 2 * κ) * (s / 2)))) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu : 0 < u := lt_of_lt_of_le (rpow_pos_of_pos hP0 _) hu0
  have hC₃ : 0 < c / κ + 1 := by positivity
  obtain ⟨N, hN1, hPN, hvol⟩ := volume_projLength_gt_le_slope (A := A) hB hc hD hBr hκ hu hu1
    (blockLength_le hB hC₃.le hκ2 hP hPB hu0 hu1)
  have hK2 : 2 ≤ B / u := by
    rw [le_div_iff₀ hu]
    linarith [sqrt_two_le_three_halves]
  have hPn : 0 < P := by exact_mod_cast hP0
  refine hvol.trans ((volume_lowEnergy_le_old hs hCO hOld hA hK2 hC₃ hκ hPn hN1 hPN).trans
    (le_of_eq ?_))
  congr 1
  rw [div_rpow (by linarith) hu.le, rpow_neg hu.le, div_eq_mul_inv]
  ring

/-- **New superlevel estimate** (beyond note (22)): for `max(P^{-1/3}, B P^{-z}) ≤ u ≤ √2`,
`|{θ ∈ [0, π/4] : λ(π_θ K_P) > u}| ≤ C P^{5τ - (1-η) c₁/D} B^{σ₂} u^{-σ₂}` with
`σ₂ = 4 + 20 c₁/D`. -/
theorem volume_superlevel_new {A B c : ℝ} (hA : 1 ≤ A) (hB : 3 ≤ B) (hc : 0 < c)
    (hD : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K)
    (hBr : BridgeStatement) {μ D c₁ CN : ℝ} (hCN : 0 < CN)
    (hNew : ∀ H : ℝ, 1 ≤ H → ∀ R : ℝ, 2 ≤ R →
      CN * H ^ 8 * Real.log (2 + H * R) ^ 9 ≤ R ^ μ →
      ∀ N : ℕ, CN * H ^ 19 * R ^ D * Real.log (2 + H * R) ^ 19 ≤ N →
        volume {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} ≤
          ENNReal.ofReal (CN * H ^ 4 * Real.log (2 + H * R) ^ 5 / R ^ c₁))
    (hD1 : 1 ≤ D) (hD20 : D ≤ 20) (hμ : 0 ≤ μ)
    {κ z η τ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) (hη : 0 ≤ η) (hτ : 0 < τ)
    {P : ℕ} (hP : 1 ≤ (P : ℝ))
    (hPB : (c / κ + 1) * B ^ (3 / 2 : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ))
    (hR : 2 ≤ (P : ℝ) ^ ((1 - η - 20 * z) / D))
    (hred : CN * A ^ 8 * ((2 + A) ^ τ / τ) ^ 9 ≤
      (P : ℝ) ^ ((1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ))
    (hdepth : 2 * (c / κ + 1) * CN * A ^ 19 * ((2 + A) ^ τ / τ) ^ 19 ≤
      (P : ℝ) ^ (η - 19 * τ - z * κ))
    {u : ℝ} (hu0 : (P : ℝ) ^ (-(1 / 3 : ℝ)) ≤ u) (huz : B * (P : ℝ) ^ (-z) ≤ u)
    (hu1 : u ≤ √2) :
    volume {θ ∈ Icc 0 (π / 4) | u < projLength P θ} ≤
      ENNReal.ofReal (CN * A ^ 4 * ((2 + A) ^ τ / τ) ^ 5 *
        (P : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) * B ^ (4 + 20 * (c₁ / D)) *
        u ^ (-(4 + 20 * (c₁ / D)))) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hu : 0 < u := lt_of_lt_of_le (rpow_pos_of_pos hP0 _) hu0
  have hC₃ : 0 < c / κ + 1 := by positivity
  obtain ⟨N, hN1, hPN, hvol⟩ := volume_projLength_gt_le_slope (A := A) hB hc hD hBr hκ hu hu1
    (blockLength_le hB hC₃.le hκ2 hP hPB hu0 hu1)
  have hK2 : 2 ≤ B / u := by
    rw [le_div_iff₀ hu]
    linarith [sqrt_two_le_three_halves]
  have hKP : B / u ≤ (P : ℝ) ^ z := by
    rw [div_le_iff₀ hu]
    have hz1 : (P : ℝ) ^ (-z) * (P : ℝ) ^ z = 1 := by
      rw [← rpow_add hP0]
      simp
    calc B = B * (P : ℝ) ^ (-z) * (P : ℝ) ^ z := by rw [mul_assoc, hz1, mul_one]
      _ ≤ u * (P : ℝ) ^ z := mul_le_mul_of_nonneg_right huz (rpow_pos_of_pos hP0 _).le
      _ = (P : ℝ) ^ z * u := mul_comm _ _
  refine hvol.trans ((volume_lowEnergy_le_new hCN hNew hD1 hD20 hμ hA hK2 hC₃ hκ.le hη hτ hP
    hN1 hPN hKP hR hred hdepth).trans (le_of_eq ?_))
  congr 1
  rw [div_rpow (by linarith) hu.le, rpow_neg hu.le, div_eq_mul_inv]
  ring

end Favard.Assembly
