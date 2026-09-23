import FavardLength.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The superlevel-set estimate for the projection length (J10)

Fix the data of the combinatorial dichotomy (constants `A ≥ 1`, `B ≥ 3`, `c > 0`) and of the
exceptional-direction bound (a moment exponent `s > 0` and a constant `C_E ≥ 0`), and an auxiliary
exponent `0 < ε ≤ 1` used to absorb logarithms into powers. For a depth `P` beyond an explicit
threshold and a level `P^{-1/4} ≤ t ≤ √2` we set

* `K = B / t ≥ 2`, `J = ⌈c K log K⌉ ≥ 1`, `N = ⌊P / J⌋ ≥ 1`, `H = A K ≥ 2`.

Nesting of the approximants (`N J ≤ P`) and the dichotomy put the superlevel set
`{θ ∈ [0, π/4] : λ(π_θ K_P) > t}` inside the low-energy set
`{θ ∈ [0, π/4] : energy r θ ≤ H for 1 ≤ r ≤ N}`, whose measure is at most
`C_E (H³ (2 + log H) / N)^{s/2}` by the exceptional-direction bound. Using
`log x ≤ x^ε / ε`, `J ≤ (c/ε + 1) K^{1+ε}` and `N ≥ P / (2J)`, this is at most
`C t^{-(2+ε)s} P^{-s/2}` (manuscript (J10), with the logarithms absorbed into `t^{-εs}`).
-/

open MeasureTheory Set Real

namespace Favard.Decay

/-- The constant `2 (c/ε + 1) (2 + 1/ε) A^{3+ε} B^{4+2ε}` of the superlevel-set estimate, before
taking the power `s/2`. -/
noncomputable def tailBase (A B c ε : ℝ) : ℝ :=
  2 * (c / ε + 1) * (2 + 1 / ε) * A ^ (3 + ε) * B ^ (4 + 2 * ε)

lemma tailBase_nonneg {A B c ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) (hε : 0 < ε) :
    0 ≤ tailBase A B c ε := by
  unfold tailBase
  have : 0 ≤ A ^ (3 + ε) := rpow_nonneg hA _
  have : 0 ≤ B ^ (4 + 2 * ε) := rpow_nonneg hB _
  positivity

/-- The depth threshold `(2 (c/ε + 1) B²)²` beyond which `2 ⌈c K log K⌉ ≤ P` for every level
`t ≥ P^{-1/4}`. -/
noncomputable def depthThreshold (B c ε : ℝ) : ℝ :=
  (2 * (c / ε + 1) * B ^ 2) ^ 2

lemma one_le_depthThreshold {B c ε : ℝ} (hB : 3 ≤ B) (hc : 0 < c) (hε : 0 < ε) :
    1 ≤ depthThreshold B c ε := by
  have h1 : 1 ≤ c / ε + 1 := by
    have : 0 ≤ c / ε := by positivity
    linarith
  have h2 : 1 ≤ 2 * (c / ε + 1) * B ^ 2 := by nlinarith
  unfold depthThreshold
  nlinarith

/-- **Superlevel-set estimate (J10).** Beyond the depth threshold, for
`P^{-1/4} ≤ t ≤ √2` the set of directions `θ ∈ [0, π/4]` with `λ(π_θ K_P) > t` has measure at
most `C_E · tailBase^{s/2} · P^{-s/2} · t^{-(2+ε)s}`. -/
theorem volume_projLength_gt_le {A B c : ℝ} (hA : 1 ≤ A) (hB : 3 ≤ B) (hc : 0 < c)
    (hD : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K)
    {s CE : ℝ} (hs : 0 < s) (hCE : 0 ≤ CE)
    (hE : ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
      volume {θ ∈ Icc 0 (π / 4) | ∀ r : ℕ, 1 ≤ r → r ≤ N → energy r θ ≤ H} ≤
        ENNReal.ofReal (CE * (H ^ 3 * (2 + Real.log H) / N) ^ (s / 2)))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {P : ℕ} (hP : depthThreshold B c ε ≤ P)
    {t : ℝ} (ht0 : (P : ℝ) ^ (-(1 / 4 : ℝ)) ≤ t) (ht1 : t ≤ √2) :
    volume {θ ∈ Icc 0 (π / 4) | t < projLength P θ} ≤
      ENNReal.ofReal (CE * tailBase A B c ε ^ (s / 2) * (P : ℝ) ^ (-(s / 2)) *
        t ^ (-((2 + ε) * s))) := by
  set C3 := c / ε + 1 with hC3
  have hC3one : 1 ≤ C3 := by
    have : 0 ≤ c / ε := by positivity
    linarith
  have hP1 : (1 : ℝ) ≤ P := (one_le_depthThreshold hB hc hε0).trans hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hT0pos : 0 < (P : ℝ) ^ (-(1 / 4 : ℝ)) := rpow_pos_of_pos hPpos _
  have ht : 0 < t := lt_of_lt_of_le hT0pos ht0
  -- `1 / t ≤ P^{1/4}`
  have hinvt : t⁻¹ ≤ (P : ℝ) ^ (1 / 4 : ℝ) := by
    rw [rpow_neg hPpos.le] at ht0
    calc t⁻¹ ≤ ((P : ℝ) ^ (1 / 4 : ℝ))⁻¹⁻¹ := inv_anti₀ (by positivity) ht0
      _ = _ := inv_inv _
  -- the multiplicity threshold `K = B / t`
  set K := B / t with hK
  have hsqrt2 : √2 ≤ 3 / 2 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  have hK2 : 2 ≤ K := by
    rw [hK, le_div_iff₀ ht]
    linarith
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  -- the block length `J = ⌈c K log K⌉`
  set J := ⌈c * K * Real.log K⌉₊ with hJ
  have hJge : c * K * Real.log K ≤ J := Nat.le_ceil _
  have hJlt : (J : ℝ) < c * K * Real.log K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJpos : 0 < J := by
    have : (0 : ℝ) < J := lt_of_lt_of_le (by positivity) hJge
    exact_mod_cast this
  have hKe1 : 1 ≤ K ^ (1 + ε) := one_le_rpow hK1 (by linarith)
  have hlog_le : Real.log K ≤ K ^ ε / ε := log_le_rpow_div hK0.le hε0
  have hKK : K * K ^ ε = K ^ (1 + ε) := by rw [rpow_add hK0, rpow_one]
  have hJle : (J : ℝ) ≤ C3 * K ^ (1 + ε) := by
    calc (J : ℝ) ≤ c * K * Real.log K + 1 := hJlt.le
      _ ≤ c * K * (K ^ ε / ε) + K ^ (1 + ε) := by gcongr
      _ = C3 * K ^ (1 + ε) := by
          rw [hC3, ← hKK]
          field_simp
  -- `K^{1+ε} ≤ B² √P`, hence `2J ≤ P`
  have hK2P : K ^ (1 + ε) ≤ B ^ 2 * √P := by
    calc K ^ (1 + ε) ≤ K ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le hK1 (by linarith)
      _ = B ^ 2 * t⁻¹ ^ 2 := by rw [rpow_two, hK, div_eq_mul_inv, mul_pow]
      _ ≤ B ^ 2 * ((P : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
      _ = B ^ 2 * √P := by
          congr 1
          rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hPpos.le]
          norm_num
  have hsqrtP : 2 * C3 * B ^ 2 ≤ √P := Real.le_sqrt_of_sq_le hP
  have h2J : 2 * (J : ℝ) ≤ P := by
    have hB0 : 0 ≤ B ^ 2 := by positivity
    calc 2 * (J : ℝ) ≤ 2 * (C3 * (B ^ 2 * √P)) := by
          have := mul_le_mul_of_nonneg_left hK2P (by linarith [hC3one] : (0 : ℝ) ≤ C3)
          linarith
      _ = (2 * C3 * B ^ 2) * √P := by ring
      _ ≤ √P * √P := by gcongr
      _ = P := mul_self_sqrt hPpos.le
  -- the number of blocks `N = ⌊P / J⌋`
  set N := P / J with hN
  have hNJ : N * J ≤ P := Nat.div_mul_le_self P J
  have hP2NJ : (P : ℝ) ≤ 2 * N * J := by
    have h1 : P < N * J + J := Nat.lt_div_mul_add hJpos
    have h2 : (P : ℝ) < N * J + J := by exact_mod_cast h1
    nlinarith
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hP2NJ
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul] at hP2NJ
      linarith
    · exact h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- the energy threshold `H = A K`
  set H := A * K with hH
  have hH2 : 2 ≤ H := by nlinarith
  have hH0 : 0 < H := by linarith
  -- the superlevel set lies in the low-energy set
  have hsub : {θ ∈ Icc 0 (π / 4) | t < projLength P θ} ⊆
      {θ ∈ Icc 0 (π / 4) | ∀ r : ℕ, 1 ≤ r → r ≤ N → energy r θ ≤ H} := by
    rintro θ ⟨hθ, hlt⟩
    refine ⟨hθ, fun r _ hr => ?_⟩
    have hθ2 : θ ∈ Icc 0 (π / 2) := ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
    have hBK : B / K = t := by
      rw [hK]
      field_simp
    exact hD θ hθ2 K hK2 N J hJge
      (by rw [hBK]; exact hlt.trans_le (projLength_antitone hNJ θ)) r hr
  refine (measure_mono hsub).trans ((hE H hH2 N hN1).trans (ENNReal.ofReal_le_ofReal ?_))
  -- bounding `H³ (2 + log H) / N`
  have hHe : 1 ≤ H ^ ε := one_le_rpow (by linarith) hε0.le
  have hlogH : 2 + Real.log H ≤ (2 + 1 / ε) * H ^ ε := by
    have := log_le_rpow_div hH0.le hε0
    have h' : H ^ ε / ε = 1 / ε * H ^ ε := by ring
    nlinarith
  have hH3 : H ^ 3 * H ^ ε = A ^ (3 + ε) * K ^ (3 + ε) := by
    rw [← mul_rpow (by linarith) hK0.le, rpow_add hH0]
    norm_num
  have hinvN : (N : ℝ)⁻¹ ≤ 2 * J / P := by
    rw [inv_eq_one_div, div_le_div_iff₀ hNpos hPpos]
    linarith
  have hKpow : K ^ (3 + ε) * K ^ (1 + ε) = B ^ (4 + 2 * ε) * t ^ (-(4 + 2 * ε)) := by
    rw [← rpow_add hK0, hK, div_rpow (by linarith) ht.le, rpow_neg ht.le, div_eq_mul_inv]
    ring_nf
  have hX : H ^ 3 * (2 + Real.log H) / N ≤
      tailBase A B c ε * (P : ℝ)⁻¹ * t ^ (-(4 + 2 * ε)) := by
    have hA0 : 0 ≤ A ^ (3 + ε) := by positivity
    have hK0' : 0 ≤ K ^ (3 + ε) := by positivity
    calc H ^ 3 * (2 + Real.log H) / N
        ≤ H ^ 3 * ((2 + 1 / ε) * H ^ ε) * (2 * J / P) := by
          rw [div_eq_mul_inv]
          gcongr
      _ = (2 + 1 / ε) * (A ^ (3 + ε) * K ^ (3 + ε)) * (2 * J) * (P : ℝ)⁻¹ := by
          rw [← hH3]
          ring
      _ ≤ (2 + 1 / ε) * (A ^ (3 + ε) * K ^ (3 + ε)) * (2 * (C3 * K ^ (1 + ε))) *
            (P : ℝ)⁻¹ := by gcongr
      _ = 2 * C3 * (2 + 1 / ε) * A ^ (3 + ε) * (K ^ (3 + ε) * K ^ (1 + ε)) * (P : ℝ)⁻¹ := by
          ring
      _ = tailBase A B c ε * (P : ℝ)⁻¹ * t ^ (-(4 + 2 * ε)) := by
          rw [hKpow, tailBase, hC3]
          ring
  have hbase : 0 ≤ tailBase A B c ε :=
    tailBase_nonneg (by linarith) (by linarith) hc.le hε0
  have hXnn : 0 ≤ H ^ 3 * (2 + Real.log H) / N := by
    have : 0 ≤ 2 + Real.log H := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ H)]
    positivity
  calc CE * (H ^ 3 * (2 + Real.log H) / N) ^ (s / 2)
      ≤ CE * (tailBase A B c ε * (P : ℝ)⁻¹ * t ^ (-(4 + 2 * ε))) ^ (s / 2) := by
        gcongr
    _ = CE * tailBase A B c ε ^ (s / 2) * (P : ℝ) ^ (-(s / 2)) * t ^ (-((2 + ε) * s)) := by
        rw [mul_rpow (by positivity) (by positivity), mul_rpow hbase (by positivity),
          inv_rpow hPpos.le, ← rpow_neg hPpos.le, ← rpow_mul ht.le]
        ring_nf

end Favard.Decay
