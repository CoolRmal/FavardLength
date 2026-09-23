import FavardLength.Decay.LayerCake
import FavardLength.Decay.Tail
import FavardLength.Statements

/-!
# Polynomial decay of the Favard length (J10–J11)

From the combinatorial dichotomy (`DichotomyStatement`) and the exceptional-direction bound
(`ExceptionalAngleStatement`) we prove that every exponent `a ∈ [0, 1/4)` is admissible:
`Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`.

Given `a`, we use the fixed moment exponent `s = (max(1/4, 2a) + 1/2)/2 ∈ [1/4, 1/2)`, which
satisfies `a < s/2`, and the auxiliary exponent `ε = 1 - 2s ∈ (0, 1]`, so that
`σ = (2 + ε) s < 1`. For depths `P` beyond `Decay.depthThreshold`, the superlevel-set estimate
`Decay.volume_projLength_gt_le` (J10) bounds `|{θ ∈ [0, π/4] : λ(π_θ K_P) > t}|` by
`M P^{-s/2} t^{-σ}` for `P^{-1/4} ≤ t ≤ √2`; the layer-cake bound
`Decay.intervalIntegral_le_of_meas_lt_le` and the symmetry reduction `favardLength_eq_quarter`
then give `Fav(K_P) ≤ P^{-1/4} + C P^{-s/2} ≤ C' P^{-a}` (J11). Small depths are absorbed into
the constant through `Fav(K_P) ≤ √2`.
-/

open MeasureTheory Set Real

namespace Favard

/-- **Polynomial decay of the Favard length (J10–J11).** The dichotomy and the
exceptional-direction bound imply `Fav(K_n) ≤ C n^{-a}` for every `a ∈ [0, 1/4)`. -/
theorem decay_of (hD : DichotomyStatement) (hE : ExceptionalAngleStatement) :
    ∀ a : ℝ, 0 ≤ a → a < 1 / 4 → ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      favardLength n ≤ C * (n : ℝ) ^ (-a) := by
  intro a ha0 ha1
  -- the moment exponent `s`
  set s := (max (1 / 4) (2 * a) + 1 / 2) / 2 with hs_def
  have hs1 : 1 / 4 ≤ s := by
    have := le_max_left (1 / 4 : ℝ) (2 * a)
    linarith
  have hs2 : s < 1 / 2 := by
    have : max (1 / 4 : ℝ) (2 * a) < 1 / 2 := max_lt (by norm_num) (by linarith)
    linarith
  have hs3 : a < s / 2 := by
    have := le_max_right (1 / 4 : ℝ) (2 * a)
    linarith
  obtain ⟨CE, hCE, hEs⟩ := hE s hs1 hs2
  -- the dichotomy, with `A ≥ 1` and `B ≥ 3`
  obtain ⟨A₀, B₀, c, -, -, hc, hD₀⟩ := hD
  set A := max A₀ 1 with hA_def
  set B := max B₀ 3 with hB_def
  have hA : 1 ≤ A := le_max_right _ _
  have hB : 3 ≤ B := le_max_right _ _
  have hD' : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K := by
    intro θ hθ K hK N J hJ hlt r hr
    have hK0 : 0 < K := by linarith
    have h1 : B₀ / K ≤ B / K := div_le_div_of_nonneg_right (le_max_left _ _) hK0.le
    exact (hD₀ θ hθ K hK N J hJ (h1.trans_lt hlt) r hr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le)
  -- the auxiliary exponents `ε` and `σ = (2 + ε) s < 1`
  set ε := 1 - 2 * s with hε_def
  have hε0 : 0 < ε := by linarith
  have hε1 : ε ≤ 1 := by linarith
  set σ := (2 + ε) * s with hσ_def
  have hσ : σ < 1 := by nlinarith
  -- the constants
  set P₀ := Decay.depthThreshold B c ε with hP₀_def
  have hP₀ : 1 ≤ P₀ := Decay.one_le_depthThreshold hB hc hε0
  set I := ∫ t in (0)..√2, t ^ (-σ) with hI_def
  have hI : 0 ≤ I :=
    intervalIntegral.integral_nonneg (sqrt_nonneg _) fun t ht => rpow_nonneg ht.1 _
  set M₀ := CE * Decay.tailBase A B c ε ^ (s / 2) with hM₀_def
  have hM₀ : 0 ≤ M₀ :=
    mul_nonneg hCE.le (rpow_nonneg
      (Decay.tailBase_nonneg (by linarith) (by linarith) hc.le hε0) _)
  have hP₀a : 0 ≤ √2 * P₀ ^ a := mul_nonneg (sqrt_nonneg _) (rpow_nonneg (by linarith) _)
  have hMI : 0 ≤ 4 / π * M₀ * I := mul_nonneg (mul_nonneg (by positivity) hM₀) hI
  refine ⟨√2 * P₀ ^ a + 1 + 4 / π * M₀ * I, by linarith, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 0 ≤ (n : ℝ) ^ (-a) := rpow_nonneg hn0.le _
  rcases lt_or_ge (n : ℝ) P₀ with hlt | hge
  · -- small depths: `Fav(K_n) ≤ √2 ≤ √2 P₀^a n^{-a}`
    have h2 : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
      rw [← rpow_add hn0]
      simp
    have h3 : (n : ℝ) ^ a ≤ P₀ ^ a := rpow_le_rpow hn0.le hlt.le ha0
    calc favardLength n ≤ √2 := favardLength_le_sqrt_two n
      _ = √2 * ((n : ℝ) ^ a * (n : ℝ) ^ (-a)) := by rw [h2, mul_one]
      _ ≤ √2 * (P₀ ^ a * (n : ℝ) ^ (-a)) := by gcongr
      _ = (√2 * P₀ ^ a) * (n : ℝ) ^ (-a) := by ring
      _ ≤ (√2 * P₀ ^ a + 1 + 4 / π * M₀ * I) * (n : ℝ) ^ (-a) := by
          gcongr
          linarith
  · -- large depths: layer cake with the superlevel-set estimate (J10)
    have hint := Decay.intervalIntegral_le_of_meas_lt_le (measurable_projLength n)
      (projLength_nonneg n) (b := π / 4) (T₀ := (n : ℝ) ^ (-(1 / 4 : ℝ))) (U := √2)
      (M := M₀ * (n : ℝ) ^ (-(s / 2))) (σ := σ) (by positivity) (rpow_nonneg hn0.le _)
      (sqrt_nonneg _) (mul_nonneg hM₀ (rpow_nonneg hn0.le _)) hσ (projLength_le_sqrt_two n)
      (fun t ht0 ht1 =>
        Decay.volume_projLength_gt_le hA hB hc hD' (by linarith) hCE.le hEs hε0 hε1 hge ht0
          ht1.le)
    have hq : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (n : ℝ) ^ (-a) :=
      rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hsq : (n : ℝ) ^ (-(s / 2)) ≤ (n : ℝ) ^ (-a) :=
      rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [favardLength_eq_quarter]
    calc 4 / π * ∫ θ in (0)..(π / 4), projLength n θ
        ≤ 4 / π * (π / 4 * (n : ℝ) ^ (-(1 / 4 : ℝ)) + M₀ * (n : ℝ) ^ (-(s / 2)) * I) := by
          gcongr
      _ = (n : ℝ) ^ (-(1 / 4 : ℝ)) + 4 / π * M₀ * I * (n : ℝ) ^ (-(s / 2)) := by
          field_simp
      _ ≤ (n : ℝ) ^ (-a) + 4 / π * M₀ * I * (n : ℝ) ^ (-a) := by gcongr
      _ ≤ (√2 * P₀ ^ a + 1 + 4 / π * M₀ * I) * (n : ℝ) ^ (-a) := by nlinarith

end Favard
