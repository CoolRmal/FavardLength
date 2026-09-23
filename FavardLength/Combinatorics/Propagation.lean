import FavardLength.Combinatorics.Statements
import FavardLength.Combinatorics.Propagation.Coloring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Terminal selection and propagation (G13)–(G17)

We prove the contract `Favard.Comb.PropagationStatement`, the second alternative of the
combinatorial dichotomy, with the constants `c = 18/c₀` and `B = 20`.

Fix `θ ∈ [0, π/2]`, `K ≥ 2`, `N`, `J` with `μ_N(K) > c₀ K⁻²` and `J ≥ c K log K`.

1. The terminal selection (`Favard.Comb.exists_witnessed_terminal`, G13–G15) gives a witnessed
   family `W` of depth-`N` words with `μ_N(K) ≤ 9σ #W / (4^N K)`. Hence the selected fraction
   `p = #W / 4^N` satisfies `p > c₀ / (9σK) ≥ c₀ / (18K)`, and so `pJ ≥ log K`.
2. The black words of length `NJ` project into a set of length at most `σ e^{-pJ} ≤ σ/K` (G16).
3. The green words project into a set of length at most `9σ/K` (G17).

Every word of length `NJ` is black or green, so `|π_θ(K_{NJ})| ≤ 10σ/K ≤ 20/K`.
-/

open MeasureTheory Set Real Finset

namespace Favard.Comb

variable {θ : ℝ}

/-- **Selected fraction (G15)**: if `μ_N(K) > c₀ K⁻²`, the terminal words of the selection make up
a fraction at least `c₀ / (18 K)` of the depth-`N` words. -/
theorem le_card_div_of_lt_volume {N : ℕ} {K c₀ : ℝ} (hK : 0 < K) {W : Finset Word}
    (hvol : volume (superLevel N θ K) ≤ ENNReal.ofReal (9 * sig θ * #W / (4 ^ N * K)))
    (hμ : ENNReal.ofReal (c₀ / K ^ 2) < volume (superLevel N θ K)) :
    c₀ / (18 * K) ≤ #W / 4 ^ N := by
  have hσ := sig_le_two θ
  have hp0 : (0 : ℝ) ≤ #W / 4 ^ N := by positivity
  have hlt := (ENNReal.ofReal_lt_ofReal_iff'.mp (hμ.trans_le hvol)).1
  rw [show 9 * sig θ * #W / (4 ^ N * K) = 9 * sig θ * (#W / 4 ^ N) / K by field_simp,
    div_lt_div_iff₀ (by positivity) hK] at hlt
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hσ) hp0) (sq_nonneg K)]

/-- **Propagation (G13)–(G17).** For every `c₀ > 0`, if `μ_N(K) > c₀ K⁻²` and
`J ≥ (18/c₀) K log K`, then `|π_θ(K_{NJ})| ≤ 20/K`. -/
theorem propagation : PropagationStatement := by
  intro c₀ hc₀
  refine ⟨18 / c₀, 20, by positivity, by norm_num, fun θ hθ K hK N J hμ hJ => ?_⟩
  have hK0 : 0 < K := by linarith
  have hσ0 := sig_nonneg hθ
  have hσ2 := sig_le_two θ
  obtain ⟨W, hWN, hWit, hvol⟩ := exists_witnessed_terminal hθ N hK0
  have hp := le_card_div_of_lt_volume hK0 hvol hμ
  have hp0 : (0 : ℝ) ≤ #W / 4 ^ N := by positivity
  -- the black words: `σ e^{-pJ} ≤ σ/K` since `pJ ≥ log K`
  have hpJ : Real.log K ≤ #W / 4 ^ N * J := by
    have hlog : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    calc Real.log K = c₀ / (18 * K) * (18 / c₀ * K * Real.log K) := by field_simp
      _ ≤ #W / 4 ^ N * J := mul_le_mul hp hJ (by positivity) hp0
  have hexp : Real.exp (-(#W / 4 ^ N * J)) ≤ 1 / K := by
    calc Real.exp (-(#W / 4 ^ N * J)) ≤ Real.exp (-Real.log K) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / K := by rw [Real.exp_neg, Real.exp_log hK0, one_div]
  have hblack := volume_biUnion_blackWords_le hθ hWN J
  have hgreen := volume_biUnion_greenWords_le hθ (J := J) hK0 hWit
  -- every word is black or green
  rw [projLength_eq hθ, words_eq_blackWords_union_greenWords N J W, Finset.set_biUnion_union]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (measure_union_le _ _).trans ((add_le_add hblack hgreen).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : sig θ * Real.exp (-(#W / 4 ^ N * J)) ≤ sig θ * (1 / K) :=
    mul_le_mul_of_nonneg_left hexp hσ0
  have h2 : sig θ * (1 / K) + 9 * sig θ / K = 10 * sig θ / K := by ring
  have h3 : 10 * sig θ / K ≤ 20 / K := div_le_div_of_nonneg_right (by linarith) hK0.le
  linarith

end Favard.Comb
