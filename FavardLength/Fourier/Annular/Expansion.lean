import FavardLength.Fourier.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Code expansion of the normalized Cantor Fourier transform

The factor `φ_t(z) = (cos z + cos(tz))/2` is the average of `e^{iδz}` over the four digits
`δ ∈ {1, -1, t, -t}`. Multiplying out the product `ν̂_{r,t}(ξ) = ∏_{j<r} φ_t(4^{-j} ξ)` expresses
`ν̂_{r,t}(ξ)` as the average of `e^{iξ c_d}` over all codes `d : Fin r → Fin 4`, where
`c_d = ∑_j δ_{d j} 4^{-j}`. Multiplicities are retained: the sum runs over codes, not over the set
of points `c_d`. Consequently

`ν̂_{r,t}(ξ)² = 4^{-2r} ∑_{d, d'} cos(ξ (c_d - c_{d'}))`.

We also identify the high-frequency product with a rescaled `ν̂`:
`highProd m n t y = ν̂_{n-m,t}(4^n y)`.
-/

open Real Finset
open scoped ComplexConjugate

namespace Favard

namespace Annular

/-- The four digits `1, -1, t, -t` of the normalized construction. -/
def digit (t : ℝ) : Fin 4 → ℝ := ![1, -1, t, -t]

/-- The point `c_d = ∑_{j<r} δ_{d j} 4^{-j}` of the generation-`r` construction with code `d`. -/
noncomputable def code (r : ℕ) (t : ℝ) (d : Fin r → Fin 4) : ℝ :=
  ∑ j : Fin r, digit t (d j) / 4 ^ (j : ℕ)

/-- `φ_t(z)` is the average of `e^{iδz}` over the four digits `δ`. -/
lemma ofReal_phi (t z : ℝ) :
    (phi t z : ℂ) = (4 : ℂ)⁻¹ * ∑ k : Fin 4, Complex.exp (↑(digit t k * z) * Complex.I) := by
  simp only [Fin.sum_univ_four, digit, Complex.exp_ofReal_mul_I, phi]
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- Expansion of `ν̂_{r,t}(ξ)` as an average over codes. -/
lemma ofReal_nuHat (r : ℕ) (t ξ : ℝ) :
    (nuHat r t ξ : ℂ) =
      ((4 : ℂ) ^ r)⁻¹ * ∑ d : Fin r → Fin 4, Complex.exp (↑(ξ * code r t d) * Complex.I) := by
  unfold nuHat
  rw [Complex.ofReal_prod, Finset.prod_range]
  simp_rw [ofReal_phi]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    Fintype.prod_sum]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Complex.exp_sum, ← Finset.sum_mul]
  congr 2
  rw [code, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by ring

/-- One term of `|∑ e^{iξ c_d}|²`. -/
lemma exp_mul_conj_exp (a b : ℝ) :
    Complex.exp (↑a * Complex.I) * conj (Complex.exp (↑b * Complex.I)) =
      Complex.exp (↑(a - b) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- **Code expansion of `ν̂²`**: `ν̂_{r,t}(ξ)² = 4^{-2r} ∑_{d,d'} cos(ξ (c_d - c_{d'}))`. -/
lemma nuHat_sq (r : ℕ) (t ξ : ℝ) :
    nuHat r t ξ ^ 2 = ((4 : ℝ) ^ r)⁻¹ ^ 2 *
      ∑ d : Fin r → Fin 4, ∑ d' : Fin r → Fin 4, cos (ξ * (code r t d - code r t d')) := by
  have h : nuHat r t ξ ^ 2 = ((nuHat r t ξ : ℂ) * conj (nuHat r t ξ : ℂ)).re := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  rw [h, ofReal_nuHat, map_mul, map_sum, mul_mul_mul_comm, Finset.sum_mul_sum]
  simp_rw [exp_mul_conj_exp]
  have h4 : ((4 : ℂ) ^ r)⁻¹ * conj ((4 : ℂ) ^ r)⁻¹ = (((((4 : ℝ) ^ r)⁻¹ ^ 2 : ℝ)) : ℂ) := by
    simp [sq, map_ofNat]
  rw [h4, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [Complex.exp_ofReal_mul_I_re, mul_sub]

/-- `|φ_t(z)| ≤ 1`. -/
lemma abs_phi_le_one (t z : ℝ) : |phi t z| ≤ 1 := by
  unfold phi
  rw [abs_le]
  constructor <;>
    linarith [neg_one_le_cos z, neg_one_le_cos (t * z), cos_le_one z, cos_le_one (t * z)]

/-- `|ν̂_{r,t}(ξ)| ≤ 1`. -/
lemma abs_nuHat_le_one (r : ℕ) (t ξ : ℝ) : |nuHat r t ξ| ≤ 1 := by
  unfold nuHat
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_phi_le_one _ _

/-- `ν̂_{r,t}(ξ)² ≤ 1`. -/
lemma nuHat_sq_le_one (r : ℕ) (t ξ : ℝ) : nuHat r t ξ ^ 2 ≤ 1 :=
  (sq_le_one_iff_abs_le_one _).2 (abs_nuHat_le_one r t ξ)

@[fun_prop]
lemma continuous_nuHat (r : ℕ) (t : ℝ) : Continuous (nuHat r t) := by
  unfold nuHat phi
  fun_prop

@[fun_prop]
lemma continuous_highProd (m n : ℕ) (t : ℝ) : Continuous (highProd m n t) := by
  unfold highProd phi
  fun_prop

/-- The high-frequency product is a rescaled `ν̂`: `P₂(t, y) = ν̂_{n-m,t}(4^n y)`. -/
lemma highProd_eq_nuHat {m n : ℕ} (hmn : m ≤ n) (t y : ℝ) :
    highProd m n t y = nuHat (n - m) t (4 ^ n * y) := by
  unfold highProd nuHat
  symm
  refine Finset.prod_nbij' (fun j => n - j) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Ioc] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_Ioc] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 1
    have h4 : (4 : ℝ) ^ n = 4 ^ (n - j) * 4 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h4]
    field_simp

end Annular

end Favard
