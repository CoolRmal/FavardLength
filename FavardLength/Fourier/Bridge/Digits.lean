import FavardLength.Squares
import FavardLength.Fourier.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Projected corners in normalized coordinates

For a direction `θ` put `σ = cos θ + sin θ` and `t = (cos θ - sin θ)/σ`. Writing each binary
digit as `[b] = 1/2 + (2[b] - 1)/2`, the level-`j` contribution
`3 · 4^{-(j+1)} ([x_j] cos θ + [y_j] sin θ)` of a code to the projected corner equals
`(3σ/8) 4^{-j}` plus `(3σ/8) 4^{-j}` times a normalized digit `d_j ∈ {1, -1, t, -t}`. Hence all
projected corners are an affine image, with the common slope `a = 3σ/8`, of the normalized points
`c_w(t) = ∑_{j<r} d_j 4^{-j}`, and

`|π_θ(corner w) - π_θ(corner w')| = (3σ/8) |c_w(t) - c_{w'}(t)|`.

We also expand `∑_w e^{iξ c_w(t)} = 4^r ν̂_{r,t}(ξ)` over codes (multiplicities retained), which
gives `∑_{w,w'} cos(ξ (c_w(t) - c_{w'}(t))) = (4^r ν̂_{r,t}(ξ))²`.
-/

open Real Finset
open scoped ComplexConjugate

namespace Favard

namespace Bridge

/-- The normalized digit `1, -1, t, -t` attached to the digit pairs `(true, true)`,
`(false, false)`, `(true, false)`, `(false, true)`. -/
def digit (t : ℝ) : Bool × Bool → ℝ
  | (true, true) => 1
  | (false, false) => -1
  | (true, false) => t
  | (false, true) => -t

/-- The normalized point `c_w(t) = ∑_{j<r} d_j 4^{-j}` of the square code `w`. -/
noncomputable def code {r : ℕ} (t : ℝ) (w : SqCode r) : ℝ :=
  ∑ j : Fin r, digit t (w j) / 4 ^ (j : ℕ)

/-- One level of the projected corner in normalized coordinates. -/
lemma level_eq {σ c s : ℝ} (hσ : σ ≠ 0) (hc : c + s = σ) (p : Bool × Bool) (j : ℕ) :
    (if p.1 then (3 : ℝ) else 0) / 4 ^ (j + 1) * c +
        (if p.2 then (3 : ℝ) else 0) / 4 ^ (j + 1) * s =
      3 * σ / 8 / 4 ^ j + 3 * σ / 8 * (digit ((c - s) / σ) p / 4 ^ j) := by
  obtain ⟨a, b⟩ := p
  subst hc
  cases a <;> cases b <;> simp only [digit, Bool.false_eq_true, ↓reduceIte] <;> field_simp <;> ring

/-- **Projected corners are affine in the normalized points**: with `σ = cos θ + sin θ ≠ 0`,
`π_θ(corner w) = ∑_{j<r} (3σ/8) 4^{-j} + (3σ/8) c_w((cos θ - sin θ)/σ)`. -/
lemma proj_corner {θ : ℝ} (hσ : cos θ + sin θ ≠ 0) {r : ℕ} (w : SqCode r) :
    proj θ (corner w) = ∑ j : Fin r, 3 * (cos θ + sin θ) / 8 / 4 ^ (j : ℕ) +
      3 * (cos θ + sin θ) / 8 * code ((cos θ - sin θ) / (cos θ + sin θ)) w := by
  simp only [proj, corner, leftEnd, code, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => level_eq hσ rfl (w j) j

/-- Distances between projected corners are `3σ/8` times distances between normalized points. -/
lemma abs_proj_corner_sub {θ : ℝ} (hσ : 0 < cos θ + sin θ) {r : ℕ} (w w' : SqCode r) :
    |proj θ (corner w) - proj θ (corner w')| =
      3 * (cos θ + sin θ) / 8 * |code ((cos θ - sin θ) / (cos θ + sin θ)) w -
        code ((cos θ - sin θ) / (cos θ + sin θ)) w'| := by
  rw [proj_corner hσ.ne', proj_corner hσ.ne', add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_pos (by positivity)]

/-- The four normalized digits average `e^{iδz}` to `φ_t(z)`. -/
lemma sum_exp_digit (t z : ℝ) :
    ∑ p : Bool × Bool, Complex.exp (↑(z * digit t p) * Complex.I) = 4 * (phi t z : ℂ) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, digit, Complex.exp_ofReal_mul_I, phi]
  push_cast
  simp only [mul_neg, mul_one, Complex.cos_neg, Complex.sin_neg]
  ring_nf

/-- **Code expansion**: `∑_w e^{iξ c_w(t)} = 4^r ν̂_{r,t}(ξ)`. -/
lemma sum_exp_code (r : ℕ) (t ξ : ℝ) :
    ∑ w : SqCode r, Complex.exp (↑(ξ * code t w) * Complex.I) =
      ((4 ^ r * nuHat r t ξ : ℝ) : ℂ) := by
  have h : ∀ w : SqCode r, Complex.exp (↑(ξ * code t w) * Complex.I) =
      ∏ j : Fin r, Complex.exp (↑(ξ / 4 ^ (j : ℕ) * digit t (w j)) * Complex.I) := by
    intro w
    rw [← Complex.exp_sum, ← Finset.sum_mul, code, Finset.mul_sum]
    congr 2
    push_cast
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [← Fintype.prod_sum fun (j : Fin r) (p : Bool × Bool) =>
    Complex.exp (↑(ξ / 4 ^ (j : ℕ) * digit t p) * Complex.I)]
  simp_rw [sum_exp_digit]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, nuHat,
    Finset.prod_range fun j => phi t (ξ / 4 ^ j)]
  push_cast
  rfl

/-- One term of `|∑ e^{iξ c_w}|²`. -/
lemma exp_mul_conj_exp (a b : ℝ) :
    Complex.exp (↑a * Complex.I) * conj (Complex.exp (↑b * Complex.I)) =
      Complex.exp (↑(a - b) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- **The cosine double sum**: `∑_{w,w'} cos(ξ (c_w - c_{w'})) = (4^r ν̂_{r,t}(ξ))²`. -/
lemma sum_sum_cos_code (r : ℕ) (t ξ : ℝ) :
    ∑ w : SqCode r, ∑ w' : SqCode r, cos (ξ * (code t w - code t w')) =
      (4 ^ r * nuHat r t ξ) ^ 2 := by
  have h : ((4 ^ r * nuHat r t ξ) ^ 2 : ℝ) =
      (((4 ^ r * nuHat r t ξ : ℝ) : ℂ) * conj ((4 ^ r * nuHat r t ξ : ℝ) : ℂ)).re := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  rw [h, ← sum_exp_code, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [exp_mul_conj_exp, Complex.exp_ofReal_mul_I_re, mul_sub]

end Bridge

end Favard
