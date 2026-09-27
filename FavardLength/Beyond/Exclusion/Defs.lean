import FavardLength.Beyond.Statements
import FavardLength.Fourier.Bridge.Digits
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shared definitions for the smooth-window exclusion

Definitions used by all sub-parts of the proof of `ExclusionStatement` (beyond note §2,
Appendices D–H). Conventions:

* `ρ = 8/3`; codes are the square codes `w : SqCode n` of the quarter development with the
  normalized centres `c_w(t) = Bridge.code t w = ∑_{j<n} d_j 4^{-j}`, `d_j ∈ {1, -1, t, -t}`.
* The **tail density** `f_{n,t}(x) = ρ⁻¹ ∑_w 1[|x - c_w(t)| ≤ ρ 4^{-n}/2]` is the manuscript's
  normalized density (beyond note §1); it has mass one, support in `[-ρ/2, ρ/2]` for `|t| ≤ 1`,
  and `∫ f_{n,t}² = normEnergy n t` (`Exclusion.integral_tailDensity_sq`).
* Fourier transforms use Mathlib's convention `f̂(ξ) = ∫ e^{-2πiξx} f(x) dx` (Appendix G (1)).
  The transform is `ψ_{n,t}(ξ) = ν̂_{n,t}(2πξ) sinc(πρ4^{-n}ξ)`, the moments are
  `M_j(ξ) = ∫ x^j e^{-2πiξx} f_{n,t}(x) dx = (-2πi)^{-j} ψ^{(j)}(ξ)`, and `Ψ(z)` is the entire
  extension of `ψ` to complex `z`.
* `A_n(x) = ∏_{j=1}^n cos(πx/4^j)` (`cosProd`); the modulus of the infinite product is
  `|A(x)| = inf_n |A_n(x)|` (`absCosProd`), a decreasing limit.
* The exceptional set `X_{B,γ,K}` (Appendix H §2) is restricted to odd pairs, the only ones
  used by `ExclusionStatement`.
* The smooth cutoff `χ(x) = s(8x-2) s(6-8x)` of Appendix G (9), with `s = Real.smoothTransition`.
-/

open MeasureTheory Set Real
open scoped Nat

namespace Favard.Exclusion

/-! ### The tail density and its Fourier transform -/

/-- The normalized tail density `f_{n,t}(x) = ρ⁻¹ ∑_w 1[|x - c_w(t)| ≤ ρ4^{-n}/2]`, `ρ = 8/3`,
summed over the `4^n` square codes (with multiplicity). -/
noncomputable def tailDensity (n : ℕ) (t x : ℝ) : ℝ :=
  3 / 8 * ∑ w : SqCode n,
    (Icc (Bridge.code t w - 4 / 3 / 4 ^ n) (Bridge.code t w + 4 / 3 / 4 ^ n)).indicator 1 x

/-- The Fourier transform `ψ_{n,t}(ξ) = ν̂_{n,t}(2πξ) · sinc(πρ4^{-n}ξ)` of the tail density
(Appendix G (1)); see `Exclusion.tailMoment_zero` and `Exclusion.fourier_tailDensity`. -/
noncomputable def tailFT (n : ℕ) (t ξ : ℝ) : ℝ :=
  nuHat n t (2 * π * ξ) * sinc (8 / 3 * π / 4 ^ n * ξ)

/-- The entire extension `Ψ_{n,t}(z) = ∫ e^{-2πizx} f_{n,t}(x) dx`, `z ∈ ℂ`. -/
noncomputable def tailFTC (n : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-2 * π * Complex.I * z * x) * tailDensity n t x

/-- The moments `M_j(ξ) = ∫ x^j e^{-2πiξx} f_{n,t}(x) dx` of the tail density, so that
`ψ^{(j)}_{n,t}(ξ) = (-2πi)^j M_j(ξ)`. -/
noncomputable def tailMoment (n : ℕ) (t : ℝ) (j : ℕ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ j * Complex.exp (↑(-2 * π * ξ * x) * Complex.I) * tailDensity n t x

/-- The Fourier transform of the centred box of mass one and width `ρ4^{-n}`, at complex `z`:
`(ρ4^{-n})⁻¹ ∫_{-ρ4^{-n}/2}^{ρ4^{-n}/2} e^{-2πizy} dy`; for real `z` it is `sinc(πρ4^{-n}z)`. -/
noncomputable def boxFTC (n : ℕ) (z : ℂ) : ℂ :=
  3 / 8 * 4 ^ n *
    ∫ y in (-(4 / 3 / 4 ^ n : ℝ))..(4 / 3 / 4 ^ n), Complex.exp (-2 * π * Complex.I * z * y)

/-- A sum of translated tail copies `g(x) = ∑_i f_{n,t}(x - β_i)` (Appendix E, G (10)). -/
noncomputable def copySum (n : ℕ) (t : ℝ) {m : ℕ} (β : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, tailDensity n t (x - β i)

/-! ### Cosine products -/

/-- The finite cosine product `A_n(x) = ∏_{j=1}^n cos(πx/4^j)`. -/
noncomputable def cosProd (n : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range n, Real.cos (π * x / 4 ^ (j + 1))

/-- The finite cosine product `A_n(z) = ∏_{j=1}^n cos(πz/4^j)` at complex `z`. -/
noncomputable def cosProdC (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, Complex.cos (π * z / 4 ^ (j + 1))

/-- The modulus `|A(x)| = inf_n |A_n(x)| = lim_n |A_n(x)|` of the infinite cosine product
`A(x) = ∏_{j ≥ 1} cos(πx/4^j)`. -/
noncomputable def absCosProd (x : ℝ) : ℝ :=
  ⨅ n : ℕ, |cosProd n x|

/-! ### Harmonics and the exceptional set -/

/-- `k` has even two-adic valuation: `k = 4^v h` with `h` odd (in particular `k ≥ 1`). -/
def IsFourPowOdd (k : ℕ) : Prop :=
  ∃ v h : ℕ, Odd h ∧ k = 4 ^ v * h

open Classical in
/-- The exceptional set `X_{B,γ,K}` of Appendix H §2, restricted to odd pairs: odd `p, q ≤ B`
for which some odd harmonic `h ≤ K` has a large complementary product
`|A(ph/2) A(qh/2)| > B^{-γ}`. -/
noncomputable def exceptionalSet (B γ : ℝ) (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (⌊B⌋₊ + 1) ×ˢ Finset.range (⌊B⌋₊ + 1)).filter fun pq =>
    Odd pq.1 ∧ Odd pq.2 ∧ ∃ h ∈ Finset.range (K + 1), Odd h ∧
      B ^ (-γ) < absCosProd (pq.1 * h / 2) * absCosProd (pq.2 * h / 2)

/-! ### The smooth window -/

/-- The smooth cutoff `χ(x) = s(8x - 2) s(6 - 8x)` of Appendix G (9): smooth, with values in
`[0,1]`, supported in `[1/4, 3/4]` and equal to one on `[3/8, 5/8]`. -/
noncomputable def cutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (8 * x - 2) * Real.smoothTransition (6 - 8 * x)

/-- **Middle-half flatness** at resolution `h = T/4^L` (Appendix E (1), G (10)): on the cells
`[c h, (c+1) h] ⊆ [T/4, 3T/4]`, the cell masses of `g` are close to `α h` in the sense
`∑_c (∫_{cell} g - α h)² ≤ e α² T h`, i.e. `‖ḡ - α‖²_{L²(T/4, 3T/4)} ≤ e α² T` for the cell
average `ḡ` (with `e = η²`). -/
def MiddleFlat (g : ℝ → ℝ) (T α e : ℝ) (L : ℕ) : Prop :=
  ∑ c ∈ Finset.Ico (4 ^ (L - 1) : ℕ) (3 * 4 ^ (L - 1)),
      ((∫ x in (c : ℝ) * (T / 4 ^ L)..((c : ℝ) + 1) * (T / 4 ^ L), g x) - α * (T / 4 ^ L)) ^ 2 ≤
    e * α ^ 2 * T * (T / 4 ^ L)

/-- The Taylor-expanded window transform of Appendix G (14):
`∑_{j ≤ J} M_j(ξ)/(j! T^j) ∑_i χ^{(j)}(β_i/T) e^{-2πiξβ_i}`, which approximates
`∫ χ(x/T) e^{-2πiξx} ∑_i f_{n,t}(x - β_i) dx` up to the Taylor remainder. -/
noncomputable def expandedWindow (J n : ℕ) (t T ξ : ℝ) {m : ℕ} (β : Fin m → ℝ) : ℂ :=
  ∑ j ∈ Finset.range (J + 1), tailMoment n t j ξ / ((j ! : ℂ) * (T : ℂ) ^ j) *
    ∑ i, ((iteratedDeriv j cutoff (β i / T) : ℝ) : ℂ) *
      Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)

end Favard.Exclusion
