import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Frozen definitions for the Fourier side

These follow the normalization of the manuscript (`favard-optimized-quarter-proof.md`, section
"Fourier preparations"): the phase `e^{-iξx}` has no `2π`, `ρ = 8/3`, `c = 3/8`, and for a slope
`t ∈ [0,1]` the normalized projected construction has generation-`j` digits `±4^{-j}, ±t 4^{-j}`.
-/

open MeasureTheory Set Real

namespace Favard

/-- `φ_t(z) = (cos z + cos(tz))/2 = cos(z(1+t)/2) cos(z(1-t)/2)`, the Fourier transform of the
uniform probability measure on `{±1, ±t}`. -/
noncomputable def phi (t z : ℝ) : ℝ :=
  (cos z + cos (t * z)) / 2

/-- `ν̂_{r,t}(ξ) = ∏_{j<r} φ_t(4^{-j} ξ)`, the Fourier transform of the generation-`r` normalized
Cantor measure `ν_{r,t}`. -/
noncomputable def nuHat (r : ℕ) (t ξ : ℝ) : ℝ :=
  ∏ j ∈ Finset.range r, phi t (ξ / 4 ^ j)

/-- The normalized energy `‖f_{r,t}‖₂² = (2π)⁻¹ ∫ sinc(ρ 4^{-r} ξ / 2)² ν̂_{r,t}(ξ)² dξ`
(Plancherel form, `ρ = 8/3`). -/
noncomputable def normEnergy (r : ℕ) (t : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ ξ, sinc (4 / 3 / 4 ^ r * ξ) ^ 2 * nuHat r t ξ ^ 2

/-- The low-frequency product `P₁(t,y) = ∏_{k=0}^{m} φ_t(4^k y)`. -/
noncomputable def lowProd (m : ℕ) (t y : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (m + 1), phi t (4 ^ k * y)

/-- The high-frequency product `P₂(t,y) = ∏_{k=m+1}^{n} φ_t(4^k y)`. -/
noncomputable def highProd (m n : ℕ) (t y : ℝ) : ℝ :=
  ∏ k ∈ Finset.Ioc m n, phi t (4 ^ k * y)

/-- The one-coordinate cosine product `D(w) = ∏_{k=0}^{m-1} cos(4^k w)`. -/
noncomputable def lowD (m : ℕ) (w : ℝ) : ℝ :=
  ∏ k ∈ Finset.range m, cos (4 ^ k * w)

/-- The Riesz product `R(w) = ∏_{k=m+1}^{n} (1 + cos(4^k w))`. -/
noncomputable def riesz (m n : ℕ) (w : ℝ) : ℝ :=
  ∏ k ∈ Finset.Ioc m n, (1 + cos (4 ^ k * w))

end Favard
