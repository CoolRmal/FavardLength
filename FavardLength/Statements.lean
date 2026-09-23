import FavardLength.Squares
import FavardLength.Fourier.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Interface statements between the parts of the development

Each `Prop` below is the contract of one independently developed part. A part proves its
statement (possibly from the statements of the parts it uses) in its own files; the final
assembly in `FavardLength/Main.lean` plugs the proofs together. Keeping the contracts in this
frozen file lets the parts be developed and compiled independently.

Equation labels (G…, P…, J…, L…) refer to `references/favard-optimized-quarter-proof.md`.
-/

open MeasureTheory Set Real

namespace Favard

/-! ## Geometric side -/

/-- **Combinatorial dichotomy** (G1–G17), contrapositive form. If the depth-`NJ` projection in
direction `θ ∈ [0, π/2]` is longer than `B/K`, with `J ≥ c K log K`, then every generation
`r ≤ N` has projection energy at most `A K`. -/
def DichotomyStatement : Prop :=
  ∃ A B c : ℝ, 0 < A ∧ 0 < B ∧ 0 < c ∧
    ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K

/-- **Elementary lower bound** (L1–L2): `Fav(K_n) ≥ c/n`. -/
def LowerBoundStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c / n ≤ favardLength n

/-- **Exceptional directions** (J9), in the angle variable with geometric energies. -/
def ExceptionalAngleStatement : Prop :=
  ∀ s : ℝ, 1 / 4 ≤ s → s < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
    volume {θ ∈ Icc 0 (π / 4) | ∀ r : ℕ, 1 ≤ r → r ≤ N → energy r θ ≤ H} ≤
      ENNReal.ofReal (C * (H ^ 3 * (2 + Real.log H) / N) ^ (s / 2))

/-- **Normalization bridge** (P1): for `θ ∈ [0, π/4]` and slope `t = tan(π/4 - θ)
= (cos θ - sin θ)/(cos θ + sin θ)`, the normalized energy is `3/(8σ)` times the geometric
energy, where `σ = cos θ + sin θ`. -/
def BridgeStatement : Prop :=
  ∀ θ ∈ Icc 0 (π / 4), ∀ r : ℕ,
    normEnergy r (tan (π / 4 - θ)) = 3 / (8 * (cos θ + sin θ)) * energy r θ

/-- **Triangle (Fejér) identity**: the no-`2π` Fourier inversion formula for the triangle
function, whose Fourier transform is `ℓ² sinc(ℓξ/2)²`. -/
def TriangleStatement : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → Integrable (fun ξ : ℝ => sinc (ℓ / 2 * ξ) ^ 2) ∧
    ∀ x : ℝ, max 0 (ℓ - |x|) = (2 * π)⁻¹ * ∫ ξ, ℓ ^ 2 * sinc (ℓ / 2 * ξ) ^ 2 * cos (ξ * x)

/-! ## Fourier side, normalized slope variable `t ∈ [0,1]` -/

/-- **Exceptional directions** (J9), normalized form. -/
def NormalizedExceptionalStatement : Prop :=
  ∀ s : ℝ, 1 / 4 ≤ s → s < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
    volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} ≤
      ENNReal.ofReal (C * (H ^ 3 * (2 + Real.log H) / N) ^ (s / 2))

/-- **Frequency window with small energy** (P2), averaged over a measurable set of slopes whose
terminal normalized energy is at most `H`. The window index `n` is common to all slopes in `E`. -/
def WindowStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H → ∀ m N : ℕ, 4 * (m + 3) ≤ N →
    ∀ E : Set ℝ, E ⊆ Icc 0 1 → MeasurableSet E → (∀ t ∈ E, normEnergy N t ≤ H) →
      ∃ n : ℕ, m + 2 ≤ n ∧ 2 * n ≤ N ∧
        ∫⁻ t in E, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
            ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2) ≤
          ENNReal.ofReal (C * H * (m + 1) / N) * volume E

/-- **Annular lower bound for the high-frequency mass** (P3). -/
def AnnularStatement : Prop :=
  ∃ A₀ ca : ℝ, 0 < A₀ ∧ 0 < ca ∧ ∀ H : ℝ, 0 < H → ∀ m n : ℕ, m < n → A₀ * H ≤ 4 ^ m →
    ∀ t ∈ Icc (0 : ℝ) 1, normEnergy (n - m) t ≤ H →
      ENNReal.ofReal (ca / 4 ^ (n - m)) ≤
        ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1, ENNReal.ofReal (highProd m n t y ^ 2)

/-- **Joint negative moment** (J1), for one fixed moment exponent `s ∈ [1/4, 1/2)` at a time.
The reciprocal power is taken in `ℝ≥0∞`, where `0 ^ (-s) = ⊤`. -/
def JointMomentStatement : Prop :=
  ∀ s : ℝ, 1 / 4 ≤ s → s < 1 / 2 → ∃ A : ℝ, 0 < A ∧ ∀ m n : ℕ, m < n →
    ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
        ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2) ≤
      ENNReal.ofReal (A * ((4 : ℝ) ^ m) ^ (3 * s / 2) / 4 ^ (n - m))

/-- **Sine-cell inverse moment weighted by the Riesz product** (P4 and J2–J3), on the cells
`I_i = [iπ/L, (i+1)π/L]`, `L = 4^m`. -/
def SineCellStatement : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ m n i : ℕ, i < 4 ^ m →
    ∫⁻ w in Icc (i * π / 4 ^ m) ((i + 1) * π / 4 ^ m),
        ENNReal.ofReal |sin (4 ^ m * w)| ^ (-s) * ENNReal.ofReal (riesz m n w) ≤
      ENNReal.ofReal (C * π / 4 ^ m)

/-- **Low-frequency cell majorants** (J4–J5): nonnegative numbers dominating `D²` on each cell,
with total at most `C √L = C 2^m`. -/
def LowCellStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∃ b : ℕ → ℝ, (∀ i, 0 ≤ b i) ∧
    (∀ i : ℕ, i < 4 ^ m → ∀ w ∈ Icc ((i : ℝ) * π / 4 ^ m) ((i + 1) * π / 4 ^ m),
      lowD m w ^ 2 ≤ b i) ∧
    ∑ i ∈ Finset.range (4 ^ m), b i ≤ C * 2 ^ m

/-- **Finite Hilbert-matrix inequality** (J6). -/
def HilbertStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (b : ℕ → ℝ), (∀ i, 0 ≤ b i) →
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, b i * b j / ((i : ℝ) + j + 1) ≤
      C * ∑ i ∈ Finset.range L, b i ^ 2

end Favard
