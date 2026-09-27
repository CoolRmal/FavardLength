import FavardLength.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Interface statements for the beyond-quarter exponent

Contracts between the parts of the proof that `α_Fav ≥ 156307/625000`, following
`references/favard-beyond-quarter-complete.md` (the "beyond note"). Equation numbers `(k)` refer to
its main text, and `B.k`, `G.k`, `H.k`, `I.k` to its appendices.

* Baseline (beyond note (3), Appendix B): an improved cell-power sum for the low-frequency cosine
  product, via a discrete transfer operator on the 4-adic grid of cell centres, gives an improved
  joint negative moment and exceptional-direction estimate.
* Exclusion (beyond note (6)–(7), Appendices D–H): smooth-window exclusion of neighbourhoods of
  all odd/odd rational slopes outside a counted exceptional set.
* Coverage (beyond note §3, Appendix I): redundant odd/odd rational approximation.
* NewExceptional (beyond note (18)): exclusion and coverage bound the low-energy slope set.

The final assembly (beyond note §5–6) combines these with the combinatorial dichotomy, the
normalization bridge, and a layer-cake integration.
-/

open MeasureTheory Set Real

namespace Favard

/-- The sixth-moment dimension `d = log₄(5/4)` (beyond note (8)–(9)). -/
noncomputable def sixthMomentDim : ℝ :=
  Real.logb 4 (5 / 4)

/-- The redundancy exponent `μ = 1 - 2d - 6γ - 4ε` (beyond note (16)). -/
noncomputable def redundancyExp (γ ε : ℝ) : ℝ :=
  1 - 2 * sixthMomentDim - 6 * γ - 4 * ε

/-! ## Baseline -/

/-- **Improved cell-power sum** (Appendix B.1, discrete form): nonnegative majorants of `D_m²` on
the cells `I_i = [iπ/4^m, (i+1)π/4^m]` whose `s`-th powers sum to at most `C (4^m)^{1-β}`. -/
def CellPowerSumStatement (s β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∃ b : ℕ → ℝ, (∀ i, 0 < b i) ∧
    (∀ i : ℕ, i < 4 ^ m → ∀ w ∈ Icc ((i : ℝ) * π / 4 ^ m) ((i + 1) * π / 4 ^ m),
      lowD m w ^ 2 ≤ b i) ∧
    ∑ i ∈ Finset.range (4 ^ m), b i ^ s ≤ C * ((4 : ℝ) ^ m) ^ (1 - β)

/-- **Improved joint negative moment** (Appendix B.2, (7)). -/
def JointMomentImprovedStatement (s β : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ m n : ℕ, m < n →
    ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
        ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2) ≤
      ENNReal.ofReal (A * ((4 : ℝ) ^ m) ^ (2 * s - β) / 4 ^ (n - m))

/-- **Improved exceptional directions** (Appendix B.2, (8)), normalized slope variable. -/
def ExceptionalImprovedStatement (s β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H → ∀ N : ℕ, 1 ≤ N →
    volume {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} ≤
      ENNReal.ofReal (C * (H ^ (4 - 2 * β / s) * (2 + Real.log H) / N) ^ (s / 2))

/-! ## Exclusion, coverage, and the new exceptional estimate -/

/-- **Smooth-window exclusion with a counted exceptional set** (beyond note (6)–(7); Appendix H.4
with the sixth moment of H.5). For fixed `0 < γ < 2` and `0 < ε < 1/2`, with `ℓ = log(2 + HB)`:
outside a set of at most `C H⁴ B^{2d+6γ+2ε} ℓ⁴` pairs, every reduced odd/odd pair `p ≤ q ≤ B`
has terminal normalized energy `> H` at every slope within `c H⁻⁴ B^{-1-2ε} ℓ⁻⁵` of
`(q-p)/(q+p)`, at every depth `N ≥ C H¹⁹ B^{4-2γ+9ε} ℓ¹⁹`. -/
def ExclusionStatement (γ ε : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ H : ℝ, 1 ≤ H → ∀ B : ℝ, 2 ≤ B →
    ∃ X : Finset (ℕ × ℕ),
      (X.card : ℝ) ≤ C * H ^ 4 * B ^ (2 * sixthMomentDim + 6 * γ + 2 * ε) *
        Real.log (2 + H * B) ^ 4 ∧
      ∀ p q : ℕ, Odd p → Odd q → Nat.Coprime p q → p ≤ q → (q : ℝ) ≤ B → (p, q) ∉ X →
        ∀ N : ℕ, C * H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * Real.log (2 + H * B) ^ 19 ≤ N →
          ∀ t ∈ Icc (0 : ℝ) 1,
            |t - ((q : ℝ) - p) / ((q : ℝ) + p)| ≤
              c / (H ^ 4 * B ^ (1 + 2 * ε) * Real.log (2 + H * B) ^ 5) →
            H < normEnergy N t

/-- **Redundant odd/odd rational coverage** (Appendix I.1). For `R ≥ R₀`, `0 < r ≤ 1/R` and
`M = rR² ≥ M₀`, outside a set of measure at most `C/M`, every `x ∈ [0,1]` lies within `r` of at
least `cM` reduced fractions `p/q` with `p, q` odd, `p ≤ q` and `R/2 ≤ q ≤ R`. -/
def CoverageStatement : Prop :=
  ∃ R₀ M₀ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ R r : ℝ, R₀ ≤ R → 0 < r → r ≤ R⁻¹ → M₀ ≤ r * R ^ 2 →
    ∃ U : Set ℝ, volume U ≤ ENNReal.ofReal (C / (r * R ^ 2)) ∧
      ∀ x ∈ Icc (0 : ℝ) 1 \ U,
        c * (r * R ^ 2) ≤
          (((Finset.range (⌊R⌋₊ + 1) ×ˢ Finset.range (⌊R⌋₊ + 1)).filter fun pq : ℕ × ℕ =>
            Odd pq.1 ∧ Odd pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧ pq.1 ≤ pq.2 ∧
              R / 2 ≤ pq.2 ∧ |x - (pq.1 : ℝ) / pq.2| ≤ r).card : ℝ)

/-- **The new exceptional-energy estimate** (beyond note (17)–(19)): under the redundancy
condition `B^μ ≥ C H⁸ ℓ⁹` and the depth condition, the slopes with terminal normalized energy at
most `H` have measure at most `C H⁴ B^{-(1-2ε)} ℓ⁵`. -/
def NewExceptionalStatement (γ ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ B : ℝ, 2 ≤ B →
    C * H ^ 8 * Real.log (2 + H * B) ^ 9 ≤ B ^ redundancyExp γ ε →
    ∀ N : ℕ, C * H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * Real.log (2 + H * B) ^ 19 ≤ N →
      volume {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} ≤
        ENNReal.ofReal (C * H ^ 4 * Real.log (2 + H * B) ^ 5 / B ^ (1 - 2 * ε))

end Favard
