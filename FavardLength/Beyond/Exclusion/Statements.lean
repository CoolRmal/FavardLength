import FavardLength.Beyond.Exclusion.Defs

/-!
# Sub-contracts for the smooth-window exclusion

The proof of `Favard.ExclusionStatement γ ε` (beyond note §2; Appendices D–H of
`references/beyond/favard-beyond-quarter-complete.md`) is split into the following independent
parts; `Favard.exclusion_of` in `FavardLength/Beyond/Exclusion/Main.lean` derives the exclusion
statement from them.

* **(a) Complementary products** (Appendix H §§1–3, 5): the sixth-moment count of the
  exceptional set `#X_{B,γ,K} ≤ C K B^{2d+6γ}` (H (17)–(19)) and, outside it, the lower bound
  `|A_n(pk) A_n(qk)| ≥ 4 B^{γ-2}/(π² k²)` at harmonics `k = 4^v h`, `h ≤ K` odd (H (5)–(6)).
* **(b) Relative derivatives** (Appendix G §2, Appendix F): near the rational parameter the
  transform is comparable to `A_n(pk) A_n(qk)`, and its moments (i.e. its derivatives) are
  bounded by the transform times powers of `log(2 + Qk)`.
* **(c) Positive-weight harmonic** (Appendix G §3): a harmonic with even two-adic valuation and
  `k < 6m²` at which a nonnegatively weighted phase sum does not cancel.
* **(d) Flat block** (Appendices D, E): martingale selection in a low-energy density, enlarged and
  rescaled to an interval of length `T = ρ4^r`, with whole tail copies that are flat on the
  middle half at resolution `T/4^{r+L}`.
* **(e) Window bounds** (Appendix G §4): the lower copy count under the plateau of the cutoff and
  the upper bound for the Taylor-expanded window transform from flatness.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

/-- **(a) Sixth-moment count** (Appendix H (17)–(19)): `#X_{B,γ,K} ≤ C K B^{2d+6γ}` with
`d = log₄(5/4)`, uniformly in `γ`, `B ≥ 1` and the harmonic budget `K`. -/
def ComplementaryCountStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ B : ℝ) (K : ℕ), 1 ≤ B →
    ((exceptionalSet B γ K).card : ℝ) ≤ C * K * B ^ (2 * sixthMomentDim + 6 * γ)

/-- **(a) Complementary lower bound** (Appendix H (5)–(6)): for odd `p, q ≤ B` outside
`X_{B,γ,K}` and a harmonic `k = 4^v h` with `h ≤ K` odd, every finite product satisfies
`|A_n(pk) A_n(qk)| ≥ 4 B^{γ-2}/(π² k²)`. -/
def ComplementaryBoundStatement : Prop :=
  ∀ (γ B : ℝ) (K p q k v h n : ℕ), 1 ≤ B → Odd p → Odd q → (p : ℝ) ≤ B → (q : ℝ) ≤ B →
    (p, q) ∉ exceptionalSet B γ K → Odd h → h ≤ K → k = 4 ^ v * h →
      4 * B ^ (γ - 2) / (π ^ 2 * (k : ℝ) ^ 2) ≤
        |cosProd n ((p : ℝ) * k) * cosProd n ((q : ℝ) * k)|

/-- **(b) Relative derivatives at the useful harmonics** (Appendix G (6)–(7)). Let `p, q` be
odd, `Q = p + q`, `t₀ = (q - p)/Q`, let `k` have even two-adic valuation and `ξ = Qk/8` (so that
`4(1 - t₀)ξ = pk` and `4(1 + t₀)ξ = qk`). If `4|t - t₀| ξ log(2 + Qk) ≤ c₀` and
`ρ4^{-n} ξ ≤ 1/4`, then `|ψ_{n,t}(ξ)| ≥ c₁ |A_n(pk) A_n(qk)|` and every moment satisfies
`|M_j(ξ)| ≤ C_j log(2 + Qk)^j |ψ_{n,t}(ξ)|` (the constants `C_j` may depend on `j`). -/
def RelDerivStatement : Prop :=
  ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (p q k n : ℕ) (t : ℝ), Odd p → Odd q → IsFourPowOdd k → t ∈ Icc (0 : ℝ) 1 →
      4 * |t - ((q : ℝ) - p) / ((p : ℝ) + q)| * (((p : ℝ) + q) * k / 8) *
          Real.log (2 + ((p : ℝ) + q) * k) ≤ c₀ →
      8 / 3 / 4 ^ n * (((p : ℝ) + q) * k / 8) ≤ 1 / 4 →
      c₁ * |cosProd n ((p : ℝ) * k) * cosProd n ((q : ℝ) * k)| ≤
          |tailFT n t (((p : ℝ) + q) * k / 8)| ∧
        ∀ j : ℕ, ‖tailMoment n t j (((p : ℝ) + q) * k / 8)‖ ≤
          C j * Real.log (2 + ((p : ℝ) + q) * k) ^ j * |tailFT n t (((p : ℝ) + q) * k / 8)|

/-- **(c) A noncancelling harmonic for positive weights** (Appendix G (8)): for nonnegative
weights with `W₂ = ∑ w_i² > 0` and arbitrary real phases there is `k = 4^v h`, `h` odd, with
`k < 6m²` and `|∑_i w_i e^{ikθ_i}|² ≥ W₂/4`. -/
def HarmonicStatement : Prop :=
  ∀ (m : ℕ) (w θ : Fin m → ℝ), (∀ i, 0 ≤ w i) → 0 < ∑ i, w i ^ 2 →
    ∃ k : ℕ, IsFourPowOdd k ∧ (k : ℝ) < 6 * (m : ℝ) ^ 2 ∧
      (∑ i, w i ^ 2) / 4 ≤ ‖∑ i, (w i : ℂ) * Complex.exp (↑(k * θ i) * Complex.I)‖ ^ 2

/-- **(d) Flat block with cropped copies** (Appendix D (1)–(3), Appendix E (1)–(2), G (10)).
If `normEnergy N t ≤ H` and `N ≥ 16(r + L)`, there are a tail depth `n ≥ N/2 - r`, a mean
`0 < α ≤ 12H` and `m ≤ α T` whole tail copies `g = ∑_i f_{n,t}(· - β_i)`, `T = ρ4^r`, which
are flat on the middle half `[T/4, 3T/4]` at resolution `T/4^{r+L}` with squared relative
error `η² = 64ρH(r+L)/N`. (In the manuscript, `g = F` on `[ρ, T - ρ]` for the rescaled
density `F(x) = f_{N,t}(inf I + 4^{-(j₀+r)} x)`, `m = ∫ g ≤ ∫_0^T F = αT`.) -/
def FlatBlockStatement : Prop :=
  ∀ (H t : ℝ) (N r L : ℕ), 0 < H → t ∈ Icc (0 : ℝ) 1 → 2 ≤ r → 16 * (r + L) ≤ N →
    normEnergy N t ≤ H →
    ∃ (n m : ℕ) (β : Fin m → ℝ) (α : ℝ), N ≤ 2 * (n + r) ∧ 0 < α ∧ α ≤ 12 * H ∧
      (m : ℝ) ≤ α * (8 / 3 * 4 ^ r) ∧
      MiddleFlat (copySum n t β) (8 / 3 * 4 ^ r) α (512 / 3 * H * (r + L) / N) (r + L)

/-- **(e) Window bounds** (Appendix G (12), (14)–(15), (18)–(19)). Fix the Taylor order `J`.
For copies `g = ∑_i f_{n,t}(· - β_i)` flat on the middle half of `[0, T]` at resolution
`h = T/4^L` with squared error `e ≤ 1`:
* at least `αT(1/8 - √e)` of the squared cutoff weights `χ(β_i/T)²` sit on the plateau
  (G (12)); and
* the Taylor-expanded window transform at a frequency `ξ ≥ 1/4` is bounded by the Taylor
  remainder `C m/T^{J+1}` plus the flat-block upper bound `C α T (√e + h ξ + (Tξ)^{-J})`
  (flatness, averaging, and constant-mode terms). -/
def WindowBoundStatement : Prop :=
  ∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n L m : ℕ) (t T α e ξ : ℝ) (β : Fin m → ℝ),
    t ∈ Icc (0 : ℝ) 1 → 64 / 3 ≤ T → 2 ≤ L → 0 ≤ α → 0 ≤ e → e ≤ 1 → 1 / 4 ≤ ξ →
    MiddleFlat (copySum n t β) T α e L →
      α * T * (1 / 8 - √e) ≤ ∑ i, cutoff (β i / T) ^ 2 ∧
      ‖expandedWindow J n t T ξ β‖ ≤
        C * m / T ^ (J + 1) + C * α * T * (√e + T / 4 ^ L * ξ + 1 / (T * ξ) ^ J)

end Favard.Exclusion
