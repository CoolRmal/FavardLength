# Plan: the beyond-quarter exponent `α_Fav ≥ 156307/625000`

Source: `references/beyond/favard-beyond-quarter-complete.md` (the "beyond note", SHA-256
`bd2183c6136399e9012c73c6eba3eee669d0687c71726a6a583076ca4902b333`), with component notes in
`references/beyond/`. Target (beyond note (1)): `Fav(K_n) ≤ C n^{-156307/625000}` for all `n ≥ 1`.
The quarter development (`PLAN.md`) is complete and reused unchanged.

## Contracts

`FavardLength/Beyond/Statements.lean` (frozen) holds the contracts. The quarter contracts in
`FavardLength/Statements.lean` (`DichotomyStatement`, `WindowStatement`, `AnnularStatement`,
`SineCellStatement`, `HilbertStatement`, `BridgeStatement`, …) are already proved; see
`FavardLength/Main.lean` for the proof terms (`dichotomy`, `window`, `annular`,
`sineCell_of meanOne`, `hilbert`, `bridge_of triangle`, …).

| Part | Files | Proves |
|---|---|---|
| CellPowerSum | `FavardLength/Beyond/CellPowerSum*.lean` | `CellPowerSumStatement (1/2 - 1/10^7) (3071/10000)` |
| JointMomentImproved | `FavardLength/Beyond/JointMoment*.lean` | `SineCellStatement → CellPowerSumStatement s β → HilbertStatement → JointMomentImprovedStatement s β` for `1/4 ≤ s < 1/2`, `0 < β ≤ s` |
| ExceptionalImproved | `FavardLength/Beyond/Exceptional*.lean` | `WindowStatement → AnnularStatement → JointMomentImprovedStatement s β → ExceptionalImprovedStatement s β` for `1/4 ≤ s < 1/2`, `0 < β < 3s/2` |
| Exclusion | `FavardLength/Beyond/Exclusion/` | `ExclusionStatement γ ε` for all `0 < γ < 2`, `0 < ε < 1/2` (lead agent designs sub-contracts) |
| Coverage | `FavardLength/Beyond/Coverage/` | `CoverageStatement` |
| NewExceptional | `FavardLength/Beyond/NewExceptional.lean` | `ExclusionStatement γ ε → CoverageStatement → 0 < redundancyExp γ ε → NewExceptionalStatement γ ε` |
| Assembly | `FavardLength/Beyond/Assembly/` | the final bound from `DichotomyStatement`, `BridgeStatement`, `ExceptionalImprovedStatement s₀ β₀`, `NewExceptionalStatement γ₀ ε₀` |

Parameters: `s₀ = 1/2 - 1/10^7`, `β₀ = 3071/10000`, `γ₀ = 13/125`, `ε₀ = 1/100000`,
`z = 1/625`. Certificates: `d = log₄(5/4) < 161/1000` because `5^1000 < 4^1161`;
`μ(γ₀, ε₀) > 1349/25000`; `D = 4 - 2γ₀ + 9ε₀ = 379209/100000`; `δ = (1 - 2ε₀)/D = 99998/379209`.

## Mathematical notes

### CellPowerSum (replaces the sampling inequality of B.1.2; no complex analysis)
Cells `I_i` have centres `c_i = (i + 1/2)π/4^m`. For `w ∈ I_i`,
`|cos(4^k w)| ≤ |cos(4^k c_i)| + ε_k` with `ε_k = (π/2) 4^{k-m}`. Take
`b_i = ∏_{k<m} (|cos(4^k c_i)| + ε_k)²` (plus a tiny positive shift if needed). For `2s ≤ 1`,
`(a + ε)^{2s} ≤ a^{2s} + ε^{2s}`, and `x^{2s} ≤ x + (1-2s)/(2s e)` on `[0,1]` (B.10 (31)). With
period-`π` weights `G_k(y) = |cos y| + κ + ε_k^{2s}`, `κ = (1-2s)/(2se)`, the grid identity
`∑_{c ∈ G_m} g(c) F(4c) = ∑_{x ∈ G_{m-1}} ∑_{j<4} g((x + jπ)/4) F(x)` (the map `c ↦ 4c mod π` is
4-to-1 from `G_m` onto `G_{m-1}`) and positivity give `∑_i b_i^s ≤ 4^m ∏_k ‖L_{G_k} 1‖_∞`. The exact
evaluation `(1/4)∑_{j<4} |cos((x + jπ)/4)| = ((1+√2) cos(x/4) + sin(x/4))/4 ≤ ρ_* = √(4+2√2)/4`
(B.10 (30)) gives `‖L_{G_k} 1‖ ≤ ρ_* + κ + ε_k^{2s}`, and `∏_k (1 + ε_k^{2s}/ρ_*)` is bounded
uniformly in `m`. The certificate `ρ_* + κ ≤ 4^{-β₀}` closes the argument.

### JointMomentImproved / ExceptionalImproved
Copy `Moment/JointMoment.lean` and `Fourier/Exceptional.lean`. Replace the concavity bound
`∑ β_i^s ≤ L^{1-s}(∑ β_i)^s` by `CellPowerSumStatement`: the prefactor becomes `L^{2s-β}`. In
J9 this gives `e ≤ C (H q L^{3-2β/s}/N)^{s/2}` with `L ≍ H` (B.2 (8)).

### NewExceptional (beyond note §4, I.5)
Coverage at slope radius `r = c' H⁻⁴ B^{-1-2ε} ℓ⁻⁵` and `R = B`. The population `cM` exceeds the
exclusion count under the redundancy hypothesis, so each covered slope `x` has a non-excluded
pair. The slope-to-parameter map `x ↦ (1-x)/(1+x)` is a 2-Lipschitz involution of `[0,1]`.

### Assembly (beyond note §5–6)
With projection threshold `λ` and `K = B_dich/λ`, `J = ⌈c K log K⌉`, `N = ⌊P/J⌋`, the dichotomy
puts `{θ ∈ [0,π/4] : L_P(θ) > λ}` in the low-energy set, and the bridge moves it to slopes (see
`Fourier/Angle.lean`). Two tails:
* old: `ExceptionalImproved` gives `≲ P^{-s/2} K^{5s/2-β} (log)^C`;
* new, for `K₀ ≤ K ≤ P^z`: `NewExceptional` with `B = (P/(K^{20}(1+log P)^{C₀}))^{1/D}` gives
  `≲ P^{-δ} K^{4+20δ} (log)^C`.

Layer cake in `λ` gives the exponents `δ - z(3+20δ)` and `s/2 + z(1+β-5s/2)`, both
`> 156307/625000`, and the strict margins absorb every logarithm. Small `n` go into the constant.

## Rules
As in `PLAN.md`: edit only your own paths; never edit frozen files (`Challenge.lean`,
`Solution.lean`, `FavardLength.lean`, `FavardLength/Statements.lean`,
`FavardLength/Beyond/Statements.lean`, and every file of the completed quarter development);
no `sorry`/`admit`/`axiom`/`native_decide` in finished work; targeted imports; at most one Lean
process at a time; lines ≤ 100 characters; files ≤ 1500 lines.
