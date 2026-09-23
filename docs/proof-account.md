# How the Lean proof goes

This is an informal account of the proof in this repository, written against commit `a3cb6a5` and still accurate. It
covers what the Lean code actually proves, not the manuscript
(the September 2026 manuscript *An optimized negative-moment argument for the four-corner Favard exponent*, "the manuscript"; see the README for its provenance). Labels G…, P…, J…, L… refer to
that manuscript. The four theorems in `Solution.lean` restate `Challenge.lean` word for word; `le_one_of_mem_admissibleExponents` (added after `a3cb6a5`) is `admissibleExponents_subset_Iic_one lowerBound`.
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for each of them, and
the development contains no `sorry`.

**Architecture.** `FavardLength/Statements.lean` fixes one `Prop` contract per part. Its
constants are existentially quantified; the values quoted below are the ones the proofs supply.
`FavardLength/Main.lean` chains the parts together:

```
dichotomy        := dichotomy_of_packing Comb.packing Comb.propagation
jointMoment      := jointMoment_of (sineCell_of meanOne) (lowCell_of meanOne) hilbert
exceptionalAngle := exceptionalAngle_of (normalizedExceptional_of window annular jointMoment)
                                        (bridge_of triangle)
decay            := decay_of dichotomy exceptionalAngle
exponent_bounds  := exponent_bounds_of decay lowerBound
```

## 1. Definitions and basic facts

`Defs.lean` repeats the Challenge definitions: `cantorApprox`, `fourCorner`, `proj`,
`projLength n θ` (the real value of the Lebesgue measure of the projection), `favardLength` and
`decayExponent = sSup admissibleExponents`. `Squares.lean` codes depth-`n` squares by
`Fin n → Bool × Bool` and defines `count n θ x`, the number of codes whose projected square
contains `x` (multiplicity is kept), and `energy n θ = ∫ count²`. `Fourier/Defs.lean` defines
`phi`, `nuHat`, `lowProd`, `highProd`, `lowD` and `riesz`. It also defines
`normEnergy r t = (2π)⁻¹ ∫ sinc((4/3)4^{-r}ξ)² ν̂_{r,t}(ξ)² dξ` **directly in Fourier form**.

`Basic.lean` has its proofs in `BasicProof/`. It covers the square decomposition, nesting,
`projLength ≤ √2`, and measurability of `θ ↦ projLength n θ`. Measurability comes from the set
`{(θ,x) : x ∈ π_θ(K)}` being closed for compact `K`, with no continuity argument. The remaining
facts are the reduction `favardLength_eq_quarter`, `Fav(K_n) = (4/π)∫_0^{π/4} projLength`,
`∫ count = cos θ + sin θ`, and the overlap formula `energy_eq_sum_overlap`.

## 2. Combinatorial dichotomy (`Combinatorics/`, `dichotomy_of_packing`)

`DichotomyStatement` (G1–G17, contrapositive form) says the following. Fix `θ ∈ [0,π/2]`,
`K ≥ 2` and `J ≥ cK log K`. If `projLength (N*J) θ > B/K`, then `energy r θ ≤ AK` for every
`r ≤ N`. The proof supplies **A = 648, B = 20, c = 18/c₀, c₀ = 1/(16·672)**, which gives
c = 193536. The manuscript's constants are `192√2`, `13√2` and `6√2/c₀` with `c₀ = 1/3072`.
Words are `List (Bool × Bool)` with projected intervals `wordIval`. The sub-contracts are in
`Combinatorics/Statements.lean`.

- **Packing (G6–G9)** is `packing` in `Packing.lean` and proves `Σ_{R∈𝓡} 4^{-|R|} ≤ 672 K μ_N(K)`.
  Here `𝓡 = retained` is the set of marked words with no marked proper prefix. A word is marked
  at the first crossing of `2K`, where G6 gives `2K ≤ f_m < 8K`. The local bound G8,
  `sum_retainedMeeting_le`, is `16K·4^{-k}`: there are at most `16K` depth-`k` ancestors, and
  G1 (`PrefixFree.sum_inv_four_pow_le`) applies below each one. G9, `sum_maxCells_le`, is
  `Σ 4^{-k} ≤ 42 μ_N(K)`. *Divergences:*
  - The cells are the `topCell`s of retained words. Each is the largest eligible grid ancestor
    of the grid interval that contains the word's left endpoint.
  - G9 avoids connected components. It applies the finite Vitali lemma to 7-fold enlargements,
    each of which contains an interval of length `σ4^{-k}/2` inside `{F_N ≥ K}`. The constant is
    `42 = 3·7·2` rather than the manuscript's 12, so packing gives 672 rather than 192.
- **Energy absorption (G10–G12)** is `energyAbsorption_of_packing` in `Absorption.lean`. It
  proves that `μ_N(K) ≤ c₀/K²` implies `∫F_N² ≤ 648K`.
  - G11: `F_N² ≤ 8K Σ h_R²` pointwise wherever `F_N ≥ 8K` (`Decomposition.lean`).
  - G10, exact form: `∫h_R² = 4^{-|R|}∫F_{N-|R|}²` (`Subtree.lean`).
  - G12: a discrete layer cake, `n² = Σ_{k<n}(2k+1)`, gives `18σ(8K+1)`.
  - Absorption then gives `36σ(8K+1)`, which is at most `648K` using the cruder bound `σ ≤ 2`.
- **G5 without a maximal function.** `volume_le_of_forall_heavy` in `Maximal.lean` works with
  "heavy families" and the finite Vitali lemma of `Covering.lean`. It gives `μ_N(t) ≤ 9σ/t`,
  where the manuscript has `6σ/t`.
- **Propagation (G13–G17)** is `propagation` in `Propagation.lean`. It holds for every `c₀ > 0`,
  with `c = 18/c₀` and `B = 20`.
  - Terminal selection: `exists_witnessed_terminal` yields a witnessed family `W` of depth-`N`
    words with `μ_N(K) ≤ 9σ#W/(4^N K)`. Hence `p = #W/4^N ≥ c₀/(18K)`.
  - Black words (G16) cover at most `σe^{-pJ} ≤ σ/K`.
  - Green words (G17), again via heavy families, cover at most `9σ/K` (the manuscript has
    `12σ/K`).
  - The total is at most `10σ/K ≤ 20/K`.

## 3. Elementary lower bound (`LowerBound/`, `lowerBound`)

The result is **`Fav(K_n) ≥ 1/(320n)`** for `n ≥ 1`, where the manuscript has `1/(4n+√2)`.
- L1, `one_le_projLength_mul_energy`: `λ·E ≥ 1`. Its Cauchy–Schwarz step is done through the
  pointwise AM–GM bound `2f ≤ f²/E + E·1_S`.
- L2, `integral_sum_overlap_le`: `∫_0^{π/4} Σ overlap ≤ 80(n+1)`. It uses `σ ≤ 2`, corner
  separation `≥ ½·4^{-k}`, and an angular lemma `|θ'−θ| ≤ 5δ/d`. The angular lemma comes from a
  rotation identity and Jordan's inequality instead of the arcsine computation.
- Cauchy–Schwarz in `θ` is replaced by the tangent-line bound `λ ≥ 1/E ≥ 2t − t²E`, integrated
  over `[0,π/4]` with `t = 1/(2M)` and `M = 80(n+1)`.

## 4. Moment estimates (`Moment/`)

**MeanOne (`meanOne`).** For `β > 0` and finite `S ⊆ [a,∞)`,
`∫_x^{x+2π/(β4^a)} ∏_{k∈S}(1+cos(β4^k w)) dw = 2π/(β4^a)`. The proof inducts on `S`, removing the
minimum `k₀`. The cross term is *antiperiodic*, with antiperiod `π/(β4^{k₀})`, so it integrates to
zero. The code uses neither the manuscript's argument about the constant Fourier coefficient nor
the quarter-period sum `Σ_{q<4}cos(x+qπ/2)=0` suggested in `PLAN.md`.

**Hilbert (`hilbert`).** The finite Hilbert matrix inequality J6 holds with **constant 4**. The
proof is a Schur test with weights `√(i+1)`; its row sums are at most 4 by telescoping.

**SineCell (`sineCell_of`).** For `0 < s < 1/2`, `∫_{I_i}|sin(Lw)|^{-s}R ≤ Cπ/L` with
`C = 9/(1−4^s/2)`.
- P4 (`integral_riesz_le_two_pow`) is `∫_x^{x+ℓ}R ≤ 2^j(ℓ + 2π/4^{m+j+1})` for every `j`.
- J3 replaces the layer-cake identity. Jordan's inequality gives `|sin(Lw)| ≥ (2L/π)·dist(w,
  nearer endpoint)`. Around each endpoint, base-4 layers carry weight at most `4^{sk}` and mass at
  most `2^{-k}(…)`; they sum geometrically because `4^s/2 < 1`.
- The constant is stated as `9/(1−4^s/2)`, not tracked in the manuscript's form `C d⁻¹`.

**LowCell (`lowCell_of`).** The constant is **`C = 2+4π²`**, with majorants
`b_i = (2/h)∫_{I_i}D² + 2h∫_{I_i}D'²` (`sq_le_of_hasDerivAt`). The sums use
`∫_0^π D² = π2^{-m}` (mean-one with `β = 2`) and `∫_0^π D'² ≤ 2π·4^{2m}2^{-m}`. The second bound
applies Cauchy–Schwarz to `D' = Σ_k(∏_{j≠k}cos)(−4^k sin)`, then the mean-one lemma for products
with one factor removed. **No Parseval** is used. The majorants are integrals, not
`sup_{I_i} D²`.

**JointMoment (`jointMoment_of`).** For each `s ∈ [1/4,1/2)`,
`∫_0^1∫_{3/(8L)}^1 |P₁|^{-s}P₂² ≤ A·L^{3s/2}/4^{n−m}`, in `lintegral` form with reciprocal powers
in `ℝ≥0∞`. The constant is `A = 12·C_S²·π·C_H·4^s(C_L+1)^s`. The ingredients are:
- the identities `P₁ = A_m(u)A_m(v)`, `P₂² = R(u)R(v)/M` and the telescoping identity
  `sin(4^m w) = 2·4^m sin(w/2)D(w)A_m(w)`;
- the change of variables, taken from Mathlib's Jacobian formula (`lintegral_comp_uvMap`);
- J7 as `1/(u+v) ≤ 12L/(π(i+j+1))`;
- SineCell applied twice, and Hilbert applied to `(2L√β_i)^s` with `β_i = b_i + 4^{-m} > 0`;
- concavity, `Σβ_i^s ≤ L^{1−s}(Σβ_i)^s`.

`A` depends on `s` through `C_S`. The manuscript's `C d^{-2}` uniformity is not proved.

## 5. Fourier side (`Fourier/`)

**Window (`window`), P2**, with **`C = 72π`**. Let `E ⊆ [0,1]` be measurable with
`normEnergy N t ≤ H` on `E`, and let `4(m+3) ≤ N`. Then some `n` with `m+2 ≤ n` and `2n ≤ N`
satisfies `∫_E∫_{3/(8L)}^1 4^n(P₁P₂)² ≤ C·H(m+1)/N·|E|`. The proof:
- the windows `n_k = m+2+k(m+1)` are pairwise **disjoint**, which replaces the overlap count;
- `sinc² ≥ 1/2` on the windows;
- pigeonhole is applied to the `E`-average, with no Markov subset;
- the tail factors have product at least `2/3`, which replaces `∏cos(4^{-j}) > 0`.

No Plancherel is needed, because `normEnergy` is already a Fourier integral.

**Annular (`annular`), P3**, with **`A₀ = 16π`, `c_a = 1/4`**. If `16πH ≤ 4^m` and
`normEnergy (n−m) t ≤ H`, then `∫_{3/(8L)}^1 P₂² ≥ 1/(4M)`. It uses a *one-sided* triangle weight
on `[0,1]` in place of the two-sided weight plus evenness. Expanding over codes gives
`∫_0^1P₂² ≥ 1/(2M)`, and the central part is `∫_0^{3/(8L)}P₂² ≤ 4π·normEnergy/4^n`.

**Exceptional (`normalizedExceptional_of`), J9 in `t`.** For `s ∈ [1/4,1/2)`,
`|{t∈[0,1] : normEnergy r t ≤ H, 1≤r≤N}| ≤ C(H³(2+log H)/N)^{s/2}`. This is the **integrated
form**:
- The pointwise split `q² ≤ a^{-2}(pq)² + a^s|p|^{-s}q²`, integrated over `E`, gives
  `c_a|E| ≤ P|E|/a² + D a^s` for every `a > 0`.
- `le_of_forall_threshold` optimizes over `a`. Neither the Markov subset `E_*` nor a single
  selected parameter is used.
- The scale is `4^m ∈ [A₀H, max(1,4A₀H)]`, and depths `N < 4(m+3)` are absorbed into the constant.
- `E` is measurable because `t ↦ normEnergy r t` is measurable as a parametric integral of a
  jointly continuous integrand. Continuity of `normEnergy` itself, which `PLAN.md` proposed, is
  not used.
- The constant `max(C₁,C₂)` depends on `s`.

**Triangle (`triangle`).** `(ℓ−|x|)_+ = (2π)⁻¹∫ℓ²sinc(ℓξ/2)²cos(ξx)dξ`. The proof computes the
Fourier transform `ℓ²sinc(πℓw)²` explicitly and applies Mathlib's
`Integrable.fourierInv_fourier_eq`.

**Bridge (`bridge_of`), P1.** For `θ ∈ [0,π/4]`,
`normEnergy r (tan(π/4−θ)) = 3/(8σ)·energy r θ`. The proof chains:
- the overlap formula;
- projected corners, which are `3σ/8` times normalized points;
- the triangle identity with `ℓ = (8/3)4^{-r}`;
- `Σ_{w,w'}cos = (4^r ν̂)²`.

This **Fourier inversion for the triangle replaces the manuscript's rescaling-plus-Plancherel
argument**. Plancherel is used nowhere in the development.

**Angle (`exceptionalAngle_of`).** This moves J9 to angles with the *same* constant. It uses
`3/(8σ) ≤ 1` and the 1-Lipschitz inverse `t ↦ π/4 − arctan t` (via a Hausdorff-measure lemma),
not `|dt/dθ| ∈ [1,2]`.

## 6. Decay (`Decay.lean`, `decay_of`), J10–J11

For every `a ∈ [0,1/4)` there is `C > 0` with `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`. The proof
uses a **fixed** exponent `s = (max(1/4,2a)+1/2)/2`, which lies in `[1/4,1/2)` and satisfies
`a < s/2`, together with `ε = 1−2s` and `σ' = (2+ε)s < 1`.
- `volume_projLength_gt_le` (`Decay/Tail.lean`) takes `P ≥ (2(c/ε+1)B²)²` and
  `P^{-1/4} ≤ t ≤ √2`. It sets `K = B/t`, `J = ⌈cK log K⌉`, `N = ⌊P/J⌋` and `H = AK`. Nesting and
  the dichotomy then give `|{θ∈[0,π/4] : λ_P(θ) > t}| ≤ C_E·tailBase^{s/2}·P^{-s/2}·t^{-(2+ε)s}`.
  Logarithms are absorbed through `log x ≤ x^ε/ε`.
- A layer-cake bound (`Decay/LayerCake.lean`) and `favardLength_eq_quarter` give
  `Fav(K_P) ≤ P^{-1/4} + (4/π)M₀I·P^{-s/2}`. Small depths use `Fav ≤ √2`.

*Divergences:*
- There is no depth-dependent `s = (1−Q⁻¹)/2`, so the logarithmic bound J12,
  `CP^{-1/4}(2+log P)^{7/2}`, is **not** formalized.
- The energy threshold is `AK` on geometric energies. The manuscript's `192σK → 72K` step is not
  used.

## 7. Exponent (`Exponent.lean`, `exponent_bounds_of`)

The lower bound shows that every admissible exponent is at most 1, because `n^{1−a} → 0`
otherwise. Since 0 is admissible, the set is nonempty and bounded, and for any `b < 1/4` there is
an admissible `a ∈ (b,1/4)`. Together these give `1/4 ≤ α_Fav ≤ 1`.

The manuscript's section "Optimization and the limitation of this uniform moment method" has no
Lean counterpart.

## Modules

Line counts are from `wc -l`, 8525 lines in total under `FavardLength/`.

| Part | Files | Lines | Main declaration |
|---|---|---:|---|
| Defs, Squares, Fourier/Defs, Statements, Basic | 5 | 378 | contracts |
| BasicProof/ | 5 | 556 | `BasicProof.*` |
| Combinatorics/ (incl. Packing/, Propagation/) | 20 | 3121 | `dichotomy_of_packing` |
| LowerBound/ | 5 | 702 | `lowerBound` |
| Moment/MeanOne | 1 | 108 | `meanOne` |
| Moment/Hilbert | 1 | 161 | `hilbert` |
| Moment/SineCell (+Mass) | 2 | 365 | `sineCell_of` |
| Moment/LowCell (+Pointwise) | 2 | 279 | `lowCell_of` |
| Moment/JointMoment (+4) | 5 | 631 | `jointMoment_of` |
| Fourier/Window (+Bounds) | 2 | 417 | `window` |
| Fourier/Annular (+3) | 4 | 423 | `annular` |
| Fourier/Exceptional (+2) | 3 | 339 | `normalizedExceptional_of` |
| Fourier/Triangle | 1 | 207 | `triangle` |
| Fourier/Bridge (+Digits) | 2 | 218 | `bridge_of` |
| Fourier/Angle | 1 | 95 | `exceptionalAngle_of` |
| Decay (+LayerCake, Tail) | 3 | 409 | `decay_of` |
| Exponent | 1 | 60 | `exponent_bounds_of` |
| Main | 1 | 56 | `decay`, `exponent_bounds` |
