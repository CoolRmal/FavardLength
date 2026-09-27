# FavardLength

A Lean 4 + Mathlib proof that the Favard length of the four-corner Cantor set satisfies
`Fav(K_n) ≤ C n^{-156307/625000}`, so its decay exponent satisfies
`α_Fav ≥ 156307/625000 = 0.2500912 > 1/4`. The development also proves the intermediate result
that every exponent below `1/4` is admissible.

## The problem

Let `C_n ⊆ [0,1]` be the depth-`n` approximant of the middle-half Cantor set. It is the union,
over digit strings `w ∈ {0,3}^n`, of the `2^n` intervals
`[∑_{j=1}^n w_j 4^{-j}, ∑_{j=1}^n w_j 4^{-j} + 4^{-n}]`. The four-corner (Garnett) approximant
is `K_n = C_n × C_n`, a union of `4^n` squares of side `4^{-n}`. Its Favard length

```
Fav(K_n) = (1/π) ∫_0^π |π_θ(K_n)| dθ,   π_θ(x, y) = x cos θ + y sin θ,
```

is the average length of its projections. Equivalently, up to a constant factor, it is the
probability that Buffon's needle, dropped near the set, meets `K_n`. The limit set is purely
unrectifiable, so `Fav(K_n) → 0` (Besicovitch). The problem is the rate. The decay exponent is

```
α_Fav = sup { a ≥ 0 : Fav(K_n) ≤ C n^{-a} for some C > 0 and all n ≥ 1 }.
```

Known bounds before this work:

* Upper bounds on `α_Fav`: `α_Fav ≤ 1`. Mattila (1990) proved `Fav(K_n) ≳ 1/n`; Bateman–Volberg
  (2010) proved `Fav(K_n) ≳ log n / n`. The expected answer is `α_Fav = 1`.
* Lower bounds on `α_Fav`:
  * Peres–Solomyak (2002) gave the first rate, `exp(−c log* n)`.
  * Nazarov–Peres–Volberg (2010) gave the first power law, `α_Fav ≥ 1/6`. This is still the
    value in Tao's optimization-constants registry (constant 60a). NPV remark that decay
    faster than `n^{-1/4}` would need new ideas.
  * Marshall (arXiv:2509.02882 v2, August 2026) improved the combinatorial propagation to reach
    `α_Fav ≥ 1/5`. His v1 (September 2025) had claimed `1/4`. v2 withdraws that claim as not
    justified by its methods, and names the missing ingredient: a weighted low-frequency
    estimate that saves one power of the multiplicity threshold.

[`docs/literature.md`](docs/literature.md) records the literature search, with every query run.

## Results

[`Challenge.lean`](Challenge.lean) states, with literal definitions of `C_n`, `K_n`, `π_θ`,
Lebesgue projection length, `Fav`, the admissible exponents, and `α_Fav` as a real supremum:

| Declaration | Statement |
|---|---|
| `Favard.favard_le_rpow_beyond_quarter` | there is `C > 0` with `Fav(K_n) ≤ C n^{-156307/625000}` for all `n ≥ 1` |
| `Favard.beyond_quarter_le_decayExponent` | `156307/625000 ≤ α_Fav` |
| `Favard.favard_le_rpow_of_lt_quarter` | for every `a ∈ [0, 1/4)` there is `C > 0` with `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1` |
| `Favard.one_quarter_le_decayExponent` | `1/4 ≤ α_Fav` |
| `Favard.le_one_of_mem_admissibleExponents` | every admissible exponent is at most `1` |
| `Favard.decayExponent_le_one` | `α_Fav ≤ 1` |

The first two are the headline results; the next two record the intermediate quarter bound.
The last two restate the known bound `α_Fav ≤ 1`, via a proved `Fav(K_n) ≥ 1/(320 n)`. They also
show that the admissible set is bounded above, so `α_Fav` is a genuine least upper bound.

All six theorems are proved in [`Solution.lean`](Solution.lean) and depend only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. The repository contains no `sorry` outside the
Challenge's deliberate statement holes. The toolchain's `lake comparator` (Lean v4.35.0-rc2)
accepts the Solution, checked with Lean's kernel and the bundled independent NanoDa and con-ron
kernels. The repository's own CI also runs `lake comparator --paranoid`, which adds
leanchecker-paranoid, lean4lean and con-leche.

## The quarter bound

The argument follows the Nazarov–Peres–Volberg framework, with Marshall's sharp combinatorics
(Marshall v2, §7) in an endpoint form. It adds a new analytic step: a joint negative moment of
the whole low-frequency product. The overall structure:

1. **Combinatorial dichotomy** (G1–G17). Fix a direction and a multiplicity threshold `K`.
   Either the depth-`N` multiplicity function has superlevel set `{F_N ≥ K}` of measure at most
   `c₀ K^{-2}`, in which case its energy is `O(K)`, or the projection at depth `N·J` with
   `J ≳ K log K` has length `O(1/K)`.
2. **Joint negative moment** (J1). For fixed `s ∈ [1/4, 1/2)`,
   `∫_0^1 ∫_{c/L}^1 |P₁|^{-s} |P₂|² dy dt ≲_s L^{3s/2}/M`. Here `P₁` and `P₂` are the low- and
   high-frequency cosine products. The proof uses a telescoping identity, a change of variables
   to `(u, v) = (y(1+t), y(1−t))`, Riesz-product mass bounds on short intervals, sine-cell
   inverse moments, low-frequency cell majorants, and a finite Hilbert-matrix inequality.
3. **Exceptional directions** (J9). The set of directions whose energies up to depth `N` all
   stay below `H` has measure `≲_s (H³ log H / N)^{s/2}`. This combines a frequency window of
   small energy with an annular lower bound for the high-frequency mass (a Fejér-kernel
   argument) and the joint moment.
4. **Decay** (J10–J11). Layer-cake integration over thresholds gives
   `Fav(K_P) ≲_s P^{-1/4} + P^{-s/2}(2 + log P)^s`. Taking `s` close to `1/2` gives every
   exponent below `1/4`.
5. **Upper bound on the exponent** (L1–L2). Cauchy–Schwarz and pair counting give
   `Fav(K_n) ≥ 1/(320 n)`.

[`docs/proof-account.md`](docs/proof-account.md) is an informal account of the Lean proof that
is actually present. It lists the constants proved and where the Lean route departs from the
manuscript. [`PLAN.md`](PLAN.md) describes the architecture: each part proves a `Prop`
contract in [`FavardLength/Statements.lean`](FavardLength/Statements.lean), and
[`FavardLength/Main.lean`](FavardLength/Main.lean) plugs the parts together.

## Beyond the quarter

The strict improvement follows a September 2026 note, *Beyond the quarter exponent*. Its
mechanism differs from optimizing the negative moment alone:

1. **Improved baseline** (`Beyond/CellPowerSum*`, `Beyond/JointMoment.lean`,
   `Beyond/Exceptional.lean`). A transfer operator on the 4-adic grid of cell centres, with the
   exact evaluation `‖L_{1/2} 1‖_∞ = √(4+2√2)/4`, gives `∑_i sup_{I_i} D_m^{2s} ≲ L^{1-β}` with
   `β = 0.3071 > 1/4`. This improves the joint moment to `L^{2s-β}/M` and the exceptional-direction
   estimate to `(H^{4-2β/s} log H / N)^{s/2}`.
2. **Smooth-window exclusion** (`Beyond/Exclusion/`). Martingale selection finds a flat block
   of tail copies. A positive-weight Riesz-kernel argument finds a noncancelling harmonic, and a
   Taylor expansion of a smooth window with relative derivative bounds (Cauchy estimates on the
   entire transform) gives a contradiction. Together they exclude a neighbourhood of radius
   `≍ H⁻⁴B^{-1-2ε}` around every odd/odd slope `p/q`, `q ≤ B`, outside a set of
   `≲ H⁴B^{2d+6γ+2ε}` pairs counted by an exact sixth moment, `d = log₄(5/4)`.
3. **Redundant rational coverage** (`Beyond/Coverage/`). Outside a set of measure `≲ 1/M`,
   every slope lies within `r` of `≳ M = rB²` reduced odd/odd fractions, so the counted
   exceptions cannot cover it (geometry of numbers in a planar lattice).
4. **Assembly** (`Beyond/NewExceptional.lean`, `Beyond/Assembly/`). This gives a new
   exceptional-energy bound `≲ H⁴B^{-(1-2ε)}` at moderate thresholds, while the improved
   baseline covers large ones. A two-tail layer cake with the parameters `γ = 13/125`,
   `ε = 10⁻⁵`, `z = 1/625` yields the exponent `156307/625000`, with exact rational margins.

[`docs/proof-account-beyond.md`](docs/proof-account-beyond.md) describes this part of the Lean
proof, and [`PLAN-BEYOND.md`](PLAN-BEYOND.md) its architecture.

## Provenance and production

The mathematical arguments are two September 2026 manuscripts: *An optimized negative-moment
argument for the four-corner Favard exponent* (the quarter bound) and *Beyond the quarter
exponent* (the strict improvement). Yongxi Lin produced them in a ChatGPT project together with
internal reviews and a formalization plan. It has not been published or externally refereed,
and it is not included in this repository. Lean now checks the argument for the stated theorems.

The Lean development was written by Claude Code agents directed by Yongxi Lin: the quarter bound
on 2026-09-23 and the strict improvement on 2026-09-26/27.
An orchestrating session froze the Challenge, the shared definitions and the part contracts.
It then dispatched parallel agents, one per part, and assembled and audited the result.
`formalization.yaml` records the measured effort and the review performed.

## Repository map

- `Challenge.lean`: the statement surface, with literal definitions.
- `Solution.lean`: restates and proves the four Challenge theorems.
- `FavardLength/`: the proof development (about 16,500 lines):
  - `BasicProof/` and `Basic.lean`: basic facts about the approximants;
  - `Combinatorics/`: the G1–G17 dichotomy;
  - `Moment/`: the joint moment J1;
  - `Fourier/`: P1–P3, J9, and the transfer to angles;
  - `LowerBound/`: L1–L2;
  - `Decay*.lean` and `Exponent.lean`: J10–J11 and the exponent bounds;
  - `Beyond/`: the strict improvement beyond `1/4`.
- `comparator.json`: the declarations Comparator must match.
- `formalization.yaml`: Palomar metadata.

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The Comparator script runs the toolchain's `lake comparator` under bubblewrap, which needs
Linux; CI runs it on every push. Submissions to Palomar go through
https://submit.palomar-registry.org/.

## Licence

Apache-2.0; see [`LICENSE`](LICENSE).
