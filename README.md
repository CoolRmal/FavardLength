# FavardLength

A Lean 4 + Mathlib proof that the Favard length of the four-corner Cantor set decays at least
like `n^{-1/4+ε}`: the decay exponent `α_Fav` is at least `1/4`.

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
| `Favard.favard_le_rpow_of_lt_quarter` | for every `a ∈ [0, 1/4)` there is `C > 0` with `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1` |
| `Favard.one_quarter_le_decayExponent` | `1/4 ≤ α_Fav` |
| `Favard.le_one_of_mem_admissibleExponents` | every admissible exponent is at most `1` |
| `Favard.decayExponent_le_one` | `α_Fav ≤ 1` |

The first two are the new results. The last two restate the known bound `α_Fav ≤ 1`, via a
proved `Fav(K_n) ≥ 1/(320 n)`. They also show that the admissible set is bounded above, so
`α_Fav` is a genuine least upper bound. Nothing here claims that `1/4` itself is admissible.

All four theorems are proved in [`Solution.lean`](Solution.lean) and depend only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. The repository contains no `sorry` outside the
Challenge's deliberate statement holes. Comparator, run through the pinned template script with
Landrun sandboxing and the independent NanoDa kernel, accepts the Solution.

## The proof

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

## Provenance and production

The mathematical argument is a September 2026 manuscript, *An optimized negative-moment argument
for the four-corner Favard exponent*. Yongxi Lin produced it in a ChatGPT project together with
internal reviews and a formalization plan. It has not been published or externally refereed,
and it is not included in this repository. Lean now checks the argument for the stated theorems.

The Lean development was written on 2026-09-23 by Claude Code agents, directed by Yongxi Lin.
An orchestrating session froze the Challenge, the shared definitions and the part contracts.
It then dispatched parallel agents, one per part, and assembled and audited the result.
`formalization.yaml` records the measured effort and the review performed.

## Repository map

- `Challenge.lean`: the statement surface, with literal definitions.
- `Solution.lean`: restates and proves the four Challenge theorems.
- `FavardLength/`: the proof development (about 8,500 lines):
  - `BasicProof/` and `Basic.lean`: basic facts about the approximants;
  - `Combinatorics/`: the G1–G17 dichotomy;
  - `Moment/`: the joint moment J1;
  - `Fourier/`: P1–P3, J9, and the transfer to angles;
  - `LowerBound/`: L1–L2;
  - `Decay*.lean` and `Exponent.lean`: J10–J11 and the exponent bounds.
- `comparator.json`: the declarations Comparator must match.
- `formalization.yaml`: Palomar metadata.

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The Comparator script needs Linux and Landrun; CI runs it on every push. Submissions to Palomar
go through https://submit.palomar-registry.org/.

## Licence

Apache-2.0; see [`LICENSE`](LICENSE).
