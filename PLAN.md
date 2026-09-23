# Formalization plan

Target: the three statements of `Challenge.lean`:

* `Favard.favard_le_rpow_of_lt_quarter`: for every `a ∈ [0, 1/4)` there is `C > 0` with
  `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`;
* `Favard.one_quarter_le_decayExponent`: `1/4 ≤ α_Fav`;
* `Favard.decayExponent_le_one`: `α_Fav ≤ 1`.

Mathematical source: `references/favard-optimized-quarter-proof.md` (SHA-256
`a90fbdcc0cbe9f0e412b0db9430013d2667b3688ce4c531b14837f46c744145c`), following
`references/favard-quarter-autoformalization-plan.md`. Equation labels G1–G17, P1–P4, J1–J12,
L1–L2 refer to the manuscript. The `references/` directory is local and untracked.

## Architecture

The development is split into parts whose contracts are `Prop`s in the frozen file
`FavardLength/Statements.lean`. Each part proves its contract, possibly assuming the contracts of
the parts it uses, in its own directory. `FavardLength/Main.lean` plugs the parts together, and
`Solution.lean` re-exports the three Challenge theorems.

Frozen files (never edit without the orchestrator): `Challenge.lean`, `FavardLength/Defs.lean`,
`FavardLength/Squares.lean`, `FavardLength/Fourier/Defs.lean`, `FavardLength/Statements.lean`.
`FavardLength/Basic.lean` has frozen statements; its proofs are filled in by the Basic part.

```
Defs (= Challenge definitions) ── Squares ── Basic ─┬─ LowerBound ───────────────────────┐
                                                    ├─ Combinatorics ⇒ DichotomyStatement │
Fourier/Defs ─ Statements ──────────────────────────┤                                    ├─ Main ─ Solution
   Hilbert, SineCell, LowCell ⇒ JointMoment ────────┤                                    │
   Window, Annular, JointMoment ⇒ NormalizedExcept. ┤                                    │
   Triangle identity ⇒ Bridge; Bridge + NormExc ⇒ ExceptionalAngle ────────────────────┤
   Dichotomy + ExceptionalAngle + Basic ⇒ Decay (J10–J11) ⇒ Exponent ──────────────────┘
```

| Part | Directory / files | Proves | May assume |
|---|---|---|---|
| Basic | `FavardLength/BasicProof/` | every lemma of `Basic.lean`, as `Favard.BasicProof.<name>` with the identical statement; the orchestrator then wires `Basic.lean` to them | — |
| LowerBound | `FavardLength/LowerBound/` | `LowerBoundStatement` | Basic |
| Combinatorics | `FavardLength/Combinatorics/` | `DichotomyStatement` | Basic |
| Hilbert | `FavardLength/Moment/Hilbert.lean` | `HilbertStatement` | — |
| MeanOne | `FavardLength/Moment/MeanOne.lean` | `MeanOneStatement` | — |
| SineCell | `FavardLength/Moment/SineCell.lean` (+ `Moment/SineCell/`) | `MeanOneStatement → SineCellStatement` | MeanOne |
| LowCell | `FavardLength/Moment/LowCell.lean` (+ `Moment/LowCell/`) | `MeanOneStatement → LowCellStatement` | MeanOne |
| JointMoment | `FavardLength/Moment/JointMoment.lean` | `SineCellStatement → LowCellStatement → HilbertStatement → JointMomentStatement` | the three |
| Window | `FavardLength/Fourier/Window.lean` | `WindowStatement` | — |
| Annular | `FavardLength/Fourier/Annular.lean` | `AnnularStatement` | — |
| Exceptional | `FavardLength/Fourier/Exceptional.lean` | `WindowStatement → AnnularStatement → JointMomentStatement → NormalizedExceptionalStatement` | the three |
| Triangle | `FavardLength/Fourier/Triangle.lean` | `TriangleStatement` | — |
| Bridge | `FavardLength/Fourier/Bridge.lean`, `Fourier/Angle.lean` | `TriangleStatement → BridgeStatement`; `NormalizedExceptionalStatement → BridgeStatement → ExceptionalAngleStatement` | Basic |
| Decay | `FavardLength/Decay.lean` | `DichotomyStatement → ExceptionalAngleStatement → ∀ a ∈ [0,1/4), ∃ C > 0, …` | Basic |
| Exponent | `FavardLength/Exponent.lean` | decay family + `LowerBoundStatement` ⇒ `1/4 ≤ α_Fav ≤ 1` | Basic |

## Mathematical notes for the parts

### Normalizations
* Geometric: for `θ ∈ [0, π/2]`, `σ = cos θ + sin θ ∈ [1, √2]`; the depth-`n` square with code
  `w` projects to `[proj θ (corner w), proj θ (corner w) + σ 4^{-n}]`.
* Normalized (manuscript "Fourier preparations"): `t = tan(π/4 − θ) = (cos θ − sin θ)/σ ∈ [0,1]`
  for `θ ∈ [0, π/4]`; `dt/dθ = −(1+t²)`, so `θ = π/4 − arctan t` and the inverse map is
  1-Lipschitz (use `LipschitzWith.hausdorffMeasure_image_le` or a direct argument).
  `normEnergy r t = (2π)⁻¹ ∫ sinc((4/3) 4^{-r} ξ)² ν̂_{r,t}(ξ)² dξ` is `‖f_{r,t}‖₂²` in Plancherel
  form. Bridge: `normEnergy r t = 3/(8σ) · energy r θ` (P1), proved through the triangle identity
  `(ℓ − |x|)_+ = (2π)⁻¹ ∫ (2 sin(ℓξ/2)/ξ)² cos(ξx) dξ` (Mathlib Fourier inversion,
  `MeasureTheory.Integrable.fourierInv_fourier_eq`, with the explicit Fourier transform of the
  triangle function), the overlap formula `energy_eq_sum_overlap`, and the product expansion
  `|∑_w e^{iξ p_w}|² = 16^r ∏_{j} …`.
* `lowProd m t y = P₁`, `highProd m n t y = P₂ = ν̂_{n−m,t}(4^n y)`, `L = 4^m`, `M = 4^{n−m}`.

### J1 (joint moment) — proof route
* Substitution `u = y(1+t)`, `v = y(1−t)`, `dy dt = du dv/(u+v)`; factor it as `z = yt`
  (a 1-D scaling for fixed `y`) followed by the linear map `(y,z) ↦ (y+z, y−z)`. Work with
  `lintegral` throughout.
* Telescoping: `sin(Lw) = 2L sin(w/2) D(w) ∏_{k=0}^{m} cos(4^k w/2)` from
  `sin(2^j x) = 2^j sin x ∏_{i<j} cos(2^i x)` with `j = 2m+1`, `x = w/2`. In `ℝ≥0∞`,
  `|A_m(w)|^{-s} ≤ (2L)^s |D(w)|^s |sin(Lw)|^{-s}` everywhere (both sides `⊤` at zeros).
* `|P₂|² = M⁻¹ R(u) R(v)` from `cos²(x/2) = (1 + cos x)/2`.
* Cells `I_i = [iπ/L, (i+1)π/L]`; on `(I_i × I_j) ∩ Ω`, `1/(u+v) ≤ C/(h(i+j+1))`, using
  `u ≥ 3/(8L)` in the `(0,0)` cell. Then SineCell twice, LowCell, Hilbert, and
  `∑_{i<L} a_i^s ≤ L^{1−s}(∑ a_i)^s`.

### SineCell (P4, J2–J3)
* Mean-one lemma without Fourier series: for `g` with period `T/4`,
  `∫_0^T cos(2π x/T) g = 0` because `∑_{q=0}^{3} cos(x + qπ/2) = 0`; by induction
  `∫_0^{2π/(β 4^a)} ∏_{k∈S} (1 + cos(β 4^k w)) dw = 2π/(β 4^a)` for finite `S ⊆ [a, ∞)`.
* P4 by the manuscript's case split on `4^{-j-1} < δ ≤ 4^{-j}`; J3 by the layer-cake identity
  `|sin|^{-s} = 1 + s ∫_{|sin|}^{1} δ^{-s-1} dδ` (or a dyadic decomposition of `{|sin(Lw)| ≤ δ}`).

### LowCell (J4–J5)
* `∫_0^π D² = π 2^{-m}` by the mean-one lemma (frequencies `2·4^k`).
* No Parseval is needed: `|D'| ≤ ∑_k 4^k |∏_{j≠k} cos(4^j w)|`, Cauchy–Schwarz, and the mean-one
  lemma for the lacunary product with one factor removed give `∫_0^π D'² ≤ C L² ∫_0^π D²`-type
  bounds of order `L^{3/2}`.
* `b_i = (2/h)∫_{I_i} D² + 2h ∫_{I_i} D'²` dominates `D²` on `I_i` (FTC + Cauchy–Schwarz).

### Exceptional (J9) — integrated form (no Markov selection needed)
For `t ∈ E`: `∫_{c/L}^1 P₂² ≥ c_a/M` (Annular); `∫_{|P₁|<a} P₂² ≤ a^s ∫ |P₁|^{-s} P₂²`;
`4^n ∫ (P₁P₂)² ≥ 4^n a² (c_a/M − a^s I(t))`. Integrate over `E`, use Window and JointMoment, and
choose `a^s = c_a e /(2 A L^{3s/2})`, `L = 4^m` minimal with `A₀ H ≤ L`. Small `N`
(`N < 4(m+3)`) and the case where the bound exceeds one are handled by the constant. `E` is
measurable because `t ↦ normEnergy r t` is continuous (dominated convergence; `|ν̂| ≤ 1` and
`sinc²` is integrable).

### Decay (J10–J11) with a fixed moment parameter
Given `a < 1/4`, take `s = (max(1/4, 2a) + 1/2)/2`. For `P` large and `P^{-1/4} ≤ t ≤ √2`, set
`K = B/t`, `J = ⌈c K log K⌉`, `N = ⌊P/J⌋`; nesting gives `L_P ≤ L_{NJ}`; Dichotomy puts
`{θ ∈ [0, π/4] : L_P(θ) > t}` inside the low-energy set; ExceptionalAngle bounds its measure by
`C t^{-2s} P^{-s/2} (2 + log P)^s`. Layer cake (`lintegral_eq_lintegral_meas_lt`) and
`favardLength_eq_quarter` give `Fav(K_P) ≤ C(P^{-1/4} + P^{-s/2}(2+log P)^s)`; absorb the
logarithm into `P^{s/2 − a}` and the small depths into the constant.

### Hazards (from the plan)
1. Natural vs real powers; positive depths in negative powers.
2. `toReal` of an infinite measure; prove finiteness (`volume_proj_image_fourCorner_ne_top`).
3. Real `sSup` needs nonempty and bounded above.
4. The manuscript's phase has no `2π`; Mathlib's Fourier transform does. Prove one bridge.
5. Totalized `x⁻¹`, `0 ^ (-s)`: use `ℝ≥0∞` for reciprocal powers.
6. Nonintegrable Bochner integrals are `0`: prove integrability before monotonicity, or use
   `lintegral`.
7. Repeated projected centers must keep multiplicity: sum over codes, never over a set of points.

## Rules for every part
* Never edit frozen files. Never add `axiom`, `sorry` in finished work, `native_decide`,
  `admit`, or `implemented_by`. Never weaken a `Statements.lean` contract; if one is false or
  unusable, stop and report the smallest failing statement.
* Use targeted Mathlib imports, not `import Mathlib` (which takes about a minute to load here).
* Check a file with `lake env lean FavardLength/…/File.lean`. Build your own modules with
  `lake build FavardLength.Part.File`. Do not build or edit other parts' files.
* Keep files under about 1500 lines; split by topic.
