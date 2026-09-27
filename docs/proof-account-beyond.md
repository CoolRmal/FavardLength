# How the Lean proof of the beyond-quarter exponent goes

This is an informal account of the Lean proof of the two beyond-quarter theorems in
`Solution.lean`. The first is `favard_le_rpow_beyond_quarter`, `Fav(K_n) ≤ C n^{-156307/625000}`
for `n ≥ 1`, whose proof term is `Favard.beyond`. The second is
`beyond_quarter_le_decayExponent`, `156307/625000 ≤ α_Fav`, proved by
`beyond_quarter_le_decayExponent'` via `le_csSup`, with the bound `α ≤ 1` from `lowerBound`.
The account is written against commit `36fbea2` and covers what the Lean code proves, not the
source. The source is `references/beyond/favard-beyond-quarter-complete.md`, "the beyond note",
with SHA-256 `bd2183c6…b333`. It is not part of the public repository. Equation numbers `(k)`
refer to the note's main text; `G (12)` means equation (12) of Appendix G, and `B.3` means
Section 3 of Appendix B.

The quarter development is reused unchanged and is described in `docs/proof-account.md`.
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for both theorems.
`FavardLength/Beyond/` contains no `sorry`, `admit`, `axiom` or `native_decide`.

**Architecture.** `Beyond/Statements.lean` fixes the following contracts:

- `CellPowerSumStatement s β`
- `JointMomentImprovedStatement s β`
- `ExceptionalImprovedStatement s β`
- `ExclusionStatement γ ε`
- `CoverageStatement`
- `NewExceptionalStatement γ ε`

It also defines `d = sixthMomentDim = log₄(5/4)` and `μ = redundancyExp γ ε = 1 − 2d − 6γ − 4ε`.
`Exclusion/Statements.lean` splits the exclusion into six sub-contracts. Unfolded,
`Beyond/Main.lean` proves:

```
exceptionalImproved := exceptionalImproved_of window annular …
                         (jointMomentImproved_of (sineCell_of meanOne) hilbert … cellPowerSum)
exclusion γ₀ ε₀     := exclusion_of complementaryCount complementaryBound relDeriv harmonic
                         (flatBlock_of cellSelection) windowBound …
beyond              := beyond_of dichotomy (bridge_of triangle) exceptionalImproved
                         (newExceptional_of … (1349/25000 < μ) (exclusion γ₀ ε₀) coverage)
```

The parameters are `s₀ = 1/2 − 10⁻⁷`, `β₀ = 3071/10000`, `γ₀ = 13/125` and `ε₀ = 10⁻⁵`.

## 1. Cell-power sum (`CellPowerSum.lean`, `CellPowerSum/{Transfer,Certificate}.lean`)

`cellPowerSum : CellPowerSumStatement s₀ β₀`. For every `m` the contract asks for positive
majorants `b_i ≥ D_m(w)²` on the cells `I_i = [iπ/4^m, (i+1)π/4^m]`, `i < 4^m`, with
`Σ b_i^s ≤ C (4^m)^{1−β}`. The general form `CellPowerSum.cellPowerSum_of` gives this for
`1/4 ≤ s ≤ 1/2` whenever `261313/400000 + (1 − 2s) ≤ 4^{−β}`. The proof has five steps.

1. **Majorants.** Let `c_i = (i + 1/2)π/4^m` and `ε_k = (π/2)4^{k−m}`. Since `cos` is
   1-Lipschitz, `|cos(4^k w)| ≤ |cos(4^k c_i)| + ε_k` on `I_i`. So
   `b_i = ∏_{k<m}(|cos(4^k c_i)| + ε_k)²`.
2. **Powers.** Put `a = 2s`. Then `(x+y)^a ≤ x^a + y^a`, and `x^a ≤ x + (1−a)` by weighted AM–GM
   (`rpow_le_add_one_sub`). Hence `b_i^s ≤ ∏_k(|cos(4^k c_i)| + (1−2s) + ε_k^{2s})`.
3. **Transfer** (`sum_prod_le`). If `Σ_{j<4}|cos((x+jπ)/4)| ≤ 4r` on `[0,π]`, then
   `Σ_i ∏_k(|cos(4^k c_i)| + d_k) ≤ ∏_k 4(r + d_k)` for all `d_k ≥ 0`. The proof is by induction
   on `m`. For `i = j4^m + i'` one has `4c_i = c'_{i'} + jπ`, so by `π`-periodicity the factors
   with `k ≥ 1` depend only on `i'`, and the factor `k = 0` is summed over the four branches `j`.
   `sum_abs_cos_le` evaluates that sum exactly as `(1+√2)cos(x/4) + sin(x/4)` and bounds it by
   `261313/100000 ≥ √(4+2√2)`. This gives `r = 261313/400000`.
4. **Tails.** `∏(q + e_k) ≤ q^m exp(Σe_k/q)`, and `Σ_k ε_k^{2s} ≤ 2` because `ε_k ≤ 1` and
   `2s ≥ 1/2`. Here `q = r + 1 − 2s` and `C = exp(2/q)`.
5. **Certificate.** At `s₀`, `q = 0.6532827 ≤ 653285/10⁶ ≤ 4^{−β₀}` (`certificate`). This follows
   from `653285^10000 · 4^3071 ≤ 10^60000` (`certificate_nat`), which the kernel checks by `decide`.

*Divergences from B.1 and B.10:*
- There is no integral transfer identity B.1 (5) and no subharmonic sampling inequality (6), so
  no complex analysis is needed. The operator acts on the finite 4-adic grid of cell centres, and
  majorants at the centres replace the cell suprema `a_i`.
- The perturbation bound is `x^a ≤ x + (1−a)`, not the `(1−a)/(ae)` of B.10 (31). The transfer
  constant is therefore `ρ_* + (1 − 2s)`, with `ρ_*` replaced by `261313/400000`.
- The note certifies `β_* > 307/1000` via `239^500·2^614 < 560^500` and then picks some `β` near
  `307/1000`. Lean instead fixes `β₀ = 3071/10000` and uses the certificate above.

## 2. Improved joint moment and exceptional directions (`JointMoment.lean`, `Exceptional.lean`)

`jointMomentImproved_of` (for `1/4 ≤ s < 1/2`) proves
`∫∫|P₁|^{−s}|P₂|² ≤ A(4^m)^{2s−β}/4^{n−m}`. It repeats the quarter J1 proof: the change of
variables, the cellwise bound, the sine-cell integrals and the Hilbert inequality. The only change
is that the concavity bound `Σβ_i^s ≤ L^{1−s}(Σβ_i)^s` becomes the cell-power sum,
`(2L)^{2s}L^{−1}Σb_i^s ≤ C4^s L^{2s−β}`. The quarter `LowCellStatement` is not used; the
hypotheses `0 < β ≤ s` are unused.

`exceptionalImproved_of` (for `0 < β < 3s/2`) repeats J9. It takes `κ = 4 − 2β/s > 1` and
`L = 4^m ∈ [A₀H, max(1, 4A₀H)]`. From the window (P2), the annular bound (P3) and the joint moment
it proves `|E(H,N)| ≤ C(H^{4−2β/s}(2+log H)/N)^{s/2}` for `H ≥ 2`, `N ≥ 1`, where `E(H,N)` is the
set of slopes with energy at most `H` at every generation `1…N`. Depths `N < 4(m+3)` are
trivial.

*Divergence:* the endpoint weak estimate B.3–B.4, which gives `N^{−1/4}`, is not formalized.
Lean uses the strong moment at the fixed `s₀`, so the power of `N` is
`s₀/2 = 1/4 − 5·10⁻⁸`. The final margin pays for this. There is no `(1−2s)^{−2}` bookkeeping,
since the constants depend on `s`.

## 3. Smooth-window exclusion (`Exclusion/`)

`exclusion_of` proves `ExclusionStatement γ ε` for all `0 < γ < 2` and `0 < ε < 1/2` from the six
sub-contracts.

**Shared analysis** (`Defs`, `Density`, `Transform`, `Analytic`, `Cutoff`). The tail density
is `tailDensity n t = ρ⁻¹Σ_w 1[|x − c_w(t)| ≤ ρ4^{−n}/2]` with `ρ = 8/3`. It has mass one, support
in `[−4/3, 4/3]`, `∫f² = normEnergy n t` (by the overlap formula and the quarter triangle
identity), and a self-similar splitting (`tailDensity_rescale`).

`tailFTC_eq` gives the product formula `Ψ(z) = A_n(4(1−t)z)A_n(4(1+t)z)b_n(z)` for the entire
extension, and `Analytic` proves `Ψ^{(j)}(ξ) = (−2πi)^j M_j(ξ)`. The cutoff is
`χ(x) = s(8x−2)s(6−8x)` (Mathlib's `smoothTransition`), with a uniform Taylor remainder and
`|χ̂(w)| ≤ C_J|w|^{−J}` from Mathlib's Fourier transform of derivatives.

**(a) Complementary products** (`Complementary*.lean`). `exceptionalSet B γ K` consists of the
odd `p, q ≤ B` for which some odd `h ≤ K` has `|A(ph/2)A(qh/2)| > B^{−γ}`, with
`|A| = inf_n |A_n|`.
- `sum_cosProd_pow_six` proves the exact sixth moment `Σ_{i<4^m}A_m((2i+1)h/2)^6 = (5/4)^m` for
  odd `h`. The proof is by induction on the depth: split off the finest factor and use
  `Σ_{s<4}cos⁶(θ + πsh/4) = 5/4`. The note uses a Fourier-digit/aliasing argument instead.
  Consequently `Σ_{p odd ≤ B}|A(ph/2)|^6 ≤ (5/4)B^d`.
- `complementaryCount` bounds `#X ≤ (5/4)²K B^{2d+6γ}` by Markov's inequality and a union bound
  over `h`.
- `complementaryBound` shows that outside `X`, `|A_n(pk)A_n(qk)| ≥ 4B^{γ−2}/(π²k²)` for
  `k = 4^v h`. It uses the finite identity `A_n(x)A_n(x/2)·4^n sin(πx/(2·4^n)) = sin(πx/2)` with
  `|sin y| ≤ |y|` and a limit, instead of the exact infinite identity (11).
- *Divergence:* only odd/odd pairs appear. The note's even-valuation pairs `p = 4^u a_p` are not
  needed, so there is no factor for removing powers of four.

**(b) Relative derivatives** (`RelDeriv*.lean`). `relDeriv` holds with `c₀ = 1/4`,
`c₁ = e^{−5}/2` and `C_j = 2e^{171}j!/(2π)^j`. Take odd `p, q` and `k` of even two-adic valuation,
and put `ξ = Qk/8` and `L = log(2+Qk)`. If `4|t−t₀|ξL ≤ 1/4` and `ρ4^{−n}ξ ≤ 1/4`, then
`|ψ(ξ)| ≥ c₁|A_n(pk)A_n(qk)|` and `‖M_j(ξ)‖ ≤ C_j L^j|ψ(ξ)|`.

The ingredients are the tangent sum `tanSum ≤ 10 log(2+x₀)` (G (4)), the complex ratio bound
`norm_cosProdC_add_le`, and Cauchy's estimate on the circle of radius `1/L`, where
`|Ψ| ≤ 2e^{171}|ψ|`. The lower bound is relative to the product at the rational point, not the
absolute `c/(Q²k²)` of G (7); part (a) supplies the product bound afterwards.

**(c) Harmonic** (`Harmonic.lean`). `harmonic` shows: for nonnegative weights with `W₂ > 0`
there is `k = 4^v h` with `h` odd, `k < 6m²` and `|Σw_i e^{ikθ_i}|² ≥ W₂/4`. The proof uses the
kernel `∏_{r<d}(1 + cos 4^r x)`, whose coefficients are `2^{−|e|}` on the digit vectors
`e ∈ {0,±1}^d`.

*Divergence:* `d` is chosen from the copy count, `2m ≤ 2^d ≤ 4m`, rather than from the effective
count `W₁²/W₂`. The zero mode is bounded by `(ΣW)² ≤ mW₂`.

**(d) Flat block** (`CellSelection.lean`, `FlatBlock.lean`). `cellSelection` (d1) finds, for
`N ≥ 16L`, a level-`j` cell with `2j ≤ N`, mean `0 < a ≤ 12H` and relative block variance at most
`64ρHL/N`; the proof actually gives `32HL/N`. It works with finite sums of cell masses and needs
no conditional-expectation API:
- the level energies satisfy `E_j ≤ ∫f²`;
- Pythagoras gives `E_{j+L} − E_j = ΣV_i`;
- the blocks `[kL, (k+1)L]` with `k ≤ ⌊N/(2L)⌋` telescope, so one block has increment at most
  `2HL/N`;
- the good cells, those with `3/32 ≤ a_i ≤ 12H`, carry mass at least `2/3` and coarse energy at
  least `1/16`.

*Divergences:* there is no neighbour condition D (2), because `a_i ≤ 12H` follows directly from
Markov's inequality. There is no copy count D (4) and no lower bound `j ≥ N/4`.

`flatBlock_of` (d2) applies the selection with block length `r + L` and rescales at level `j + r`.
It keeps the copies with `β_u ∈ [ρ/2, T − ρ/2]`, where `T = ρ4^r`. The result is:
- `g = F` on `[T/4, 3T/4]`;
- `m ≤ aT` copies;
- a tail depth `n` with `N ≤ 2(n + r)`;
- flatness at resolution `T/4^{r+L}` with `e = η² = (512/3)H(r+L)/N`.

*Divergences:* flatness holds only on the middle half, which is where the window lives, rather
than on `[ρ, T−ρ]`. The lost-mass bound E (3), the count `R/8 ≤ m` and E (5)–(7) are not
formalized.

**(e) Window bounds** (`Window*.lean`). `windowBound` holds for every `J`, assuming `e ≤ 1`,
`T ≥ 64/3`, `L ≥ 2` and `ξ ≥ 1/4`.
- `plateau_count` gives `αT(1/8 − √e) ≤ Σχ(β_i/T)²` by counting the copies in `[7T/16, 9T/16]`;
  G (12) has `1/8 − η/√8`.
- `‖expandedWindow J‖ ≤ Cm/T^{J+1} + CαT(√e + (T/4^L)ξ + (Tξ)^{−J})`. This combines two bounds.
  The first is the order-`J` Taylor expansion, copy by copy, with a Lagrange remainder. The second
  is the flat-block bound, obtained by averaging over cells against the Lipschitz modulated cutoff,
  together with the decay of `χ̂`.

**Parameters and contradiction** (`Parameters.lean`, `Main.lean`). `exclusion_of` picks the Taylor
order `J = ⌈(2−γ)/ε⌉₊ + 10`, so `J ≥ 10` and `ε(J−5) ≥ 2−γ`. It then fixes constants in this
order:
- `C_E(J)`, `C_χ(J)` and `Csum = Σ_{j<J}C_{j+1}`;
- `cψ = c₁/(9π²)`, `δ₁ = cψ/(1088C_E)` and `δ₅ = 1/(64(Csum·C_χ + 1))`;
- `κ = max(2, 12⁵4^J/δ₁, 12·200018²/δ₅²)` and `Λ = max(1, 4(128κ⁴)⁷/δ₁)`;
- the depth constant `CN`, and `crad = c₀/(6·128²·200018κ⁹)`.

Given `H` and `B`, let `ℓ = log(2+HB)` and `x₀ = κ⁴HB^εℓ²`. Then `4^r ∈ (x₀, 4x₀]`,
`4^L > Λ(2+HB)^{38}`, and `K = ⌈6(128κ⁴)²H⁴B^{2ε}ℓ⁴⌉`. The omitted set is `X_{B,γ,K}`, of size
at most `(5/4)²(6·128²κ⁸+1)H⁴B^{2d+6γ+2ε}ℓ⁴`.

`exclusion_pointwise` assumes `normEnergy N t ≤ H` and derives a contradiction:
- (d) gives the copies, and the depth condition gives `e ≤ 1/256`;
- (e) gives `W ≥ αT/16 ≥ m/16` and `m ≤ 12HT`;
- (c) gives `k < 6m² ≤ K` and `|S₀| ≥ √m/8`;
- (a) and (b) give `ψ ≥ cψ/(m⁴B^{2−γ})` and `log(2+Qk) ≤ 200018κℓ`;
- `window_chain` bounds `ψ|S₀|` by `17C_E m 4^J/T^J` (Taylor remainder and constant mode
  together, since `ξ ≥ 1/4`) plus `16C_E m(√e + hξ)` plus the relative-derivative corrections;
- `taylor_small`, `flat_small`, `avg_small` and `corr_small` bound each of the four errors by
  `ψ√m/64`, and `window_contra` gives `False`.

*Divergences:*
- The note fixes `J = 189605` with `J ≥ 9` and `ε(J − 9/2) > 2−γ`. Lean chooses `J` inside
  `exclusion_of` for each `(γ, ε)`, giving `J = 189610` at `(γ₀, ε₀)`. The `J − 5` comes from
  bounding `√m ≤ m` in the Taylor ratio.
- Every constant depends on `J`.
- The resolution is `Λ(2+HB)^{38}`, not `DB^{3−γ}(32HR)^{13/2}`.
- The note compares a lower bound for `I(ξ)` (`3𝓜/4`) with an upper bound (`3𝓜/8`). Lean
  instead bounds the Taylor polynomial and isolates its `j = 0` term, and each error is at most
  `1/64` of the main term rather than `1/8`.
- Coprimality of `(p, q)` is not used.

## 4. Coverage (`Coverage/`)

`coverage : CoverageStatement` holds with `A = 64(L₀+2)`, `R₀ = A`, `M₀ = 1`, `C = 4A²` and
`c = 1/16384`, where `L₀ = ⌈72·98 + 8⌉₊ = 7064`.
- **Reduced basis** (`Lattice.lean`, `exists_reduced_basis`). A shortest vector is primitive.
  Bezout completion and Gauss reduction give `Q(w₁) ≤ Q(w₂)` and `Q(w₁)Q(w₂) ≤ 4D²/3` via the
  Lagrange identity.
- **Short vectors** (`Exception.lean`). A vector shorter than `A/M` puts `x` within `A/(qR)` of
  some `p/q` with `q ≤ A/(rR)`. These intervals have total measure at most `4A²/(rR²)`.
- **Counting** (`count_ge`). The lattice `(q/R, (p−xq)/(rR))` has determinant `1/M`. The
  coefficient rectangle `|m−m₀| ≤ η/s₁`, `|n−n₀| ≤ η/s₂` with `η = 1/32` maps into the sup-norm
  ball of radius `1/16` about `(3/4, 0)`. Its points give `11R/16 ≤ q ≤ 13R/16`, `0 ≤ p ≤ q` and
  `|x − p/q| ≤ r/11`. By unimodularity, odd/odd `(q, p)` is a parity class of `(m, n)`. It
  contains at least `L₁L₂/2 ≥ M/16384` coprime pairs.
- **Primitive points** (`card_coprime_parity_ge`). An `L₁ × L₂` box with `L₀ ≤ L₂ ≤ L₁` and
  `|n| ≤ 98L₂` contains at least `L₁L₂/2` coprime pairs of any nonzero parity class.

*Divergences:* Lean replaces Möbius inversion (error `O(U log V)`) by a union bound. It sums over
the odd common divisors `3 ≤ d ≤ 98L₂` plus the zero row, using `Σ_{d≥3 odd} d^{−2} ≤ 1/4` and
Cauchy–Schwarz for `Σ 1/d`. The hypothesis `M ≥ M₀` is unused.

## 5. New exceptional estimate (`NewExceptional.lean`)

`newExceptional_of` requires `μ > 0`. It applies coverage with `R = B` and
`r = c'H⁻⁴B^{−1−2ε}ℓ⁻⁵`, where `c' = min(c_X, 1)/2`, so `M = c'B^{1−2ε}/(H⁴ℓ⁵)`. Split
`1 − 2ε = μ + (2d + 6γ + 2ε)`. The redundancy condition `CH⁸ℓ⁹ ≤ B^μ` then gives `B ≥ R₀`,
`M ≥ M₀` and `c_V·M > #X`. Hence every covered slope has a nearby pair outside `X`.

`slopeMap x = (1−x)/(1+x)` is an involution, is 2-Lipschitz on `[0, ∞)`, and sends `p/q` to
`(q−p)/(q+p)`. The low-energy set therefore lies in `φ(U ∩ [0,1])`, whose measure is at most
`2|U|` (Hausdorff measure of a Lipschitz image). This gives `CH⁴ℓ⁵/B^{1−2ε}`. Only the upper
Lipschitz bound is used, and the energy is the terminal one at depth `N`.

## 6. Assembly (`Assembly/`)

- **Certificate** (`Certificate.lean`). `5^1000 < 4^1161` (`decide +kernel`) gives
  `d < 161/1000`, hence `μ(γ₀, ε₀) > 1349/25000`.
- **Geometry** (`volume_projLength_gt_le_slope`). For a threshold `u`, put `K = B/u` and
  `J = ⌈cK log K⌉ ≤ (c/κ+1)K^{1+κ}` (using `log K ≤ K^κ/κ`), and `N = ⌊P/J⌋`, so
  `P ≤ 2(c/κ+1)K^{1+κ}N`. The quarter dichotomy, nesting, the bridge and the angle transfer then
  put `{λ_P > u}` inside the slope set of energy at most `AK` at every `r ≤ N`.
- **Tails** (`Tails.lean`). The old tail is `CP^{−s/2}K^{σ₁}` with
  `σ₁ = (5 − 2β/s + 2κ)s/2`, using `2 + log H ≤ (2+1/κ)H^κ`. The new tail uses
  `R = P^{(1−η)/D}K^{−20/D}` and `ℓ ≤ ((2+A)^τ/τ)P^τ` to give `CP^{5τ−(1−η)δ}K^{4+20δ}`, with
  `δ = c₁/D`. It holds for `2 ≤ K ≤ P^z` once
  `P^{(1−η−20z)/D} ≥ 2` and two constants lie below `P^{(1−η)μ/D − z(8+20μ/D) − 9τ}` and
  `P^{η−19τ−zκ}`.
- **Superlevel sets** (`Superlevel.lean`). The estimates apply for `u ≥ P^{−1/3}`, which makes
  the block fit: `(c/κ+1)B^{3/2} ≤ √P`.
- **Layer cake** (`intervalIntegral_le_of_two_tails`).
  `∫₀^b f ≤ bT₀ + M₁T₁^{1−σ₁}/(1−σ₁) + M₂T₁^{1−σ₂}/(σ₂−1)` with `T₀ = P^{−1/3}` and
  `T₁ = BP^{−z}`.
- **Final bound** (`favardLength_le_of_params`, `beyond_of`). With `κ = 1/20000`, `z = 1/625`,
  `η = 10⁻⁴` and `τ = 10⁻⁶`:
  `Fav(K_P) ≲ P^{−1/3} + P^{−s/2−z(1−σ₁)} + P^{5τ−(1−η)δ+z(σ₂−1)}`. Here
  `D = 379209/100000`, `δ = 99998/379209`, `σ₁ ≈ 0.94292` and `σ₂ ≈ 9.274`. Small `n` are
  covered by `Fav ≤ √2`.

The exponent margins against `a = 156307/625000` are:
- the old exponent exceeds `a` by `8800001/125·10¹² ≈ 7.04·10⁻⁸`;
- the new exponent exceeds `a` by `645655471/1896045000000 ≈ 3.41·10⁻⁴`;
- `a ≤ 1/3`.

The auxiliary exponents are also positive: `(1−η−20z)/D ≈ 0.255`,
`(1−η)μ/D − z(8+20μ/D) − 9τ > 9.6·10⁻⁴` (using `μ > 1349/25000`), and
`η − 19τ − zκ = 8.092·10⁻⁵`.

*Divergences:*
- There is no linear propagation (Appendix C and the depth `N ≍ P/H` of §5). Lean uses the
  old dichotomy with `J ≍ K log K`.
- Logarithms are absorbed into the small powers `κ, τ, η` inside the lemmas, whereas the note
  carries `(1+log P)^C` to the end. Lean's denominator scale `R` has no `(1+log P)^{C₀}` factor.
- The layer cake is taken in `u` directly rather than in `H` with a Jacobian. Levels below
  `P^{−1/3}` are bounded trivially, giving `P^{−1/3}` rather than `O(1/P)`, and there is no
  initial threshold `H₀`.
- The old exponent is `s₀/2 + z(1−σ₁)` rather than `1/4 + z(β − 1/4)`. The note's margins (29)
  and (30) are replaced by the margins above.

## Modules

Line counts are from `wc -l`. There are 7937 lines in total under `FavardLength/Beyond/`.

| Part | Files | Lines | Main declaration |
|---|---:|---:|---|
| Statements, Main | 2 | 180 | contracts; `beyond` |
| CellPowerSum (+Transfer, Certificate) | 3 | 395 | `cellPowerSum` |
| JointMoment | 1 | 142 | `jointMomentImproved_of` |
| Exceptional | 1 | 155 | `exceptionalImproved_of` |
| Exclusion/Defs, Statements | 2 | 245 | sub-contracts |
| Exclusion/Density, Transform, Analytic, Cutoff | 4 | 898 | `tailFTC_eq` |
| Exclusion/Complementary (+LowerBound, SixthMoment) | 3 | 459 | `complementaryCount`, `complementaryBound` |
| Exclusion/RelDeriv (+Tangent, Ratio) | 3 | 684 | `relDeriv` |
| Exclusion/Harmonic | 1 | 297 | `harmonic` |
| Exclusion/CellSelection | 1 | 383 | `cellSelection` |
| Exclusion/FlatBlock | 1 | 205 | `flatBlock_of` |
| Exclusion/Window (+Basic, Cells, Plateau, Taylor, Averaging) | 6 | 697 | `windowBound` |
| Exclusion/Parameters, Main | 2 | 985 | `exclusion_of` |
| Coverage (Primitive, Lattice, Exception, Main) | 4 | 1050 | `coverage` |
| NewExceptional | 1 | 241 | `newExceptional_of` |
| Assembly (Certificate, Geometry, Tails, Superlevel, LayerCake, Main) | 6 | 921 | `beyond_of` |
