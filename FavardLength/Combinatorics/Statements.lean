import FavardLength.Combinatorics.Marking

/-!
# Sub-contracts of the combinatorial dichotomy

The proof of `Favard.DichotomyStatement` (manuscript section "The combinatorial dichotomy",
G1–G17) is split into three independently provable statements about a fixed direction
`θ ∈ [0, π/2]`, a real threshold `K ≥ 2` and a depth `N`, in terms of

* `maxCount N θ x = F_N(x) = max_{0 ≤ n ≤ N} f_n(x)` (root generation included),
* `superLevel N θ K = {x : F_N(x) ≥ K}`, whose measure is `μ_N(K)`,
* `retained N θ K`, the maximal marked squares `𝓡` of the packing construction.

1. `PackingStatement` (G6–G9): `∑_{R ∈ 𝓡} 4^{-|R|} ≤ C K μ_N(K)`.
2. `EnergyAbsorptionStatement` (G10–G12): if `μ_N(K) ≤ c₀ K⁻²` then `‖F_N‖₂² ≤ A K`. It is
   proved from 1 in `FavardLength/Combinatorics/Absorption.lean`
   (`Favard.Comb.energyAbsorption_of_packing`).
3. `PropagationStatement` (G13–G17): for every `c₀ > 0` there are `c, B` such that
   `μ_N(K) > c₀ K⁻²` and `J ≥ c K log K` imply `|π_θ(K_{NJ})| ≤ B/K`.

`Favard.dichotomy_of` (in `FavardLength/Combinatorics/Main.lean`) derives
`Favard.DichotomyStatement` from 2 and 3, and `Favard.dichotomy_of_packing` from 1 and 3. All
constants are absolute; they are existentially quantified, so any values produced by the proofs
are acceptable.
-/

open MeasureTheory Set Real

namespace Favard.Comb

/-- **Packing inequality (G7)**, manuscript (G6)–(G9): the side lengths `4^{-|R|}` of the retained
squares sum to at most `C K μ_N(K)`. -/
def PackingStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N : ℕ,
    ENNReal.ofReal (∑ R ∈ retained N θ K, 1 / 4 ^ R.length) ≤
      ENNReal.ofReal (C * K) * volume (superLevel N θ K)

/-- **Energy absorption**, manuscript (G10)–(G12) and the first alternative of the dichotomy: if
`μ_N(K) ≤ c₀ K⁻²` then `∫ F_N² ≤ A K`. -/
def EnergyAbsorptionStatement : Prop :=
  ∃ c₀ A : ℝ, 0 < c₀ ∧ 0 < A ∧ ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N : ℕ,
    volume (superLevel N θ K) ≤ ENNReal.ofReal (c₀ / K ^ 2) →
      ∫ x, (maxCount N θ x : ℝ) ^ 2 ≤ A * K

/-- **Terminal selection and propagation**, manuscript (G13)–(G17) and the second alternative of
the dichotomy: for every `c₀ > 0`, if `μ_N(K) > c₀ K⁻²` and `J ≥ c K log K`, then the depth-`NJ`
projection has length at most `B/K`. -/
def PropagationStatement : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
    ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ,
      ENNReal.ofReal (c₀ / K ^ 2) < volume (superLevel N θ K) → c * K * Real.log K ≤ J →
        projLength (N * J) θ ≤ B / K

end Favard.Comb
