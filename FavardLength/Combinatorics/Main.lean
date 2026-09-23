import FavardLength.Statements
import FavardLength.Combinatorics.Absorption

/-!
# Assembly of the combinatorial dichotomy

`Favard.dichotomy_of` derives the contract `Favard.DichotomyStatement` from the energy absorption
and propagation sub-contracts of `FavardLength/Combinatorics/Statements.lean`: fix `θ`, `K ≥ 2`,
`N`, `J ≥ c K log K` with `|π_θ(K_{NJ})| > B/K`. The second alternative is excluded, so
`μ_N(K) ≤ c₀ K⁻²`, and then every generation `r ≤ N` has energy
`∫ f_r² ≤ ∫ F_N² ≤ A K`.

Since energy absorption is proved from the packing inequality
(`Favard.Comb.energyAbsorption_of_packing`), `Favard.dichotomy_of_packing` derives the dichotomy
from the two remaining sub-contracts `PackingStatement` (G6–G9) and `PropagationStatement`
(G13–G17).
-/

open MeasureTheory Set Real

namespace Favard

open Comb

/-- The combinatorial dichotomy from energy absorption and propagation. -/
theorem dichotomy_of (hA : EnergyAbsorptionStatement) (hB : PropagationStatement) :
    DichotomyStatement := by
  obtain ⟨c₀, A, hc₀, hA0, hAbs⟩ := hA
  obtain ⟨c, B, hc, hB0, hProp⟩ := hB c₀ hc₀
  refine ⟨A, B, c, hA0, hB0, hc, fun θ hθ K hK N J hJ hproj r hr => ?_⟩
  by_cases hμ : volume (superLevel N θ K) ≤ ENNReal.ofReal (c₀ / K ^ 2)
  · exact (energy_le_integral_maxCount_sq hθ hr).trans (hAbs θ hθ K hK N hμ)
  · exact absurd (hProp θ hθ K hK N J (not_le.mp hμ) hJ) (not_le.mpr hproj)

/-- The combinatorial dichotomy from the packing inequality (G6–G9) and propagation
(G13–G17). -/
theorem dichotomy_of_packing (hP : PackingStatement) (hB : PropagationStatement) :
    DichotomyStatement :=
  dichotomy_of (energyAbsorption_of_packing hP) hB

end Favard
