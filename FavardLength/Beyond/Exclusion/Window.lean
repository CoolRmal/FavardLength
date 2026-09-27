import FavardLength.Beyond.Exclusion.Statements
import FavardLength.Beyond.Exclusion.Window.Averaging
import FavardLength.Beyond.Exclusion.Window.Plateau
import FavardLength.Beyond.Exclusion.Window.Taylor

/-!
# Window bounds

Proof of the sub-contract `WindowBoundStatement` (part (e) of the smooth-window exclusion,
Appendix G §4). Let `g = ∑_i f_{n,t}(· - β_i)` be flat on the middle half of `[0, T]` at
resolution `h = T/4^L` with squared error `e ≤ 1`.

* **Plateau count** (G (12), `Exclusion.plateau_count`): `αT(1/8 - √e) ≤ ∑_i χ(β_i/T)²`.
* **Taylor expansion** (G (14)–(15), `Exclusion.exists_norm_windowTransform_sub_expandedWindow_le`):
  the window transform `I(ξ) = ∫ χ(x/T) e^{-2πiξx} g(x) dx` differs from the expanded window
  transform by at most `C m/T^{J+1}`.
* **Flat-block upper bound** (G (18)–(19), `Exclusion.exists_norm_windowTransform_le`):
  `|I(ξ)| ≤ C αT (√e + hξ + (Tξ)^{-J})` for `ξ ≥ 1/4`.

The bound on the expanded window transform follows by the triangle inequality.
-/

open Real

namespace Favard.Exclusion

/-- **(e) Window bounds** (Appendix G (12), (14)–(15), (18)–(19)). -/
theorem windowBound : WindowBoundStatement := by
  intro J
  obtain ⟨C₁, hC₁, htay⟩ := exists_norm_windowTransform_sub_expandedWindow_le J
  obtain ⟨C₂, -, havg⟩ := exists_norm_windowTransform_le J
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁,
    fun n L m t T α e ξ β ht hT hL hα he he1 hξ hflat => ?_⟩
  have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have hT0 : 0 < T := by linarith
  refine ⟨plateau_count β ht' hT hL hα he hflat, ?_⟩
  have h1 := htay n m t T ξ β ht' hT0
  have h2 := havg n L m t T α e ξ β hT (by omega) hα he he1 hξ hflat
  have htri : ‖expandedWindow J n t T ξ β‖ ≤ ‖windowTransform n t T ξ β‖ +
      ‖windowTransform n t T ξ β - expandedWindow J n t T ξ β‖ := by
    have := norm_sub_le (windowTransform n t T ξ β)
      (windowTransform n t T ξ β - expandedWindow J n t T ξ β)
    rwa [sub_sub_cancel] at this
  have hξ0 : 0 < ξ := by linarith
  have a1 : C₁ * m / T ^ (J + 1) ≤ max C₁ C₂ * m / T ^ (J + 1) := by
    gcongr
    exact le_max_left _ _
  have a2 : C₂ * α * T * (√e + T / 4 ^ L * ξ + 1 / (T * ξ) ^ J) ≤
      max C₁ C₂ * α * T * (√e + T / 4 ^ L * ξ + 1 / (T * ξ) ^ J) := by
    gcongr
    exact le_max_right _ _
  linarith

end Favard.Exclusion
