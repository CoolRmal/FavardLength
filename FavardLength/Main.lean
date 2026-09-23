import FavardLength.Basic
import FavardLength.Combinatorics.Main
import FavardLength.Combinatorics.Packing
import FavardLength.Combinatorics.Propagation
import FavardLength.Moment.MeanOne
import FavardLength.Moment.Hilbert
import FavardLength.Moment.SineCell
import FavardLength.Moment.LowCell
import FavardLength.Moment.JointMoment
import FavardLength.Fourier.Window
import FavardLength.Fourier.Annular
import FavardLength.Fourier.Exceptional
import FavardLength.Fourier.Triangle
import FavardLength.Fourier.Bridge
import FavardLength.Fourier.Angle
import FavardLength.LowerBound.Main
import FavardLength.Decay
import FavardLength.Exponent

/-!
# Assembly

Plugs the proofs of the part contracts of `FavardLength/Statements.lean` together.

* Geometric side: the combinatorial dichotomy (G1–G17).
* Analytic side: the mean-one lemma, the sine-cell and low-product cell estimates, and the
  Hilbert-matrix inequality give the joint negative moment (J1). With the frequency window (P2)
  and the annular lower bound (P3) it gives the normalized exceptional-direction estimate (J9).
  The triangle identity gives the normalization bridge (P1), which transfers J9 to angles.
* Decay (J10–J11) and the elementary lower bound (L1–L2) give the exponent bounds.
-/

namespace Favard

/-- The combinatorial dichotomy (G1–G17). -/
theorem dichotomy : DichotomyStatement :=
  dichotomy_of_packing Comb.packing Comb.propagation

/-- The joint negative-moment estimate (J1). -/
theorem jointMoment : JointMomentStatement :=
  jointMoment_of (sineCell_of meanOne) (lowCell_of meanOne) hilbert

/-- The exceptional-direction estimate (J9) in the angle variable. -/
theorem exceptionalAngle : ExceptionalAngleStatement :=
  exceptionalAngle_of (normalizedExceptional_of window annular jointMoment) (bridge_of triangle)

/-- Every exponent `a ∈ [0, 1/4)` is admissible. -/
theorem decay (a : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1 / 4) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a) :=
  decay_of dichotomy exceptionalAngle a ha₀ ha

/-- `1/4 ≤ α_Fav ≤ 1`. -/
theorem exponent_bounds : 1 / 4 ≤ decayExponent ∧ decayExponent ≤ 1 :=
  exponent_bounds_of decay lowerBound

end Favard
