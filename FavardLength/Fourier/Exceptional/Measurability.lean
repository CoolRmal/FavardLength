import FavardLength.Fourier.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuity and measurability for the exceptional-direction estimate

The factors `φ_t(z)`, the products `ν̂_{r,t}(ξ)`, `P₁(t,y)` and `P₂(t,y)` are jointly continuous in
the slope and the frequency. Consequently `t ↦ normEnergy r t` is measurable, being a parametric
Bochner integral of a jointly continuous integrand, and the set of slopes `t ∈ [0,1]` whose
normalized energies of generations `1, …, N` are at most `H` is measurable. This is the set `E`
of the manuscript's section "Consequence for exceptional directions" (J9).
-/

open MeasureTheory Set Real

namespace Favard.Exceptional

lemma continuous_phi : Continuous fun p : ℝ × ℝ => phi p.1 p.2 := by
  unfold phi; fun_prop

lemma continuous_nuHat (r : ℕ) : Continuous fun p : ℝ × ℝ => nuHat r p.1 p.2 := by
  unfold nuHat phi; fun_prop

/-- The low-frequency product `P₁(t,y)` is jointly continuous. -/
lemma continuous_lowProd (m : ℕ) : Continuous fun p : ℝ × ℝ => lowProd m p.1 p.2 := by
  unfold lowProd phi; fun_prop

/-- The high-frequency product `P₂(t,y)` is jointly continuous. -/
lemma continuous_highProd (m n : ℕ) : Continuous fun p : ℝ × ℝ => highProd m n p.1 p.2 := by
  unfold highProd phi; fun_prop

/-- The normalized energy is a measurable function of the slope. -/
lemma measurable_normEnergy (r : ℕ) : Measurable (normEnergy r) := by
  have h : Continuous fun p : ℝ × ℝ => sinc (4 / 3 / 4 ^ r * p.2) ^ 2 * nuHat r p.1 p.2 ^ 2 := by
    have := continuous_nuHat r
    fun_prop
  have hint := h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  exact hint.measurable.const_mul _

/-- The set of slopes whose normalized energies of generations `1, …, N` are at most `H` is
measurable. -/
lemma measurableSet_lowEnergy (H : ℝ) (N : ℕ) :
    MeasurableSet {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} := by
  have : {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} =
      Icc 0 1 ∩ ⋂ r, ⋂ (_ : 1 ≤ r), ⋂ (_ : r ≤ N), {t | normEnergy r t ≤ H} := by
    ext; simp
  rw [this]
  exact measurableSet_Icc.inter <| MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_normEnergy r) measurable_const

end Favard.Exceptional
