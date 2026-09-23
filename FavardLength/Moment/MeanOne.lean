import FavardLength.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Data.Finset.Max

/-!
# The mean-one lemma for lacunary cosine products

We prove `Favard.MeanOneStatement`: for `β > 0`, `a : ℕ` and a finite set `S ⊆ [a, ∞)` of
natural numbers, the lacunary product `∏_{k ∈ S} (1 + cos(β 4^k w))` has mean one over every
interval of length `T_a = 2π / (β 4^a)`.

The proof uses no Fourier series. We induct on `S` by removing its minimum `k₀ ≥ a`, writing the
product as `(1 + cos(β 4^{k₀} w)) · g(w)` with `g = ∏_{k ∈ S \ {k₀}}`. The term `g` has mean one by
the induction hypothesis. The cross term `h(w) = cos(β 4^{k₀} w) g(w)` is antiperiodic with
antiperiod `P = π / (β 4^{k₀})`: the cosine changes sign, while every factor of `g` has a frequency
`β 4^k` with `k > k₀`, so its phase moves by the multiple `4^{k - k₀} π` of `2π`. An antiperiodic
function has integral zero over every interval of length `n · 2P`, and `T_a = 4^{k₀ - a} · 2P`.
-/

open MeasureTheory Real

namespace Favard

namespace MeanOne

/-- A continuous function with `h (w + P) = - h w` has integral zero over every interval whose
length is a natural multiple of `2P`. -/
lemma integral_eq_zero_of_antiperiodic {h : ℝ → ℝ} (hc : Continuous h) {P : ℝ}
    (hP : ∀ w, h (w + P) = -h w) (n : ℕ) (x : ℝ) :
    ∫ w in x..x + n * (2 * P), h w = 0 := by
  have hper : Function.Periodic h (2 * P) := fun w => by
    rw [two_mul, ← add_assoc, hP, hP, neg_neg]
  have hint : ∀ t₁ t₂, IntervalIntegrable h volume t₁ t₂ := fun _ _ => hc.intervalIntegrable _ _
  have h1 : ∫ w in x..x + 2 * P, h w = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint x (x + P)) (hint (x + P) _)]
    have : ∫ w in x + P..x + 2 * P, h w = ∫ w in x..x + P, h (w + P) := by
      rw [intervalIntegral.integral_comp_add_right, add_assoc x P P, ← two_mul]
    rw [this]
    simp only [hP, intervalIntegral.integral_neg, add_neg_cancel]
  have := hper.intervalIntegral_add_zsmul_eq (n : ℤ) x hint
  rw [h1, smul_zero] at this
  simpa [zsmul_eq_mul] using this

/-- Shifting by half a period of the frequency `β 4^{k₀}` changes the phase of the frequency
`β 4^k`, `k > k₀`, by a multiple of `2π`. -/
lemma cos_shift_of_lt {β : ℝ} (hβ : 0 < β) {k₀ k : ℕ} (hk : k₀ < k) (w : ℝ) :
    cos (β * 4 ^ k * (w + π / (β * 4 ^ k₀))) = cos (β * 4 ^ k * w) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have h4 : (0 : ℝ) < 4 ^ k₀ := by positivity
  have : β * 4 ^ (k₀ + j + 1) * (w + π / (β * 4 ^ k₀)) =
      β * 4 ^ (k₀ + j + 1) * w + ((2 * 4 ^ j : ℕ) : ℝ) * (2 * π) := by
    push_cast
    rw [pow_succ, pow_add]
    field_simp
    ring
  rw [this, cos_add_nat_mul_two_pi]

/-- Shifting by half a period of the frequency `β 4^{k₀}` flips the sign of `cos(β 4^{k₀} w)`. -/
lemma cos_shift_self {β : ℝ} (hβ : 0 < β) (k₀ : ℕ) (w : ℝ) :
    cos (β * 4 ^ k₀ * (w + π / (β * 4 ^ k₀))) = -cos (β * 4 ^ k₀ * w) := by
  have h4 : (0 : ℝ) < 4 ^ k₀ := by positivity
  have : β * 4 ^ k₀ * (w + π / (β * 4 ^ k₀)) = β * 4 ^ k₀ * w + π := by
    field_simp
  rw [this, cos_add_pi]

/-- The general mean-one lemma, with the base index `a` quantified inside so that the induction on
`S` can use it. -/
lemma integral_prod_eq (β : ℝ) (hβ : 0 < β) (S : Finset ℕ) :
    ∀ a : ℕ, (∀ k ∈ S, a ≤ k) → ∀ x : ℝ,
      ∫ w in x..x + 2 * π / (β * 4 ^ a), ∏ k ∈ S, (1 + cos (β * 4 ^ k * w)) =
        2 * π / (β * 4 ^ a) := by
  induction S using Finset.induction_on_min with
  | empty => intro a _ x; simp
  | insert k₀ S hk₀ ih =>
    intro a ha x
    have hk₀S : k₀ ∉ S := fun h => lt_irrefl _ (hk₀ k₀ h)
    have hak₀ : a ≤ k₀ := ha k₀ (Finset.mem_insert_self _ _)
    have hgc : Continuous fun w => ∏ k ∈ S, (1 + cos (β * 4 ^ k * w)) :=
      continuous_finsetProd _ fun k _ => by fun_prop
    have hcc : Continuous fun w => cos (β * 4 ^ k₀ * w) := by fun_prop
    have hhc : Continuous fun w => cos (β * 4 ^ k₀ * w) * ∏ k ∈ S, (1 + cos (β * 4 ^ k * w)) :=
      hcc.mul hgc
    simp_rw [Finset.prod_insert hk₀S, add_mul, one_mul]
    rw [intervalIntegral.integral_add (hgc.intervalIntegrable _ _)
      (hhc.intervalIntegrable _ _)]
    rw [ih a (fun k hk => hak₀.trans (hk₀ k hk).le) x, add_eq_left]
    -- the cross term is antiperiodic with antiperiod `π / (β 4^{k₀})`
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hak₀
    have hT : 2 * π / (β * 4 ^ a) = ((4 ^ d : ℕ) : ℝ) * (2 * (π / (β * 4 ^ (a + d)))) := by
      have h4 : (0 : ℝ) < 4 ^ a := by positivity
      have h4' : (0 : ℝ) < 4 ^ d := by positivity
      push_cast
      rw [pow_add]
      field_simp
    rw [hT]
    refine integral_eq_zero_of_antiperiodic hhc (fun w => ?_) _ x
    rw [cos_shift_self hβ, neg_mul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by rw [cos_shift_of_lt hβ (hk₀ k hk)]

end MeanOne

/-- **Mean-one lemma** for lacunary cosine products: over any interval of length `2π/(β 4^a)`,
`∏_{k ∈ S} (1 + cos(β 4^k w))` has mean one when `S ⊆ [a, ∞)`. -/
theorem meanOne : MeanOneStatement := fun β hβ a S hS x =>
  MeanOne.integral_prod_eq β hβ S a hS x

end Favard
