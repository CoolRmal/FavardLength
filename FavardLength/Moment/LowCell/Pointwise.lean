import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pointwise bounds by local `L²` norms of a function and its derivative

For a function `g` with continuous derivative `g'` and an interval `[p, q]` of length
`h = q - p > 0`, every value of `g` on `[p, q]` satisfies
`g(x)² ≤ (2/h) ∫_p^q g² + 2h ∫_p^q g'²`
(the one-dimensional Sobolev-type bound used for the low-frequency cells, manuscript J5).

The proof writes `g x = g y + ∫_y^x g'` for `y ∈ [p, q]`, uses `(a + b)² ≤ 2a² + 2b²` and the
Cauchy–Schwarz inequality `(∫_a^b f)² ≤ (b - a) ∫_a^b f²` (proved by expanding
`∫_a^b (f - c)² ≥ 0` at the mean `c`), and averages over `y ∈ [p, q]`.
-/

open MeasureTheory Set

namespace Favard.LowCell

/-- **Cauchy–Schwarz on an interval**: `(∫_a^b f)² ≤ (b - a) ∫_a^b f²` for continuous `f`. -/
lemma sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hba : 0 < b - a := sub_pos.2 hlt
  set I := ∫ x in a..b, f x with hIdef
  set c := I / (b - a) with hc
  have h0 : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hexp : ∫ x in a..b, (f x - c) ^ 2 =
      (∫ x in a..b, f x ^ 2) - 2 * c * I + c ^ 2 * (b - a) := by
    have : ∀ x, (f x - c) ^ 2 = (f x ^ 2 - 2 * c * f x) + c ^ 2 := fun x => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    · ring
    · exact (hf.pow 2).intervalIntegrable _ _
    · exact (hf.const_mul _).intervalIntegrable _ _
    · exact ((hf.pow 2).sub (hf.const_mul _)).intervalIntegrable _ _
    · exact intervalIntegrable_const
  have hI : I = c * (b - a) := by rw [hc]; field_simp
  rw [hexp] at h0
  have := mul_nonneg hba.le h0
  nlinarith

/-- **Pointwise bound on a cell**: if `g` has continuous derivative `g'`, then for `x ∈ [p, q]`,
`g(x)² ≤ (2/(q-p)) ∫_p^q g² + 2(q-p) ∫_p^q g'²`. -/
theorem sq_le_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') {p q : ℝ} (hpq : p < q) {x : ℝ} (hx : x ∈ Icc p q) :
    g x ^ 2 ≤ 2 / (q - p) * (∫ y in p..q, g y ^ 2) + 2 * (q - p) * ∫ y in p..q, g' y ^ 2 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hqp : 0 < q - p := sub_pos.2 hpq
  set K := ∫ y in p..q, g' y ^ 2 with hKdef
  have hK : ∀ y ∈ Icc p q, (∫ t in y..x, g' t) ^ 2 ≤ (q - p) * K := by
    intro y hy
    have key : ∀ a b, p ≤ a → a ≤ b → b ≤ q → (∫ t in a..b, g' t) ^ 2 ≤ (q - p) * K := by
      intro a b hpa hab hbq
      calc (∫ t in a..b, g' t) ^ 2 ≤ (b - a) * ∫ t in a..b, g' t ^ 2 :=
            sq_intervalIntegral_le hg' hab
        _ ≤ (q - p) * K := by
          refine mul_le_mul (by linarith) ?_
            (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _) hqp.le
          exact intervalIntegral.integral_mono_interval hpa hab hbq
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            ((hg'.pow 2).intervalIntegrable _ _)
    rcases le_total y x with h | h
    · exact key y x hy.1 h hx.2
    · rw [intervalIntegral.integral_symm, neg_sq]
      exact key x y hx.1 h hy.2
  have hpt : ∀ y ∈ Icc p q, g x ^ 2 ≤ 2 * g y ^ 2 + 2 * ((q - p) * K) := by
    intro y hy
    have hftc : ∫ t in y..x, g' t = g x - g y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
        (hg'.intervalIntegrable _ _)
    have := hK y hy
    rw [hftc] at this
    nlinarith [sq_nonneg (2 * g y - g x)]
  have hint := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => g x ^ 2)
    (g := fun y => 2 * g y ^ 2 + 2 * ((q - p) * K)) hpq.le
    (continuous_const.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul] at hint
  · have : 2 / (q - p) * (∫ y in p..q, g y ^ 2) + 2 * (q - p) * K =
        (2 * (∫ y in p..q, g y ^ 2) + (q - p) * (2 * ((q - p) * K))) / (q - p) := by
      field_simp
    rw [this, le_div_iff₀ hqp]
    linarith
  · exact ((hgc.pow 2).const_mul 2).intervalIntegrable _ _
  · exact intervalIntegrable_const

end Favard.LowCell
