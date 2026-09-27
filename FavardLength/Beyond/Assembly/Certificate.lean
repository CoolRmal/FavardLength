import FavardLength.Beyond.Statements

/-!
# Exact arithmetic certificates for the beyond-quarter assembly

The sixth-moment dimension `d = log₄(5/4)` satisfies `d < 161/1000` (beyond note (27)), because
`5^1000 < 4^1161`; this exact comparison of natural numbers is checked by the kernel, whose
natural-number arithmetic is implemented with GMP. Consequently the redundancy exponent
`μ = 1 - 2d - 6γ₀ - 4ε₀` of the parameters `γ₀ = 13/125`, `ε₀ = 1/100000` satisfies
`μ > 1349/25000` (beyond note (28)).
-/

namespace Favard.Assembly

/-- The exact integer comparison `5^1000 < 4^1161` behind `log₄(5/4) < 161/1000`. -/
theorem five_pow_lt_four_pow : (5 : ℕ) ^ 1000 < 4 ^ 1161 := by
  decide +kernel

/-- `d = log₄(5/4) < 161/1000` (beyond note (27)). -/
theorem sixthMomentDim_lt : sixthMomentDim < 161 / 1000 := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have key : ((5 : ℝ) / 4) ^ 1000 < 4 ^ 161 := by
    have h := (Nat.cast_lt (α := ℝ)).mpr five_pow_lt_four_pow
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat] at h
    rw [div_pow, div_lt_iff₀ (by positivity), ← pow_add]
    exact h
  have hlog := Real.log_lt_log (by positivity) key
  rw [Real.log_pow, Real.log_pow] at hlog
  unfold sixthMomentDim Real.logb
  rw [div_lt_iff₀ h4]
  push_cast at hlog
  linarith

/-- `μ(γ₀, ε₀) > 1349/25000` for `γ₀ = 13/125`, `ε₀ = 1/100000` (beyond note (28)). -/
theorem redundancyExp_gt : 1349 / 25000 < redundancyExp (13 / 125) (1 / 100000) := by
  have := sixthMomentDim_lt
  unfold redundancyExp
  linarith

end Favard.Assembly
