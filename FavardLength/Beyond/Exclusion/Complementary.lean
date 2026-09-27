import FavardLength.Beyond.Exclusion.Complementary.LowerBound
import FavardLength.Beyond.Exclusion.Complementary.SixthMoment
import FavardLength.Beyond.Exclusion.Statements

/-!
# Exclusion (a): complementary products

We prove the two sub-contracts of part (a) of the smooth-window exclusion (Appendix H
§§1–3, 5 of `references/beyond/favard-beyond-quarter-complete.md`):

* `Favard.Exclusion.complementaryCount : ComplementaryCountStatement`, the sixth-moment count
  `#X_{B,γ,K} ≤ C K B^{2d+6γ}`, `d = log₄(5/4)` (H (19)). For a fixed odd harmonic `h`, a marked
  pair has `1 < B^{6γ} |A(ph/2) A(qh/2)|^6` (Markov), the sum over all odd pairs factors as the
  square of the single sixth moment `∑_{p odd ≤ B} |A(ph/2)|^6 ≤ (5/4) B^d`
  (`sum_absCosProd_pow_six_le`), and a union bound over the at most `K` odd harmonics `h ≤ K`
  finishes the count with `C = (5/4)²`.
* `Favard.Exclusion.complementaryBound : ComplementaryBoundStatement`, the lower bound
  `|A_n(pk) A_n(qk)| ≥ 4B^{γ-2}/(π²k²)` outside the exceptional set (H (6)). Removing the power
  of four from `k = 4^v h` gives `|A_n(pk)| ≥ |A(ph)|`
  (`absCosProd_le_abs_cosProd_four_pow_mul`), completing the binary scales gives
  `|A(ph)| |A(ph/2)| ≥ 2/(πph)` for the odd integer `ph` (`two_div_pi_mul_le_absCosProd_mul`),
  and outside the exceptional set `|A(ph/2) A(qh/2)| ≤ B^{-γ}`.
-/

open Real Finset

namespace Favard.Exclusion

/-- **Markov step**: if `B^{-γ} < x` then `1 < B^{6γ} x^6`. -/
lemma one_lt_rpow_mul_pow_six {B γ x : ℝ} (hB : 0 < B) (hx : B ^ (-γ) < x) :
    1 < B ^ (6 * γ) * x ^ 6 := by
  have h1 : B ^ (6 * γ) * (B ^ (-γ)) ^ 6 = 1 := by
    rw [← rpow_mul_natCast hB.le, ← rpow_add hB,
      show 6 * γ + -γ * ((6 : ℕ) : ℝ) = 0 by push_cast; ring, rpow_zero]
  have h0 : 0 ≤ B ^ (-γ) := (rpow_pos_of_pos hB _).le
  calc (1 : ℝ) = B ^ (6 * γ) * (B ^ (-γ)) ^ 6 := h1.symm
    _ < B ^ (6 * γ) * x ^ 6 := by gcongr

/-- The odd numbers in `[0, K]` are at most `K` in number. -/
lemma card_filter_odd_range_le (K : ℕ) : ((range (K + 1)).filter Odd).card ≤ K := by
  have hsub : (range (K + 1)).filter Odd ⊆ Icc 1 K := by
    intro h hh
    obtain ⟨hr, hodd⟩ := mem_filter.mp hh
    rw [mem_range] at hr
    have := hodd.pos
    rw [mem_Icc]
    omega
  simpa using card_le_card hsub

/-- **(a) Sixth-moment count** (Appendix H (17)–(19)):
`#X_{B,γ,K} ≤ (5/4)² K B^{2d+6γ}` with `d = log₄(5/4)`. -/
theorem complementaryCount : ComplementaryCountStatement := by
  refine ⟨(5 / 4) ^ 2, by norm_num, fun γ B K hB => ?_⟩
  have hB0 : 0 < B := by linarith
  set P := (range (⌊B⌋₊ + 1)).filter Odd
  set H := (range (K + 1)).filter Odd
  -- the sixth power of a single factor
  set f : ℕ → ℕ → ℝ := fun h p => absCosProd ((p : ℝ) * h / 2) ^ 6 with hf
  have hf0 : ∀ h p, 0 ≤ f h p := fun h p => pow_nonneg (absCosProd_nonneg _) 6
  -- the Markov majorant of the indicator of `X`
  set g : ℕ × ℕ → ℝ := fun pq : ℕ × ℕ => ∑ h ∈ H, B ^ (6 * γ) * (f h pq.1 * f h pq.2) with hg
  have hterm0 : ∀ (h : ℕ) (pq : ℕ × ℕ), 0 ≤ B ^ (6 * γ) * (f h pq.1 * f h pq.2) := fun h pq =>
    mul_nonneg (rpow_pos_of_pos hB0 _).le (mul_nonneg (hf0 h pq.1) (hf0 h pq.2))
  have hg0 : ∀ pq : ℕ × ℕ, 0 ≤ g pq := fun pq => sum_nonneg fun h _ => hterm0 h pq
  have hXP : exceptionalSet B γ K ⊆ P ×ˢ P := by
    intro pq hpq
    simp only [exceptionalSet, mem_filter] at hpq
    obtain ⟨hmem, hodd1, hodd2, -⟩ := hpq
    rw [mem_product] at hmem ⊢
    exact ⟨mem_filter.mpr ⟨hmem.1, hodd1⟩, mem_filter.mpr ⟨hmem.2, hodd2⟩⟩
  have hone : ∀ pq ∈ exceptionalSet B γ K, (1 : ℝ) ≤ g pq := by
    intro pq hpq
    simp only [exceptionalSet, mem_filter] at hpq
    obtain ⟨-, -, -, h, hhK, hh, hlt⟩ := hpq
    calc (1 : ℝ) ≤ B ^ (6 * γ) * (f h pq.1 * f h pq.2) := by
          rw [hf]
          simp only
          rw [← mul_pow]
          exact (one_lt_rpow_mul_pow_six hB0 hlt).le
      _ ≤ g pq :=
          single_le_sum (f := fun h => B ^ (6 * γ) * (f h pq.1 * f h pq.2))
            (fun h _ => hterm0 h pq) (mem_filter.mpr ⟨hhK, hh⟩)
  have hHK : (H.card : ℝ) ≤ K := by exact_mod_cast card_filter_odd_range_le K
  have hmom : ∀ h ∈ H, ∑ p ∈ P, f h p ≤ 5 / 4 * B ^ sixthMomentDim := fun h hh =>
    sum_absCosProd_pow_six_le (mem_filter.mp hh).2 hB
  have hB2 : B ^ (2 * sixthMomentDim + 6 * γ) =
      B ^ sixthMomentDim * B ^ sixthMomentDim * B ^ (6 * γ) := by
    rw [rpow_add hB0, two_mul, rpow_add hB0]
  calc ((exceptionalSet B γ K).card : ℝ) = ∑ pq ∈ exceptionalSet B γ K, (1 : ℝ) := by simp
    _ ≤ ∑ pq ∈ exceptionalSet B γ K, g pq := sum_le_sum hone
    _ ≤ ∑ pq ∈ P ×ˢ P, g pq := sum_le_sum_of_subset_of_nonneg hXP fun pq _ _ => hg0 pq
    _ = ∑ h ∈ H, B ^ (6 * γ) * (∑ p ∈ P, f h p) ^ 2 := by
        rw [hg, sum_comm]
        refine sum_congr rfl fun h _ => ?_
        rw [← mul_sum, sum_product, sq, sum_mul_sum]
    _ ≤ ∑ h ∈ H, B ^ (6 * γ) * (5 / 4 * B ^ sixthMomentDim) ^ 2 := by
        refine sum_le_sum fun h hh => ?_
        have hs0 : 0 ≤ ∑ p ∈ P, f h p := sum_nonneg fun p _ => hf0 h p
        gcongr
        exact hmom h hh
    _ = H.card * (B ^ (6 * γ) * (5 / 4 * B ^ sixthMomentDim) ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ K * (B ^ (6 * γ) * (5 / 4 * B ^ sixthMomentDim) ^ 2) := by gcongr
    _ = (5 / 4) ^ 2 * K * B ^ (2 * sixthMomentDim + 6 * γ) := by
        rw [hB2]
        ring

/-- **(a) Complementary lower bound** (Appendix H (5)–(6)): for odd `p, q ≤ B` outside
`X_{B,γ,K}` and `k = 4^v h` with `h ≤ K` odd, `|A_n(pk) A_n(qk)| ≥ 4 B^{γ-2}/(π² k²)`. -/
theorem complementaryBound : ComplementaryBoundStatement := by
  intro γ B K p q k v h n hB hp hq hpB hqB hX hh hhK hk
  have hB0 : 0 < B := by linarith
  -- outside the exceptional set the complementary product is at most `B^{-γ}`
  have hcomp : absCosProd ((p : ℝ) * h / 2) * absCosProd ((q : ℝ) * h / 2) ≤ B ^ (-γ) := by
    by_contra hlt
    apply hX
    simp only [exceptionalSet, mem_filter, mem_product, mem_range]
    exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hpB), Nat.lt_succ_of_le (Nat.le_floor hqB)⟩, hp, hq,
      h, by omega, hh, not_le.mp hlt⟩
  -- completing the binary scales at the odd integers `ph` and `qh`
  have hP := two_div_pi_mul_le_absCosProd_mul (hp.mul hh)
  have hQ := two_div_pi_mul_le_absCosProd_mul (hq.mul hh)
  push_cast at hP hQ
  -- removing the power of four from `k`
  have hAp : absCosProd ((p : ℝ) * h) ≤ |cosProd n ((p : ℝ) * k)| := by
    have := absCosProd_le_abs_cosProd_four_pow_mul (p * h) v n
    rw [hk]
    push_cast at this ⊢
    rwa [show (p : ℝ) * (4 ^ v * h) = 4 ^ v * (p * h) by ring]
  have hAq : absCosProd ((q : ℝ) * h) ≤ |cosProd n ((q : ℝ) * k)| := by
    have := absCosProd_le_abs_cosProd_four_pow_mul (q * h) v n
    rw [hk]
    push_cast at this ⊢
    rwa [show (q : ℝ) * (4 ^ v * h) = 4 ^ v * (q * h) by ring]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.pos
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.pos
  have hhk : (h : ℝ) ≤ k := by
    rw [hk]
    push_cast
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 4) (by norm_num) (n := v)]
  set a₁ := absCosProd ((p : ℝ) * h)
  set a₂ := absCosProd ((p : ℝ) * h / 2)
  set b₁ := absCosProd ((q : ℝ) * h)
  set b₂ := absCosProd ((q : ℝ) * h / 2)
  have ha₁ : 0 ≤ a₁ := absCosProd_nonneg _
  have hb₁ : 0 ≤ b₁ := absCosProd_nonneg _
  have ha₂ : 0 ≤ a₂ := absCosProd_nonneg _
  have hb₂ : 0 ≤ b₂ := absCosProd_nonneg _
  have hprod : 4 / (π ^ 2 * (p * q * h ^ 2)) ≤ a₁ * b₁ * B ^ (-γ) := by
    calc 4 / (π ^ 2 * (p * q * h ^ 2)) = 2 / (π * (p * h)) * (2 / (π * (q * h))) := by
          field_simp
          ring
      _ ≤ a₁ * a₂ * (b₁ * b₂) := mul_le_mul hP hQ (by positivity) (mul_nonneg ha₁ ha₂)
      _ = a₁ * b₁ * (a₂ * b₂) := by ring
      _ ≤ a₁ * b₁ * B ^ (-γ) := by gcongr
  have hpqB : (p : ℝ) * q * h ^ 2 ≤ B ^ 2 * k ^ 2 := by
    have h1 : (p : ℝ) * q ≤ B ^ 2 := by nlinarith
    have h2 : (h : ℝ) ^ 2 ≤ k ^ 2 := by gcongr
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hBγ : B ^ (γ - 2) = B ^ γ / B ^ 2 := by
    rw [rpow_sub hB0, rpow_two]
  have hBpos : 0 < B ^ γ := rpow_pos_of_pos hB0 γ
  rw [abs_mul]
  calc 4 * B ^ (γ - 2) / (π ^ 2 * (k : ℝ) ^ 2) =
        B ^ γ * (4 / (π ^ 2 * (B ^ 2 * k ^ 2))) := by
        rw [hBγ]
        field_simp
    _ ≤ B ^ γ * (4 / (π ^ 2 * (p * q * h ^ 2))) := by
        gcongr B ^ γ * (4 / (π ^ 2 * ?_))
    _ ≤ B ^ γ * (a₁ * b₁ * B ^ (-γ)) := by gcongr
    _ = a₁ * b₁ := by
        rw [rpow_neg hB0.le]
        field_simp
    _ ≤ |cosProd n ((p : ℝ) * k)| * |cosProd n ((q : ℝ) * k)| :=
        mul_le_mul hAp hAq hb₁ (abs_nonneg _)

end Favard.Exclusion
