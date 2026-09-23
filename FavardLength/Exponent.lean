import FavardLength.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounds on the Favard-length decay exponent

From a family of upper bounds `Fav(K_n) ≤ C n^{-a}` for every `a < 1/4` and the elementary
lower bound `Fav(K_n) ≥ c/n`, we deduce `1/4 ≤ α_Fav ≤ 1`, where `α_Fav = decayExponent` is the
supremum of the admissible exponents.
-/

open Filter Topology Set

namespace Favard

/-- Under the elementary lower bound `c/n ≤ Fav(K_n)`, every admissible exponent is at most `1`. -/
lemma admissibleExponents_subset_Iic_one (hL : LowerBoundStatement) :
    admissibleExponents ⊆ Iic 1 := by
  obtain ⟨c, hc, hcL⟩ := hL
  rintro a ⟨-, C, hC, hCa⟩
  by_contra ha
  simp only [mem_Iic, not_le] at ha
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 - a)) atTop (𝓝 (C * 0)) :=
    ((tendsto_rpow_neg_atTop (y := a - 1) (by linarith)).comp
      tendsto_natCast_atTop_atTop).const_mul C |>.congr fun n => by
        simp [Function.comp, neg_sub]
  rw [mul_zero] at hlim
  obtain ⟨n, hn⟩ := ((hlim.eventually (gt_mem_nhds hc)).and (eventually_ge_atTop 1)).exists
  obtain ⟨hlt, hn1⟩ := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h := (hcL n hn1).trans (hCa n hn1)
  rw [div_le_iff₀ hnpos, mul_assoc, ← Real.rpow_add_one hnpos.ne'] at h
  have : -a + 1 = 1 - a := by ring
  rw [this] at h
  linarith

/-- `0` is admissible under the decay hypothesis. -/
lemma zero_mem_admissibleExponents
    (hdecay : ∀ a : ℝ, 0 ≤ a → a < 1 / 4 →
      ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a)) :
    (0 : ℝ) ∈ admissibleExponents :=
  ⟨le_rfl, hdecay 0 le_rfl (by norm_num)⟩

/-- **Exponent bounds**: decay bounds for every exponent below `1/4` together with the
elementary lower bound give `1/4 ≤ α_Fav ≤ 1`. -/
theorem exponent_bounds_of
    (hdecay : ∀ a : ℝ, 0 ≤ a → a < 1 / 4 →
      ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a))
    (hL : LowerBoundStatement) : 1 / 4 ≤ decayExponent ∧ decayExponent ≤ 1 := by
  have hsub := admissibleExponents_subset_Iic_one hL
  have hne : admissibleExponents.Nonempty := ⟨0, zero_mem_admissibleExponents hdecay⟩
  have hbdd : BddAbove admissibleExponents := ⟨1, fun a ha => hsub ha⟩
  refine ⟨?_, csSup_le hne fun a ha => hsub ha⟩
  refine le_of_forall_lt fun b hb => ?_
  rcases lt_or_ge b 0 with hb0 | hb0
  · exact hb0.trans_le (le_csSup hbdd (zero_mem_admissibleExponents hdecay))
  · obtain ⟨a, hba, ha⟩ := exists_between hb
    exact hba.trans_le (le_csSup hbdd ⟨hb0.trans hba.le, hdecay a (hb0.trans hba.le) ha⟩)

end Favard
