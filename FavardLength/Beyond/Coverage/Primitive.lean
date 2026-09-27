import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Primitive integer points of a parity class in a rectangle

Appendix I.2 of the beyond note. In a box of `L₁ × L₂` consecutive parameters `(j, k)`, the
integer points `(m, n) = (α + 2j, β + 2k)` of a fixed nonzero parity class `(α, β) mod 2` are
coprime for at least half of the parameters, provided `L₀ ≤ L₂ ≤ L₁` and the second coordinates
satisfy the location condition `|n| ≤ K L₂`.

Instead of Möbius inversion we use a union bound: a noncoprime pair with `n ≠ 0` has an odd common
divisor `3 ≤ d ≤ K L₂`; the pairs divisible by `d` number at most `(L₁/d + 1)(L₂/d + 1)`, and
`∑_{d ≥ 3 odd} d⁻² ≤ 1/4`. The harmonic-type sum `∑ 1/d` is controlled by Cauchy–Schwarz.
-/

open Finset

namespace Favard.Coverage

/-- A set of integers inside `L` consecutive integers whose elements are pairwise congruent
modulo `d` has at most `L / d + 1` elements. -/
theorem card_le_div_add_one_of_dvd_sub {d : ℕ} (hd : 0 < d) (j₀ : ℤ) (L : ℕ) {S : Finset ℤ}
    (hS : S ⊆ Ico j₀ (j₀ + L)) (hdvd : ∀ j ∈ S, ∀ j' ∈ S, (d : ℤ) ∣ j - j') :
    (#S : ℝ) ≤ L / d + 1 := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hmaps : Set.MapsTo (fun j : ℤ => ((j - j₀) / d).toNat) S (range (L / d + 1)) := by
    intro j hj
    have hj' := mem_Ico.1 (hS hj)
    rw [coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    show ((j - j₀) / d).toNat ≤ L / d
    rw [Int.toNat_le, Int.natCast_div]
    exact Int.ediv_le_ediv hd' (by omega)
  have hinj : Set.InjOn (fun j : ℤ => ((j - j₀) / d).toNat) S := by
    intro j hj j' hj' hjj
    simp only at hjj
    have hj1 := mem_Ico.1 (hS hj)
    have hj2 := mem_Ico.1 (hS hj')
    have hq1 : 0 ≤ (j - j₀) / d := Int.ediv_nonneg (by omega) hd'.le
    have hq2 : 0 ≤ (j' - j₀) / d := Int.ediv_nonneg (by omega) hd'.le
    have hq : (j - j₀) / d = (j' - j₀) / d := by
      have := congrArg (Nat.cast : ℕ → ℤ) hjj
      rwa [Int.toNat_of_nonneg hq1, Int.toNat_of_nonneg hq2] at this
    have hr : (j - j₀) % d = (j' - j₀) % d := by
      have h := hdvd j' hj' j hj
      have : (d : ℤ) ∣ (j' - j₀) - (j - j₀) := by
        rwa [show (j' - j₀) - (j - j₀) = j' - j by ring]
      exact Int.modEq_iff_dvd.2 this
    have e1 := Int.emod_add_mul_ediv (j - j₀) d
    have e2 := Int.emod_add_mul_ediv (j' - j₀) d
    rw [hq, hr] at e1
    linarith
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [card_range] at hcard
  calc (#S : ℝ) ≤ ((L / d + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ L / d + 1 := by push_cast; gcongr; exact Nat.cast_div_le

/-- The odd reciprocal squares from `3` on sum to at most `1/4`, by telescoping against
`1/((d - 1)(d + 1))`. -/
theorem sum_inv_odd_sq_le (N : ℕ) :
    ∑ i ∈ range N, (1 : ℝ) / (2 * i + 3) ^ 2 ≤ 1 / 4 - 1 / (4 * ((N : ℝ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have key : (1 : ℝ) / (2 * n + 3) ^ 2 ≤ 1 / (4 * (n + 1)) - 1 / (4 * (n + 1 + 1)) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/-- Elements of an interval of consecutive parameters whose affine image `α + 2j` is divisible
by the odd number `2i + 3`: at most `L / (2i + 3) + 1` of them. -/
theorem card_filter_dvd_le (i : ℕ) (j₀ α : ℤ) (L : ℕ) :
    (#((Ico j₀ (j₀ + L)).filter fun j => ((2 * i + 3 : ℕ) : ℤ) ∣ α + 2 * j) : ℝ) ≤
      L / (2 * i + 3) + 1 := by
  have h := card_le_div_add_one_of_dvd_sub (d := 2 * i + 3) (by omega) j₀ L
    (S := (Ico j₀ (j₀ + L)).filter fun j => ((2 * i + 3 : ℕ) : ℤ) ∣ α + 2 * j)
    (filter_subset _ _) ?_
  · simpa using h
  intro j hj j' hj'
  have h1 := (mem_filter.1 hj).2
  have h2 := (mem_filter.1 hj').2
  have h3 : ((2 * i + 3 : ℕ) : ℤ) ∣ 2 * (j - j') := by
    have := dvd_sub h1 h2
    rwa [show α + 2 * j - (α + 2 * j') = 2 * (j - j') by ring] at this
  have hcop : IsCoprime ((2 * i + 3 : ℕ) : ℤ) 2 := ⟨1, -((i : ℤ) + 1), by push_cast; ring⟩
  exact hcop.dvd_of_dvd_mul_left h3

/-- **Primitive points of a nonzero parity class** (Appendix I, (4)). For `L₀ ≤ L₂ ≤ L₁` and
`|β + 2k| ≤ K L₂` on the second parameter interval, at least `L₁ L₂ / 2` of the parameters
`(j, k)` give a coprime pair `(α + 2j, β + 2k)`. -/
theorem card_coprime_parity_ge {K : ℝ} (hK : 1 ≤ K) :
    ∃ L₀ : ℕ, ∀ L₁ L₂ : ℕ, L₀ ≤ L₂ → L₂ ≤ L₁ → ∀ j₀ k₀ α β : ℤ, (Odd α ∨ Odd β) →
      (∀ k ∈ Ico k₀ (k₀ + L₂), |((β + 2 * k : ℤ) : ℝ)| ≤ K * L₂) →
      (L₁ * L₂ : ℝ) / 2 ≤
        #((Ico j₀ (j₀ + L₁) ×ˢ Ico k₀ (k₀ + L₂)).filter
          fun jk : ℤ × ℤ => Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1) := by
  refine ⟨⌈72 * K + 8⌉₊, ?_⟩
  intro L₁ L₂ hL₀ hL₂₁ j₀ k₀ α β hodd hloc
  set I := Ico j₀ (j₀ + L₁) with hI
  set J := Ico k₀ (k₀ + L₂) with hJ
  set N := ⌊K * L₂⌋₊ with hN
  set A : ℕ → Finset ℤ := fun i => I.filter fun j => ((2 * i + 3 : ℕ) : ℤ) ∣ α + 2 * j
    with hA
  set B : ℕ → Finset ℤ := fun i => J.filter fun k => ((2 * i + 3 : ℕ) : ℤ) ∣ β + 2 * k
    with hB
  set Z := I ×ˢ J.filter fun k => β + 2 * k = 0 with hZ
  -- the noncoprime parameters are covered by the zero row and the odd-divisor boxes
  have hsub : (I ×ˢ J).filter (fun jk : ℤ × ℤ => ¬ Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1) ⊆
      Z ∪ (range N).biUnion fun i => A i ×ˢ B i := by
    rintro ⟨j, k⟩ h
    simp only [mem_filter, mem_product] at h
    obtain ⟨⟨hj, hk⟩, hg⟩ := h
    by_cases hn : β + 2 * k = 0
    · exact mem_union_left _ (mem_product.2 ⟨hj, mem_filter.2 ⟨hk, hn⟩⟩)
    apply mem_union_right
    set g := Int.gcd (α + 2 * j) (β + 2 * k) with hg_def
    have hgm : (g : ℤ) ∣ α + 2 * j := Int.gcd_dvd_left ..
    have hgn : (g : ℤ) ∣ β + 2 * k := Int.gcd_dvd_right ..
    have hg0 : g ≠ 0 := by
      intro h0
      exact hn (Int.gcd_eq_zero_iff.1 h0).2
    have hg2 : ¬ 2 ∣ g := by
      intro h2
      have h2' : (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast h2
      have hm2 := dvd_trans h2' hgm
      have hn2 := dvd_trans h2' hgn
      rcases hodd with ⟨a, ha⟩ | ⟨b, hb⟩ <;> omega
    have hgle : g ≤ (β + 2 * k).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.2 hn) (Int.natCast_dvd.1 hgn)
    have hgN : g ≤ N := by
      apply Nat.le_floor
      calc (g : ℝ) ≤ ((β + 2 * k).natAbs : ℝ) := by exact_mod_cast hgle
        _ = |((β + 2 * k : ℤ) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        _ ≤ K * L₂ := hloc k hk
    have hg3 : 2 * ((g - 3) / 2) + 3 = g := by omega
    rw [mem_biUnion]
    refine ⟨(g - 3) / 2, mem_range.2 (by omega), mem_product.2 ⟨mem_filter.2 ⟨hj, ?_⟩,
      mem_filter.2 ⟨hk, ?_⟩⟩⟩
    · rw [hg3]; exact hgm
    · rw [hg3]; exact hgn
  -- cardinalities
  have hIcard : #I = L₁ := by simp [hI]
  have hJcard : #J = L₂ := by simp [hJ]
  have hZcard : (#Z : ℝ) ≤ L₁ := by
    have h1 : #(J.filter fun k => β + 2 * k = 0) ≤ 1 := by
      apply card_le_one.2
      intro a ha b hb
      have := (mem_filter.1 ha).2
      have := (mem_filter.1 hb).2
      omega
    rw [hZ, card_product, hIcard]
    calc ((L₁ * #(J.filter fun k => β + 2 * k = 0) : ℕ) : ℝ) ≤ ((L₁ * 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left _ h1
      _ = L₁ := by simp
  have hbad : (#((I ×ˢ J).filter
      (fun jk : ℤ × ℤ => ¬ Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)) : ℝ) ≤
      L₁ + ∑ i ∈ range N, ((L₁ : ℝ) / (2 * i + 3) + 1) * ((L₂ : ℝ) / (2 * i + 3) + 1) := by
    have h1 := card_le_card hsub
    have h2 := card_union_le Z ((range N).biUnion fun i => A i ×ˢ B i)
    have h3 := card_biUnion_le (s := range N) (t := fun i => A i ×ˢ B i)
    have h4 : (#((I ×ˢ J).filter
        (fun jk : ℤ × ℤ => ¬ Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)) : ℝ) ≤
        #Z + ∑ i ∈ range N, (#(A i) : ℝ) * #(B i) := by
      have : #((I ×ˢ J).filter
          (fun jk : ℤ × ℤ => ¬ Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)) ≤
          #Z + ∑ i ∈ range N, #(A i) * #(B i) := by
        simp only [card_product] at h3
        omega
      exact_mod_cast this
    refine h4.trans (add_le_add hZcard (sum_le_sum fun i _ => ?_))
    have hAi : (#(A i) : ℝ) ≤ L₁ / (2 * i + 3) + 1 := by
      have := card_filter_dvd_le i j₀ α L₁
      simpa [hA, hI] using this
    have hBi : (#(B i) : ℝ) ≤ L₂ / (2 * i + 3) + 1 := by
      have := card_filter_dvd_le i k₀ β L₂
      simpa [hB, hJ] using this
    exact mul_le_mul hAi hBi (by positivity) (by positivity)
  have hsplit := card_filter_add_card_filter_not (s := I ×ˢ J)
    (fun jk : ℤ × ℤ => Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)
  rw [card_product, hIcard, hJcard] at hsplit
  have hsplit' : (#((I ×ˢ J).filter
      (fun jk : ℤ × ℤ => Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)) : ℝ) +
      #((I ×ˢ J).filter
        (fun jk : ℤ × ℤ => ¬ Int.gcd (α + 2 * jk.1) (β + 2 * jk.2) = 1)) = L₁ * L₂ := by
    exact_mod_cast hsplit
  -- the arithmetic
  set S1 := ∑ i ∈ range N, (1 : ℝ) / (2 * i + 3) ^ 2 with hS1
  set S := ∑ i ∈ range N, (1 : ℝ) / (2 * i + 3) with hS
  have hexpand : ∑ i ∈ range N, ((L₁ : ℝ) / (2 * i + 3) + 1) * ((L₂ : ℝ) / (2 * i + 3) + 1) =
      L₁ * L₂ * S1 + (L₁ + L₂) * S + N := by
    rw [hS1, hS, mul_sum, mul_sum, show (N : ℝ) = ∑ i ∈ range N, (1 : ℝ) by simp,
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hS1le : S1 ≤ 1 / 4 := by
    have := sum_inv_odd_sq_le N
    have : (0 : ℝ) ≤ 1 / (4 * (N + 1)) := by positivity
    linarith
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => by positivity
  have hS1_0 : 0 ≤ S1 := sum_nonneg fun i _ => by positivity
  have hCS : S ^ 2 ≤ N * S1 := by
    have := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1 : ℝ)) fun i => 1 / (2 * (i : ℝ) + 3)
    simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at this
    calc S ^ 2 ≤ N * ∑ i ∈ range N, (1 / (2 * (i : ℝ) + 3)) ^ 2 := this
      _ = N * S1 := by
        rw [hS1]
        congr 1
        refine sum_congr rfl fun i _ => ?_
        rw [div_pow, one_pow]
  have hNle : (N : ℝ) ≤ K * L₂ := Nat.floor_le (by positivity)
  have hL₂ : 72 * K + 8 ≤ (L₂ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL₀)
  have hL₂₁' : (L₂ : ℝ) ≤ L₁ := by exact_mod_cast hL₂₁
  have hSle : S ≤ L₂ / 16 := by
    have h1 : S ^ 2 ≤ (L₂ / 16) ^ 2 := by
      calc S ^ 2 ≤ N * S1 := hCS
        _ ≤ K * L₂ * (1 / 4) := mul_le_mul hNle hS1le hS1_0 (by positivity)
        _ ≤ (L₂ / 16) ^ 2 := by nlinarith
    nlinarith
  have e1 : (L₁ : ℝ) * L₂ * S1 ≤ L₁ * L₂ * (1 / 4) :=
    mul_le_mul_of_nonneg_left hS1le (by positivity)
  have e2 : ((L₁ : ℝ) + L₂) * S ≤ (2 * L₁) * (L₂ / 16) :=
    mul_le_mul (by linarith) hSle hS0 (by positivity)
  have e3 : (N : ℝ) ≤ K * L₁ := hNle.trans (mul_le_mul_of_nonneg_left hL₂₁' (by linarith))
  have e4 : (L₁ : ℝ) * (1 + K) ≤ L₁ * (L₂ / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hexpand] at hbad
  nlinarith

end Favard.Coverage
