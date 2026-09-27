import FavardLength.Beyond.Exclusion.Density
import FavardLength.Beyond.Exclusion.Statements

/-!
# The flat block from the martingale cell selection (exclusion part (d2))

We derive `Favard.Exclusion.FlatBlockStatement` from the martingale cell selection
`Favard.Exclusion.CellSelectionStatement` by rescaling and cropping whole tail copies
(Appendix E §§1–2 of `references/beyond/favard-beyond-quarter-complete.md`).

Apply the selection with block length `r + L`. It gives a level-`j` cell
`I = [A, A + ρ4^{-j}]`, `A = cellLeft j i`, `ρ = 8/3`, with mean `a` and small relative variance
at level `j + r + L`. Rescale at level `j₁ = j + r`: `F(x) = f_{N,t}(A + x/4^{j₁})` on `[0, T]`,
`T = ρ4^r`, so that `F(x) = ∑_u f_{n,t}(x - β_u)` with `n = N - j₁` and
`β_u = 4^{j₁}(c_u(t) - A)` (`Favard.Exclusion.tailDensity_rescale`). Keeping the copies with
`β_u ∈ [ρ/2, T - ρ/2]` gives `g = ∑_{kept} f_{n,t}(· - β_u)` with

* `g = F` on the middle half `[T/4, 3T/4]`, since a copy meeting it has `|x - β_u| ≤ ρ/2`;
* `m = #kept = ∑_{kept} ∫_0^T f_{n,t}(· - β_u) ≤ ∫_0^T F = 4^{j₁} ∫_I f_{N,t} = aT`;
* the level-`(j + r + L)` sub-cells of `I` become the cells `[ch, (c+1)h]`, `h = T/4^{r+L}`,
  with `∫_{ch}^{(c+1)h} F - ah = 4^{j₁}(∫_{sub} f_{N,t} - a|sub|)`, so the middle-half flatness
  follows from the variance bound of the selection.

## Main results

* `Favard.Exclusion.integral_tailDensity_comp_div`: change of variables for the rescaled density.
* `Favard.Exclusion.integral_tailDensity_sub_eq_one`: a whole copy inside `[0, T]` has mass one.
* `Favard.Exclusion.flatBlock_of`: `CellSelectionStatement → FlatBlockStatement`.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

open Bridge

/-- **Rescaled interval integrals**:
`∫_p^q f_{N,t}(A + x/4^j) dx = 4^j ∫_{A + p/4^j}^{A + q/4^j} f_{N,t}`. -/
lemma integral_tailDensity_comp_div (N j : ℕ) (t A p q : ℝ) :
    ∫ x in p..q, tailDensity N t (A + x / 4 ^ j) =
      4 ^ j * ∫ y in A + p / 4 ^ j..A + q / 4 ^ j, tailDensity N t y := by
  have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_div (fun z => tailDensity N t (A + z)) h4,
    intervalIntegral.integral_comp_add_left (tailDensity N t), smul_eq_mul]

/-- A whole copy `f_{n,t}(· - β)` with `[β - ρ/2, β + ρ/2] ⊆ [0, T]` has mass one on `[0, T]`. -/
lemma integral_tailDensity_sub_eq_one {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) {T β : ℝ}
    (hβ₁ : 4 / 3 ≤ β) (hβ₂ : β ≤ T - 4 / 3) :
    ∫ x in (0 : ℝ)..T, tailDensity n t (x - β) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right (tailDensity n t), zero_sub,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero, integral_tailDensity]
  intro x hx
  refine tailDensity_eq_zero ht n ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl (by linarith))

/-- A copy `f_{n,t}(· - β)` with `β ∉ [ρ/2, T - ρ/2]` vanishes on the middle half
`[T/4, 3T/4]` once `T ≥ 32/3`. -/
lemma tailDensity_sub_eq_zero_of_mem_middle {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) {T β x : ℝ}
    (hT : 32 / 3 ≤ T) (hβ : β ∉ Icc (4 / 3) (T - 4 / 3)) (hx : x ∈ Icc (T / 4) (3 * T / 4)) :
    tailDensity n t (x - β) = 0 := by
  refine tailDensity_eq_zero ht n ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hβ
  rcases hβ with hβ | hβ
  · exact lt_abs.mpr (Or.inl (by linarith [hx.1]))
  · exact lt_abs.mpr (Or.inr (by linarith [hx.2]))

/-- **Flat block from the cell selection** (Appendix E §§1–2): rescaling the selected cell at
level `j + r` and keeping the whole tail copies inside `[0, T]`, `T = ρ4^r`, proves
`FlatBlockStatement` from `CellSelectionStatement` (applied with block length `r + L`). -/
theorem flatBlock_of (h : CellSelectionStatement) : FlatBlockStatement := by
  intro H t N r L hH ht hr hN hE
  have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨j, i, a, hjN, -, hmass, ha, haH, hvar⟩ := h H t N (r + L) hH ht (by omega) hN hE
  have hj₁N : j + r ≤ N := by omega
  set n := N - (j + r)
  set T : ℝ := 8 / 3 * 4 ^ r with hT
  set A := cellLeft j i with hA
  set bu : SqCode (j + r) → ℝ := fun u => 4 ^ (j + r) * (code t u - A)
  set S : Finset (SqCode (j + r)) := Finset.univ.filter fun u => bu u ∈ Icc (4 / 3) (T - 4 / 3)
  set β : Fin S.card → ℝ := fun k => bu (S.equivFin.symm k)
  have hsumS : ∀ φ : ℝ → ℝ, ∑ k : Fin S.card, φ (β k) = ∑ u ∈ S, φ (bu u) := by
    intro φ
    rw [← Finset.sum_coe_sort S (fun u => φ (bu u))]
    exact Equiv.sum_comp S.equivFin.symm (fun u : S => φ (bu u))
  have hF : ∀ x, tailDensity N t (A + x / 4 ^ (j + r)) = ∑ u, tailDensity n t (x - bu u) :=
    fun x => tailDensity_rescale hj₁N t A x
  have h4r : (16 : ℝ) ≤ 4 ^ r := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hT32 : 32 / 3 ≤ T := by rw [hT]; linarith
  have hT0 : 0 ≤ T := by linarith
  -- the cropped copies agree with the rescaled density on the middle half
  have hgF : ∀ x ∈ Icc (T / 4) (3 * T / 4),
      copySum n t β x = tailDensity N t (A + x / 4 ^ (j + r)) := by
    intro x hx
    rw [hF, copySum, hsumS (fun b => tailDensity n t (x - b))]
    refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
    have hu' : bu u ∉ Icc (4 / 3) (T - 4 / 3) := fun hmem =>
      hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
    exact tailDensity_sub_eq_zero_of_mem_middle htabs n hT32 hu' hx
  -- the mass of the rescaled density on `[0, T]`
  have hcellT : A + T / 4 ^ (j + r) = cellLeft j (i + 1) := by
    simp only [hA, hT, cellLeft]
    push_cast
    rw [pow_add]
    field_simp
    ring
  have hFint : ∫ x in (0 : ℝ)..T, tailDensity N t (A + x / 4 ^ (j + r)) = a * T := by
    rw [integral_tailDensity_comp_div, zero_div, add_zero, hcellT, hmass, hT, pow_add]
    field_simp
  have hm : (S.card : ℝ) ≤ a * T := by
    calc (S.card : ℝ) = ∑ u ∈ S, ∫ x in (0 : ℝ)..T, tailDensity n t (x - bu u) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          refine Finset.sum_congr rfl fun u hu => ?_
          have hu' := (Finset.mem_filter.mp hu).2
          exact (integral_tailDensity_sub_eq_one htabs n hu'.1 hu'.2).symm
      _ ≤ ∑ u, ∫ x in (0 : ℝ)..T, tailDensity n t (x - bu u) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ =>
            intervalIntegral.integral_nonneg hT0 fun x _ => tailDensity_nonneg n t _
      _ = ∫ x in (0 : ℝ)..T, tailDensity N t (A + x / 4 ^ (j + r)) := by
          rw [← intervalIntegral.integral_finsetSum fun u _ =>
            ((integrable_tailDensity n t).comp_sub_right (bu u)).intervalIntegrable]
          simp_rw [hF]
      _ = a * T := hFint
  refine ⟨n, S.card, β, a, by omega, ha, haH, hm, ?_⟩
  -- flatness on the middle half
  unfold MiddleFlat
  set hh : ℝ := T / 4 ^ (r + L) with hhh
  have hK : (4 : ℝ) ^ (r + L) = 4 ^ (r + L - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hKN : 4 ^ (r + L) = 4 ^ (r + L - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hh0 : 0 ≤ hh := by positivity
  have hq : (4 : ℝ) ^ (r + L - 1) * hh = T / 4 := by
    rw [hhh, hK]
    field_simp
  have hsub : ∀ c : ℕ, cellLeft (j + (r + L)) (4 ^ (r + L) * i + c) =
      A + c * hh / 4 ^ (j + r) := by
    intro c
    simp only [hA, hhh, hT, cellLeft]
    push_cast
    simp only [pow_add]
    field_simp
    ring
  have hsub' : ∀ c : ℕ, cellLeft (j + (r + L)) (4 ^ (r + L) * i + c + 1) =
      A + (c + 1) * hh / 4 ^ (j + r) := by
    intro c
    simp only [hA, hhh, hT, cellLeft]
    push_cast
    simp only [pow_add]
    field_simp
    ring
  have hcell : ∀ c : ℕ,
      (∫ x in (c : ℝ) * hh..((c : ℝ) + 1) * hh, tailDensity N t (A + x / 4 ^ (j + r))) -
          a * hh =
        4 ^ (j + r) * ((∫ y in cellLeft (j + (r + L)) (4 ^ (r + L) * i + c)..
          cellLeft (j + (r + L)) (4 ^ (r + L) * i + c + 1), tailDensity N t y) -
            a * (8 / 3 / 4 ^ (j + (r + L)))) := by
    intro c
    rw [integral_tailDensity_comp_div, hsub, hsub', hhh, hT]
    simp only [pow_add]
    field_simp
  calc ∑ c ∈ Finset.Ico (4 ^ (r + L - 1) : ℕ) (3 * 4 ^ (r + L - 1)),
        ((∫ x in (c : ℝ) * hh..((c : ℝ) + 1) * hh, copySum n t β x) - a * hh) ^ 2
      = ∑ c ∈ Finset.Ico (4 ^ (r + L - 1) : ℕ) (3 * 4 ^ (r + L - 1)),
          ((∫ x in (c : ℝ) * hh..((c : ℝ) + 1) * hh, tailDensity N t (A + x / 4 ^ (j + r))) -
            a * hh) ^ 2 := by
        refine Finset.sum_congr rfl fun c hc => ?_
        obtain ⟨hc₁, hc₂⟩ := Finset.mem_Ico.mp hc
        have hc₁' : (4 : ℝ) ^ (r + L - 1) ≤ c := by exact_mod_cast hc₁
        have hc₂' : (c : ℝ) + 1 ≤ 3 * 4 ^ (r + L - 1) := by exact_mod_cast hc₂
        have hle : (c : ℝ) * hh ≤ ((c : ℝ) + 1) * hh := by nlinarith
        rw [intervalIntegral.integral_congr fun x hx => hgF x ?_]
        rw [uIcc_of_le hle] at hx
        constructor
        · nlinarith [hx.1, mul_le_mul_of_nonneg_right hc₁' hh0]
        · nlinarith [hx.2, mul_le_mul_of_nonneg_right hc₂' hh0]
    _ ≤ ∑ c ∈ Finset.range (4 ^ (r + L)),
          ((∫ x in (c : ℝ) * hh..((c : ℝ) + 1) * hh, tailDensity N t (A + x / 4 ^ (j + r))) -
            a * hh) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) fun c _ _ => sq_nonneg _
        rw [Finset.mem_range]
        rw [Finset.mem_Ico] at hc
        omega
    _ = (4 ^ (j + r)) ^ 2 * ∑ c ∈ Finset.range (4 ^ (r + L)),
          ((∫ y in cellLeft (j + (r + L)) (4 ^ (r + L) * i + c)..
            cellLeft (j + (r + L)) (4 ^ (r + L) * i + c + 1), tailDensity N t y) -
              a * (8 / 3 / 4 ^ (j + (r + L)))) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hcell]
        ring
    _ ≤ (4 ^ (j + r)) ^ 2 * (512 / 3 * H * ((r + L : ℕ) : ℝ) / N * a ^ 2 * (8 / 3 / 4 ^ j) *
          (8 / 3 / 4 ^ (j + (r + L)))) := by gcongr
    _ = 512 / 3 * H * (r + L) / N * a ^ 2 * T * hh := by
        rw [hhh, hT]
        push_cast
        simp only [pow_add]
        field_simp

end Favard.Exclusion
