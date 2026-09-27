import FavardLength.Beyond.Statements
import FavardLength.Fourier.Exceptional

/-!
# Improved exceptional directions (beyond note, Appendix B.2 (8))

We prove `WindowStatement → AnnularStatement → JointMomentImprovedStatement s β →
ExceptionalImprovedStatement s β` for `1/4 ≤ s < 1/2` and `0 < β < 3s/2`. The proof is that of
`Favard.normalizedExceptional_of` (J9) with the improved joint moment: the prefactor `L^{3s/2}`
of the joint negative moment becomes `L^{2s-β}`.

Fix `H ≥ 2`, `N ≥ 1`, let `E` be the set of slopes `t ∈ [0,1]` whose normalized energies of
generations `1, …, N` are at most `H`, `e = |E|`, and put `κ = 4 - 2β/s`, so `κ > 1`. Choose
`L = 4^m` with `A₀ H ≤ L ≤ max 1 (4 A₀ H)`, so `m + 1 = O(2 + log H)`.

* If `N < 4(m + 3)`, then `H^κ (2 + log H)/N` is bounded below and `e ≤ 1` is absorbed in the
  constant.
* Otherwise the window lemma, the annular lemma and the improved joint moment give, for every
  `a > 0`, `c_a e ≤ C_W H (m+1) e/(L N a²) + A L^{2s-β} a^s`. Optimizing in `a`
  (`a^s = c_a e/(2 A L^{2s-β})`) yields
  `e ≤ C (H (m+1) L^{κ-1} / N)^{s/2} ≤ C' (H^κ (2 + log H)/N)^{s/2}`, using `L^{2s-β} =
  (L^κ)^{s/2}` and `κ - 1 = 3 - 2β/s > 0`.
-/

open MeasureTheory Set Real

namespace Favard

open Exceptional in
/-- **Improved exceptional directions** (beyond note, Appendix B.2 (8)), normalized form, from
the frequency window (P2), the annular lower bound (P3) and the improved joint negative moment
(beyond note, Appendix B.2 (7)). -/
theorem exceptionalImproved_of (hW : WindowStatement) (hA : AnnularStatement) {s β : ℝ}
    (hs1 : 1 / 4 ≤ s) (hs2 : s < 1 / 2) (hβ0 : 0 < β) (hβ : β < 3 * s / 2)
    (hJ : JointMomentImprovedStatement s β) : ExceptionalImprovedStatement s β := by
  have hs : 0 < s := by linarith
  obtain ⟨CW, hCW, hWin⟩ := hW
  obtain ⟨A₀, ca, hA₀, hca, hAnn⟩ := hA
  obtain ⟨A, hA0, hJm⟩ := hJ
  set κ : ℝ := 4 - 2 * β / s with hκ
  have hκ1 : 1 < κ := by
    have : 2 * β / s < 3 := by rw [div_lt_iff₀ hs]; linarith
    linarith
  set K : ℝ := 1 + 4 * A₀ with hK
  have hK1 : 1 ≤ K := by linarith
  set Cm : ℝ := 1 + Real.log K with hCm
  have hCm1 : 1 ≤ Cm := by have := Real.log_nonneg hK1; linarith
  set C₁ : ℝ := 2 * A / ca * (2 * CW * K ^ (κ - 1) * Cm / ca) ^ (s / 2) with hC₁
  set C₂ : ℝ := ((1 / (11 * Cm)) ^ (s / 2))⁻¹ with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁0, fun H hH N hN => ?_⟩
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set q : ℝ := 2 + Real.log H with hq
  have hq0 : 0 < q := by have := Real.log_nonneg hH1; linarith
  set Y : ℝ := H ^ κ * q / N with hY
  have hY0 : 0 < Y := by positivity
  -- the scale `L = 4^m ≍ H`
  obtain ⟨m, hm1, hm2⟩ := exists_pow_four_between (A₀ * H)
  have hLK : (4 : ℝ) ^ m ≤ K * H := hm2.trans (max_le (by nlinarith) (by nlinarith))
  have hmq : (m : ℝ) + 1 ≤ Cm * q := natCast_add_one_le_of_pow_four_le hK1 hH1 hLK
  set E := {t ∈ Icc (0 : ℝ) 1 | ∀ r : ℕ, 1 ≤ r → r ≤ N → normEnergy r t ≤ H} with hE
  have hEmeas : MeasurableSet E := measurableSet_lowEnergy H N
  have hEsub : E ⊆ Icc 0 1 := fun t ht => ht.1
  have hE1 : volume E ≤ 1 := (measure_mono hEsub).trans (by simp [Real.volume_Icc])
  have hEtop : volume E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hE1
  by_cases hNm : 4 * (m + 3) ≤ N
  swap
  · -- small depths: the right side is at least one
    calc volume E ≤ 1 := hE1
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max C₁ C₂ * Y ^ (s / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hN' : (N : ℝ) ≤ 11 * (Cm * q) := by
          have : (N : ℝ) ≤ 4 * m + 11 := by exact_mod_cast (by omega : N ≤ 4 * m + 11)
          nlinarith
        have hHκ : 1 ≤ H ^ κ := Real.one_le_rpow hH1 (by linarith)
        have hY1 : 1 / (11 * Cm) ≤ Y := by
          rw [hY, div_le_div_iff₀ (by positivity) hN0]
          nlinarith [mul_le_mul_of_nonneg_right hHκ hq0.le]
        have h1 : (1 / (11 * Cm)) ^ (s / 2) ≤ Y ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hY1 (by positivity)
        have h1' : 0 < (1 / (11 * Cm)) ^ (s / 2) := by positivity
        calc (1 : ℝ) = C₂ * (1 / (11 * Cm)) ^ (s / 2) := by rw [hC₂, inv_mul_cancel₀ h1'.ne']
          _ ≤ C₂ * Y ^ (s / 2) := by gcongr
          _ ≤ max C₁ C₂ * Y ^ (s / 2) := by gcongr; exact le_max_right _ _
  -- main case: frequency window, annular lower bound, improved joint moment
  obtain ⟨n, hmn, hnN, hWn⟩ :=
    hWin H hH0 m N hNm E hEsub hEmeas (fun t ht => ht.2 N hN le_rfl)
  have hmn' : m < n := by omega
  have hAnn' : ∀ t ∈ E, ENNReal.ofReal (ca / 4 ^ (n - m)) ≤
      ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1, ENNReal.ofReal (highProd m n t y ^ 2) :=
    fun t ht => hAnn H hH0 m n hmn' hm1 t ht.1 (ht.2 (n - m) (by omega) (by omega))
  have hJ' := hJm m n hmn'
  rcases eq_or_ne (volume E) 0 with h0 | h0
  · rw [h0]; simp
  set v := (volume E).toReal with hv
  have hVv : volume E = ENNReal.ofReal v := (ENNReal.ofReal_toReal hEtop).symm
  have hv0 : 0 < v := ENNReal.toReal_pos h0 hEtop
  set L : ℝ := (4 : ℝ) ^ m with hL
  set M : ℝ := (4 : ℝ) ^ (n - m) with hM
  have hL0 : 0 < L := by positivity
  have hM0 : 0 < M := by positivity
  have hML : (4 : ℝ) ^ n = M * L := by rw [hM, hL, ← pow_add, Nat.sub_add_cancel hmn'.le]
  set P : ℝ := CW * H * (m + 1) / (L * N) with hP
  set D : ℝ := A * L ^ (2 * s - β) with hD
  have key : ∀ a : ℝ, 0 < a → ca * v ≤ P * v / a ^ 2 + D * a ^ s := by
    intro a ha
    have hE := mul_volume_le_window_add_moment hs ha hEmeas hEsub hAnn' hWn hJ'
    rw [hVv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity), hML] at hE
    convert mul_le_mul_of_nonneg_right hE hM0.le using 1
    · field_simp
    · rw [hP, hD]; field_simp
  have hmain := le_of_forall_threshold hca hv0 (by positivity) hs key
  -- final bookkeeping: `L^{2s-β} = (L^κ)^{s/2}`, `L ≤ K H`, `m + 1 ≤ Cm (2 + log H)`
  have hLκ : L ^ (2 * s - β) = (L ^ κ) ^ (s / 2) := by
    rw [← Real.rpow_mul hL0.le]; congr 1; rw [hκ]; field_simp; ring
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have step1 : 2 * D / ca * (2 * P / ca) ^ (s / 2) =
      2 * A / ca * (L ^ κ * (2 * P / ca)) ^ (s / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← hLκ, hD]; ring
  have step2 : L ^ κ * (2 * P / ca) ≤ 2 * CW * K ^ (κ - 1) * Cm / ca * Y := by
    have hLκ' : L ^ κ = L ^ (κ - 1) * L := by
      rw [← Real.rpow_add_one hL0.ne']; ring_nf
    have hHκ : H ^ κ = H ^ (κ - 1) * H := by
      rw [← Real.rpow_add_one hH0.ne']; ring_nf
    have e1 : L ^ κ * (2 * P / ca) = 2 * CW / ca * (L ^ (κ - 1) * H * (m + 1)) / N := by
      rw [hP, hLκ']; field_simp
    have e2 : 2 * CW * K ^ (κ - 1) * Cm / ca * Y =
        2 * CW / ca * ((K * H) ^ (κ - 1) * H * (Cm * q)) / N := by
      rw [hY, hHκ, Real.mul_rpow (by positivity) hH0.le]; field_simp
    rw [e1, e2]
    have hLKκ : L ^ (κ - 1) ≤ (K * H) ^ (κ - 1) :=
      Real.rpow_le_rpow hL0.le hLK (by linarith)
    gcongr
  have step3 : (L ^ κ * (2 * P / ca)) ^ (s / 2) ≤
      (2 * CW * K ^ (κ - 1) * Cm / ca) ^ (s / 2) * Y ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity) hY0.le]
    exact Real.rpow_le_rpow (by positivity) step2 (by positivity)
  have hvC : v ≤ C₁ * Y ^ (s / 2) := by
    calc v ≤ _ := hmain
      _ = _ := step1
      _ ≤ 2 * A / ca * ((2 * CW * K ^ (κ - 1) * Cm / ca) ^ (s / 2) * Y ^ (s / 2)) := by
        gcongr
      _ = C₁ * Y ^ (s / 2) := by rw [hC₁]; ring
  rw [hVv]
  refine ENNReal.ofReal_le_ofReal (hvC.trans ?_)
  gcongr
  exact le_max_left _ _

end Favard
