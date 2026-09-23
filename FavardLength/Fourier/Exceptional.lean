import FavardLength.Statements
import FavardLength.Fourier.Exceptional.Measurability
import FavardLength.Fourier.Exceptional.Threshold

/-!
# Exceptional directions in the normalized slope variable (J9)

We prove `WindowStatement → AnnularStatement → JointMomentStatement →
NormalizedExceptionalStatement`, following the manuscript's section "Consequence for exceptional
directions" in the integrated form of `PLAN.md` (no Markov selection of a subset).

Fix `s ∈ [1/4, 1/2)`, `H ≥ 2`, `N ≥ 1`, and let `E` be the set of slopes `t ∈ [0,1]` whose
normalized energies of generations `1, …, N` are at most `H`, `e = |E|`. Choose `L = 4^m` with
`A₀ H ≤ L ≤ max 1 (4 A₀ H)`, so `m + 1 = O(2 + log H)`.

* If `N < 4(m + 3)`, then `H³(2 + log H)/N` is bounded below and `e ≤ 1` is absorbed in the
  constant.
* Otherwise the window lemma gives `n` with `4^n ∫_E ∫ (P₁P₂)² ≤ C_W H (m+1) e / N`, the annular
  lemma gives `∫ P₂² ≥ c_a/M` for every `t ∈ E` (`M = 4^{n-m}`), and splitting according to
  `|P₁| ≥ a` or `|P₁| < a` together with the joint moment gives, for every `a > 0`,
  `c_a e ≤ C_W H (m+1) e/(L N a²) + A L^{3s/2} a^s`. Optimizing in `a` yields
  `e ≤ C (H (m+1) L² / N)^{s/2} ≤ C' (H³ (2 + log H)/N)^{s/2}`.
-/

open MeasureTheory Set Real

namespace Favard

namespace Exceptional

/-- The integrated splitting behind (J9): if the high-frequency mass is at least `c` for every
slope of `E`, then `c |E|` is bounded by the frequency-window integral (weighted by
`a⁻² 4^{-n}`) plus the joint negative moment (weighted by `a^s`). -/
lemma mul_volume_le_window_add_moment {s a : ℝ} (hs : 0 < s) (ha : 0 < a) {m n : ℕ}
    {E Y : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc 0 1) {c W J : ENNReal}
    (hc : ∀ t ∈ E, c ≤ ∫⁻ y in Y, ENNReal.ofReal (highProd m n t y ^ 2))
    (hW : ∫⁻ t in E, ∫⁻ y in Y,
      ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2) ≤ W)
    (hJ : ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in Y,
      ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2) ≤ J) :
    c * volume E ≤ ENNReal.ofReal ((a ^ 2 * 4 ^ n)⁻¹) * W + ENNReal.ofReal (a ^ s) * J := by
  have hmeas : Measurable (Function.uncurry fun t y =>
      ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2)) := by
    have h1 := continuous_lowProd m
    have h2 := continuous_highProd m n
    exact (ENNReal.continuous_ofReal.comp (by fun_prop)).measurable
  have hF : ∀ t, Measurable fun y =>
      ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2) :=
    fun t => hmeas.of_uncurry_left
  have hWmeas : Measurable fun t => ∫⁻ y in Y,
      ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2) :=
    hmeas.lintegral_prod_right
  have hin : ∀ t ∈ E, c ≤
      ENNReal.ofReal ((a ^ 2 * 4 ^ n)⁻¹) * (∫⁻ y in Y,
          ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2)) +
        ENNReal.ofReal (a ^ s) * ∫⁻ y in Y,
          ENNReal.ofReal |lowProd m t y| ^ (-s) * ENNReal.ofReal (highProd m n t y ^ 2) := by
    intro t ht
    refine (hc t ht).trans ((lintegral_mono fun y => ofReal_sq_le_split (κ := (4 : ℝ) ^ n) hs ha
      (by positivity) (lowProd m t y) (highProd m n t y)).trans ?_)
    rw [lintegral_add_left ((hF t).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc c * volume E = ∫⁻ _ in E, c := (setLIntegral_const _ _).symm
    _ ≤ _ := setLIntegral_mono' hE hin
    _ = _ := by
      rw [lintegral_add_left (hWmeas.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
      gcongr
      exact (lintegral_mono_set hEsub).trans hJ

end Exceptional

open Exceptional in
/-- **Exceptional directions** (J9), normalized form, from the frequency window (P2), the annular
lower bound (P3) and the joint negative moment (J1). -/
theorem normalizedExceptional_of (hW : WindowStatement) (hA : AnnularStatement)
    (hJ : JointMomentStatement) : NormalizedExceptionalStatement := by
  intro s hs1 hs2
  have hs : 0 < s := by linarith
  obtain ⟨CW, hCW, hWin⟩ := hW
  obtain ⟨A₀, ca, hA₀, hca, hAnn⟩ := hA
  obtain ⟨A, hA0, hJm⟩ := hJ s hs1 hs2
  set K : ℝ := 1 + 4 * A₀ with hK
  have hK1 : 1 ≤ K := by linarith
  set Cm : ℝ := 1 + Real.log K with hCm
  have hCm1 : 1 ≤ Cm := by have := Real.log_nonneg hK1; linarith
  set C₁ : ℝ := 2 * A / ca * (2 * CW * K ^ 2 * Cm / ca) ^ (s / 2) with hC₁
  set C₂ : ℝ := ((8 / (11 * Cm)) ^ (s / 2))⁻¹ with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁0, fun H hH N hN => ?_⟩
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set q : ℝ := 2 + Real.log H with hq
  have hq0 : 0 < q := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ H); linarith
  set Y : ℝ := H ^ 3 * q / N with hY
  have hY0 : 0 < Y := by positivity
  -- the scale `L = 4^m ≍ H`
  obtain ⟨m, hm1, hm2⟩ := exists_pow_four_between (A₀ * H)
  have hLK : (4 : ℝ) ^ m ≤ K * H := hm2.trans (max_le (by nlinarith) (by nlinarith))
  have hmq : (m : ℝ) + 1 ≤ Cm * q := natCast_add_one_le_of_pow_four_le hK1 (by linarith) hLK
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
        have hH3 : (8 : ℝ) ≤ H ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hH 3
          norm_num at this; linarith
        have hY8 : 8 / (11 * Cm) ≤ Y := by
          rw [hY, div_le_div_iff₀ (by positivity) hN0]
          nlinarith [mul_le_mul_of_nonneg_left hN' (by norm_num : (0 : ℝ) ≤ 8)]
        have h8 : (8 / (11 * Cm)) ^ (s / 2) ≤ Y ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hY8 (by positivity)
        have h8' : 0 < (8 / (11 * Cm)) ^ (s / 2) := by positivity
        calc (1 : ℝ) = C₂ * (8 / (11 * Cm)) ^ (s / 2) := by rw [hC₂, inv_mul_cancel₀ h8'.ne']
          _ ≤ C₂ * Y ^ (s / 2) := by gcongr
          _ ≤ max C₁ C₂ * Y ^ (s / 2) := by gcongr; exact le_max_right _ _
  -- main case: frequency window, annular lower bound, joint moment
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
  set D : ℝ := A * L ^ (3 * s / 2) with hD
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
  -- final bookkeeping: `L ≤ K H` and `m + 1 ≤ Cm (2 + log H)`
  have hL3 : L ^ (3 * s / 2) = (L ^ 3) ^ (s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have step1 : 2 * D / ca * (2 * P / ca) ^ (s / 2) =
      2 * A / ca * (L ^ 3 * (2 * P / ca)) ^ (s / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← hL3, hD]; ring
  have step2 : L ^ 3 * (2 * P / ca) ≤ 2 * CW * K ^ 2 * Cm / ca * Y := by
    have e1 : L ^ 3 * (2 * P / ca) = 2 * CW / ca * (L ^ 2 * H * (m + 1)) / N := by
      rw [hP]; field_simp
    have e2 : 2 * CW * K ^ 2 * Cm / ca * Y =
        2 * CW / ca * ((K * H) ^ 2 * H * (Cm * q)) / N := by
      rw [hY]; field_simp
    rw [e1, e2]
    gcongr
  have step3 : (L ^ 3 * (2 * P / ca)) ^ (s / 2) ≤
      (2 * CW * K ^ 2 * Cm / ca) ^ (s / 2) * Y ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity) hY0.le]
    exact Real.rpow_le_rpow (by positivity) step2 (by positivity)
  have hvC : v ≤ C₁ * Y ^ (s / 2) := by
    calc v ≤ _ := hmain
      _ = _ := step1
      _ ≤ 2 * A / ca * ((2 * CW * K ^ 2 * Cm / ca) ^ (s / 2) * Y ^ (s / 2)) := by gcongr
      _ = C₁ * Y ^ (s / 2) := by rw [hC₁]; ring
  rw [hVv]
  refine ENNReal.ofReal_le_ofReal (hvC.trans ?_)
  gcongr
  exact le_max_left _ _

end Favard
