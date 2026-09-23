import FavardLength.Fourier.Window.Bounds
import FavardLength.Statements
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A frequency window with small energy (P2)

We prove `WindowStatement` (manuscript, section "A frequency window with small energy").

Let `E ⊆ [0,1]` be a measurable set of slopes with terminal normalized energy
`normEnergy N t ≤ H`. Write `g_t(ξ) = ν̂_{N,t}(ξ)²`.

1. *Energy on low frequencies.* For `ξ ∈ (0, 4^n]` with `2 ≤ n` and `2n ≤ N`, the sinc argument
   `(4/3) 4^{-N} ξ` lies in `(0, 1]`, so `sinc² ≥ 1/2` and `g_t(ξ) ≤ 2 sinc²(…) g_t(ξ)`.
   Since the energy integrand is integrable, `∫ sinc² g_t ≤ 2πH`.
2. *Disjoint windows.* The windows `W_n = [4^n · 3/(8·4^m), 4^n]` with indices
   `n_k = m + 2 + k(m+1)`, `k < K := ⌊N / (4(m+1))⌋`, are pairwise disjoint and satisfy
   `2 n_k ≤ N`. Hence `∑_k ∫_{W_{n_k}} g_t ≤ 4πH` for `t ∈ E`, and by Tonelli
   `∑_k ∫_E ∫_{W_{n_k}} g_t ≤ 4πH |E|`.
3. *Pigeonhole.* Some `k` has `∫_E ∫_{W_{n_k}} g_t ≤ 4πH|E| / K`, and `N ≤ 8(m+1)K`.
4. *Rescaling.* Substituting `ξ = 4^n y` and using `(P₁P₂)² ≤ (9/4) ν̂_{N,t}(4^n y)²`
   (the tail factors have product at least `2/3`) gives the statement with `C = 72π`.

Working with disjoint windows (spaced `m + 1` apart) replaces the manuscript's overlap count;
the loss is only in the absolute constant.
-/

open MeasureTheory Set Real Finset
open scoped ENNReal

namespace Favard

namespace Window

/-- The frequency window `W_n = [4^n · 3/(8·4^m), 4^n]`: the image of `[3/(8·4^m), 1]` under
`y ↦ 4^n y`. -/
def win (m n : ℕ) : Set ℝ := Icc ((4 : ℝ) ^ n * (3 / 8 / 4 ^ m)) (4 ^ n * 1)

/-- The window indices `n_k = m + 2 + k (m + 1)`. -/
def idx (m k : ℕ) : ℕ := m + 2 + k * (m + 1)

lemma pos_of_mem_win {m n : ℕ} {ξ : ℝ} (h : ξ ∈ win m n) : 0 < ξ :=
  (by positivity : (0 : ℝ) < 4 ^ n * (3 / 8 / 4 ^ m)).trans_le h.1

/-- On a window `W_n` with `2 ≤ n` and `2n ≤ N`, the sinc factor of the terminal energy is at
least `1/2`, so `ν̂² ≤ 2 sinc² ν̂²`. -/
lemma ofReal_nuHat_sq_le {m n N : ℕ} (hn : 2 ≤ n) (hnN : 2 * n ≤ N) (t : ℝ) {ξ : ℝ}
    (hξ : ξ ∈ win m n) :
    ENNReal.ofReal (nuHat N t ξ ^ 2) ≤
      2 * ENNReal.ofReal (sinc (4 / 3 / 4 ^ N * ξ) ^ 2 * nuHat N t ξ ^ 2) := by
  have hξ0 := pos_of_mem_win hξ
  have hξ1 : ξ ≤ 4 ^ n := by simpa [win] using hξ.2
  have hx0 : 0 < 4 / 3 / 4 ^ N * ξ := by positivity
  have hx1 : 4 / 3 / 4 ^ N * ξ ≤ 1 := by
    have h4N : (4 : ℝ) ^ n * 4 ^ n ≤ 4 ^ N := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h16 : (16 : ℝ) ≤ 4 ^ n :=
      calc (16 : ℝ) = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h16 (by positivity : (0 : ℝ) ≤ 4 ^ n)]
  have hs := half_le_sinc_sq hx0 hx1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have := sq_nonneg (nuHat N t ξ)
  nlinarith

/-- Windows with indices `j < k` are disjoint: `n_k ≥ n_j + m + 1`, so
`4^{n_k} · 3/(8·4^m) ≥ (3/2) 4^{n_j} > 4^{n_j}`. -/
lemma disjoint_win {m j k : ℕ} (h : j < k) : Disjoint (win m (idx m j)) (win m (idx m k)) := by
  rw [Set.disjoint_left]
  intro ξ h1 h2
  have hle : idx m j + m + 1 ≤ idx m k := by
    unfold idx
    have : (j + 1) * (m + 1) ≤ k * (m + 1) := Nat.mul_le_mul_right _ h
    nlinarith
  set a := idx m j
  set b := idx m k
  have hb : (4 : ℝ) ^ a * 4 ^ m * 4 ≤ 4 ^ b := by
    rw [← pow_add, ← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h1' : ξ ≤ 4 ^ a := by simpa [win] using h1.2
  have h2' : (4 : ℝ) ^ b * (3 / 8 / 4 ^ m) ≤ ξ := h2.1
  have e : (4 : ℝ) ^ a * 4 ^ m * 4 * (3 / 8 / 4 ^ m) = 3 / 2 * 4 ^ a := by
    field_simp
    ring
  have hmono : (4 : ℝ) ^ a * 4 ^ m * 4 * (3 / 8 / 4 ^ m) ≤ 4 ^ b * (3 / 8 / 4 ^ m) :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  have : (0 : ℝ) < 4 ^ a := by positivity
  linarith

lemma pairwiseDisjoint_win (m K : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) fun k => win m (idx m k) := by
  intro j _ k _ hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact disjoint_win h
  · exact (disjoint_win h).symm

/-- The partial integral `t ↦ ∫_W ν̂_{N,t}²` is measurable. -/
lemma measurable_lintegral_win (N : ℕ) (W : Set ℝ) :
    Measurable fun t => ∫⁻ ξ in W, ENNReal.ofReal (nuHat N t ξ ^ 2) := by
  have hf : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (nuHat N p.1 p.2 ^ 2) :=
    ((continuous_nuHat N).pow 2).measurable.ennreal_ofReal
  exact hf.lintegral_prod_right'

/-- For a slope with terminal energy at most `H`, the masses of `ν̂²` on the disjoint windows add
up to at most `4πH`. -/
lemma sum_lintegral_win_le {m N K : ℕ} (hK : ∀ k < K, 2 * idx m k ≤ N) {t H : ℝ}
    (hE : normEnergy N t ≤ H) :
    ∑ k ∈ range K, ∫⁻ ξ in win m (idx m k), ENNReal.ofReal (nuHat N t ξ ^ 2) ≤
      2 * ENNReal.ofReal (2 * π * H) := by
  set h : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (sinc (4 / 3 / 4 ^ N * ξ) ^ 2 * nuHat N t ξ ^ 2)
  calc ∑ k ∈ range K, ∫⁻ ξ in win m (idx m k), ENNReal.ofReal (nuHat N t ξ ^ 2)
      ≤ ∑ k ∈ range K, ∫⁻ ξ in win m (idx m k), 2 * h ξ := by
        refine sum_le_sum fun k hk => setLIntegral_mono' measurableSet_Icc fun ξ hξ => ?_
        have hk' := Finset.mem_range.mp hk
        exact ofReal_nuHat_sq_le (by unfold idx; omega) (hK k hk') t hξ
    _ = 2 * ∫⁻ ξ in ⋃ k ∈ Finset.range K, win m (idx m k), h ξ := by
        rw [lintegral_biUnion_finset (pairwiseDisjoint_win m K) (fun k _ => measurableSet_Icc),
          Finset.mul_sum]
        refine sum_congr rfl fun k _ => ?_
        exact lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 2 * ∫⁻ ξ, h ξ := by gcongr; exact Measure.restrict_le_self
    _ ≤ 2 * ENNReal.ofReal (2 * π * H) := by gcongr; exact lintegral_energy_le hE

/-- Rescaling `ξ = 4^n y`: the window integral of `(P₁P₂)²` is controlled by the mass of
`ν̂_{N,t}²` on `W_n`. -/
lemma lintegral_lowProd_highProd_le {m n N : ℕ} (hmn : m ≤ n) (hnN : n < N) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
        ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2) ≤
      ENNReal.ofReal (9 / 4) * ∫⁻ ξ in win m n, ENNReal.ofReal (nuHat N t ξ ^ 2) := by
  have h38 : (3 / 8 / 4 ^ m : ℝ) ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    linarith
  have hsub : win m n = (fun y => (4 : ℝ) ^ n * y) '' Icc (3 / 8 / 4 ^ m) 1 :=
    (image_mul_left_Icc (by positivity) h38).symm
  rw [hsub, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (f' := fun _ => (4 : ℝ) ^ n)
    (fun y _ => by simpa using ((hasDerivAt_id y).const_mul ((4 : ℝ) ^ n)).hasDerivWithinAt)
    (mul_right_injective₀ (by positivity : (4 : ℝ) ^ n ≠ 0)).injOn,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
  have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hP := lowProd_mul_highProd_sq_le hmn hnN ht0 ht1 hy0 hy.2
  rw [abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n)]
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hP h4]

end Window

open Window in
/-- **Frequency window with small energy** (P2). -/
theorem window : WindowStatement := by
  refine ⟨72 * π, by positivity, ?_⟩
  intro H hH m N hN E hE hEm hEH
  -- the number of disjoint windows
  set K := N / (4 * (m + 1)) with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef, Nat.one_le_div_iff (by positivity)]
    omega
  have hKN : K * (4 * (m + 1)) ≤ N := Nat.div_mul_le_self N _
  have hNK : N < K * (4 * (m + 1)) + 4 * (m + 1) := Nat.lt_div_mul_add (by positivity)
  have hidx : ∀ k < K, 2 * idx m k ≤ N := by
    intro k hk
    have h1 : (k + 1) * (m + 1) ≤ K * (m + 1) := Nat.mul_le_mul_right _ hk
    unfold idx
    nlinarith
  -- pigeonhole over the windows
  set a : ℕ → ℝ≥0∞ := fun k =>
    ∫⁻ t in E, ∫⁻ ξ in win m (idx m k), ENNReal.ofReal (nuHat N t ξ ^ 2) with ha
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (range K) a (nonempty_range_iff.mpr (by omega))
  have hsum : ∑ j ∈ range K, a j ≤ 2 * ENNReal.ofReal (2 * π * H) * volume E := by
    simp only [ha]
    rw [← lintegral_finsetSum' _ fun j _ => (measurable_lintegral_win N _).aemeasurable]
    calc ∫⁻ t in E, ∑ j ∈ range K, ∫⁻ ξ in win m (idx m j), ENNReal.ofReal (nuHat N t ξ ^ 2)
        ≤ ∫⁻ _ in E, 2 * ENNReal.ofReal (2 * π * H) :=
          setLIntegral_mono' hEm fun t ht => sum_lintegral_win_le hidx (hEH t ht)
      _ = 2 * ENNReal.ofReal (2 * π * H) * volume E := setLIntegral_const E _
  have hcard : (K : ℝ≥0∞) * a k ≤ 2 * ENNReal.ofReal (2 * π * H) * volume E := by
    have := Finset.card_nsmul_le_sum (range K) a (a k) hmin
    rw [card_range, nsmul_eq_mul] at this
    exact this.trans hsum
  have hk' : k < K := Finset.mem_range.mp hk
  refine ⟨idx m k, by unfold idx; omega, hidx k hk', ?_⟩
  set n := idx m k with hn
  have hmn : m ≤ n := by rw [hn]; unfold idx; omega
  have hnN : n < N := by have := hidx k hk'; omega
  -- the per-slope rescaling bound
  calc ∫⁻ t in E, ∫⁻ y in Icc (3 / 8 / 4 ^ m : ℝ) 1,
          ENNReal.ofReal ((4 : ℝ) ^ n * (lowProd m t y * highProd m n t y) ^ 2)
      ≤ ∫⁻ t in E, ENNReal.ofReal (9 / 4) *
          ∫⁻ ξ in win m n, ENNReal.ofReal (nuHat N t ξ ^ 2) :=
        setLIntegral_mono' hEm fun t ht =>
          lintegral_lowProd_highProd_le hmn hnN (hE ht).1 (hE ht).2
    _ = ENNReal.ofReal (9 / 4) * a k := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (9 / 4) * (ENNReal.ofReal ((K : ℝ)⁻¹) *
          (ENNReal.ofReal 2 * ENNReal.ofReal (2 * π * H) * volume E)) := by
        gcongr
        have hK0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
        rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast (by omega : 0 < K)),
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat,
          ← ENNReal.inv_mul_cancel_left hK0 (ENNReal.natCast_ne_top K) (b := a k)]
        gcongr
    _ = ENNReal.ofReal (9 / 4 * ((K : ℝ)⁻¹ * (2 * (2 * π * H)))) * volume E := by
        have hKinv : (0 : ℝ) ≤ (K : ℝ)⁻¹ := by positivity
        conv_rhs => rw [ENNReal.ofReal_mul (p := 9 / 4) (by norm_num),
          ENNReal.ofReal_mul hKinv, ENNReal.ofReal_mul (p := 2) (by norm_num)]
        ring
    _ ≤ ENNReal.ofReal (72 * π * H * (m + 1) / N) * volume E := by
        gcongr
        have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hN8 : N ≤ 8 * (m + 1) * K := by nlinarith
        have hNr : (N : ℝ) ≤ 8 * (m + 1) * K := by exact_mod_cast hN8
        rw [show 9 / 4 * ((K : ℝ)⁻¹ * (2 * (2 * π * H))) = 9 * π * H / K by
          field_simp; ring, div_le_div_iff₀ hKpos hNpos]
        nlinarith [mul_le_mul_of_nonneg_left hNr (by positivity : (0 : ℝ) ≤ 9 * π * H)]

end Favard
