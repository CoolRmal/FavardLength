import FavardLength.Beyond.Exclusion.Statements
import FavardLength.Beyond.Exclusion.Parameters

/-!
# Smooth-window exclusion from its sub-contracts

We prove `Favard.exclusion_of`: the sub-contracts of `FavardLength/Beyond/Exclusion/Statements.lean`
imply `ExclusionStatement γ ε` for all `0 < γ < 2` and `0 < ε < 1/2` (beyond note §2; Appendix G
§§4–5, 8; Appendix H §4).

Fix the Taylor order `J ≥ 10` with `ε (J - 5) ≥ 2 - γ`. For `H ≥ 1`, `B ≥ 2`,
`ℓ = log(2 + HB)`, choose the window scale `R = 4^r ∈ (x₀, 4x₀]`, `x₀ = κ⁴ H B^ε ℓ²`, the
averaging resolution `4^L > Λ (2 + HB)^{38}`, and the harmonic budget
`K = ⌈6 (128κ⁴)² H⁴ B^{2ε} ℓ⁴⌉`; the exceptional set is `X_{B,γ,K}`. If a pair outside `X` had
`normEnergy N t ≤ H`, the flat block (d) gives `m` copies, the window bounds (e) give
`W₂ ≥ m/16`, the positive-weight lemma (c) gives a harmonic `k < 6m² ≤ K`, and (a), (b) give
`|ψ_{n,t}(ξ_k)| ≥ c B^{γ-2}/m⁴` together with the relative moment bounds. The window chain then
bounds the main term `|ψ| √m/8` by four error terms, each at most `|ψ| √m/64` by the choice of
`κ`, `Λ`, the depth constant, and the radius constant — a contradiction.
-/

open MeasureTheory Set Real
open scoped Nat

namespace Favard

open Exclusion

/-- **The pointwise contradiction** (Appendix G §§4–5, H §4): for one odd pair outside the
exceptional set and one slope in its neighbourhood, a terminal energy at most `H` is impossible.
The constants are those chosen in `Favard.exclusion_of`. -/
lemma Exclusion.exclusion_pointwise (hbound : ComplementaryBoundStatement)
    (hharm : HarmonicStatement) (hflat : FlatBlockStatement)
    {γ ε c₀ c₁ CE Cχ Csum cψ δ₁ δ₅ κ Λ CrL CN crad H B Z ℓ x₀ : ℝ} {Cm : ℕ → ℝ}
    {J a₀ r L K : ℕ}
    (hrel : ∀ (p q k n : ℕ) (t : ℝ), Odd p → Odd q → IsFourPowOdd k → t ∈ Icc (0 : ℝ) 1 →
      4 * |t - ((q : ℝ) - p) / ((p : ℝ) + q)| * (((p : ℝ) + q) * k / 8) *
          Real.log (2 + ((p : ℝ) + q) * k) ≤ c₀ →
      8 / 3 / 4 ^ n * (((p : ℝ) + q) * k / 8) ≤ 1 / 4 →
      c₁ * |cosProd n ((p : ℝ) * k) * cosProd n ((q : ℝ) * k)| ≤
          |tailFT n t (((p : ℝ) + q) * k / 8)| ∧
        ∀ j : ℕ, ‖tailMoment n t j (((p : ℝ) + q) * k / 8)‖ ≤
          Cm j * Real.log (2 + ((p : ℝ) + q) * k) ^ j * |tailFT n t (((p : ℝ) + q) * k / 8)|)
    (hwin : ∀ (n L m : ℕ) (t T α e ξ : ℝ) (β : Fin m → ℝ),
      t ∈ Icc (0 : ℝ) 1 → 64 / 3 ≤ T → 2 ≤ L → 0 ≤ α → 0 ≤ e → e ≤ 1 → 1 / 4 ≤ ξ →
      MiddleFlat (copySum n t β) T α e L →
        α * T * (1 / 8 - √e) ≤ ∑ i, cutoff (β i / T) ^ 2 ∧
        ‖expandedWindow J n t T ξ β‖ ≤
          CE * m / T ^ (J + 1) + CE * α * T * (√e + T / 4 ^ L * ξ + 1 / (T * ξ) ^ J))
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hε0 : 0 < ε) (hε : ε < 1 / 2) (hJ10 : 10 ≤ J)
    (hJε : 2 - γ ≤ ε * ((J : ℝ) - 5)) (hc₁ : 0 < c₁) (hCm : ∀ j, 0 ≤ Cm j)
    (hCE : 0 < CE) (hCχ : 0 < Cχ) (hχ : ∀ j ≤ J, ∀ x, |iteratedDeriv j cutoff x| ≤ Cχ)
    (hCsum : Csum = ∑ j ∈ Finset.range J, Cm (j + 1)) (hcψ : cψ = c₁ / (9 * π ^ 2))
    (hδ₁ : δ₁ = cψ / (1088 * CE)) (hδ₅ : δ₅ = 1 / (64 * (Csum * Cχ + 1)))
    (hκ1 : 1 ≤ κ) (hκY : 12 ^ 5 * 4 ^ J / δ₁ ≤ κ) (hκℓ : 12 * 200018 ^ 2 / δ₅ ^ 2 ≤ κ)
    (hΛδ : 4 * (128 * κ ^ 4) ^ 7 / δ₁ ≤ Λ) (hCrL : 0 < CrL)
    (ha₀ : 16 * 128 ^ 2 * κ ^ 8 ≤ 4 ^ a₀) (hCN1 : 256 * (512 / 3) * CrL ≤ CN)
    (hCN2 : 2 * ((a₀ : ℝ) + 11 + CrL) ≤ CN)
    (hCN3 : (128 * κ ^ 4) ^ 9 * (512 / 3) * CrL / δ₁ ^ 2 ≤ CN)
    (hcrad : crad = c₀ / (6 * 128 ^ 2 * 200018 * κ ^ 9))
    (hH : 1 ≤ H) (hB : 2 ≤ B) (hZ : Z = 2 + H * B) (hℓ : ℓ = Real.log Z)
    (hx₀ : x₀ = κ ^ 4 * H * B ^ ε * ℓ ^ 2) (hr1 : x₀ < 4 ^ r) (hr2 : (4 : ℝ) ^ r ≤ 4 * x₀)
    (hr2' : 2 ≤ r) (hL1 : Λ * Z ^ 38 < 4 ^ L) (hrL : (r : ℝ) + L ≤ CrL * ℓ)
    (hKge : 6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 ≤ K)
    {p q N : ℕ} {t : ℝ} (hp : Odd p) (hq : Odd q) (hpq : p ≤ q) (hqB : (q : ℝ) ≤ B)
    (hX : (p, q) ∉ exceptionalSet B γ K)
    (hN : CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) ≤ N) (ht : t ∈ Icc (0 : ℝ) 1)
    (htt₀ : |t - ((q : ℝ) - p) / ((q : ℝ) + p)| ≤ crad / (H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5))
    (hle : normEnergy N t ≤ H) : False := by
  -- the scales attached to `H` and `B`
  have hB1 : 1 ≤ B := by linarith only [hB]
  have hHB : 2 ≤ H * B := by
    have := mul_le_mul hH hB (by norm_num) (by linarith only [hH])
    linarith only [this]
  have hZ4 : 4 ≤ Z := by rw [hZ]; linarith only [hHB]
  have hZ0 : 0 < Z := by linarith only [hZ4]
  have hZ1 : 1 ≤ Z := by linarith only [hZ4]
  have hℓ1 : 1 ≤ ℓ := hℓ ▸ one_le_log_of_four_le hZ4
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hℓZ : ℓ ≤ Z := hℓ ▸ log_le_self' hZ0
  have hHZ : H ≤ Z := by
    have := le_mul_of_one_le_right (by linarith only [hH] : (0 : ℝ) ≤ H) hB1
    rw [hZ]; linarith only [this]
  have hBZ : B ≤ Z := by
    have := le_mul_of_one_le_left (by linarith only [hB1] : (0 : ℝ) ≤ B) hH
    rw [hZ]; linarith only [this]
  have hBε1 : 1 ≤ B ^ ε := Real.one_le_rpow hB1 hε0.le
  have hBεB : B ^ ε ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (show ε ≤ 1 by linarith only [hε])
  have hBε2 : (B ^ ε) ^ 2 ≤ B := by
    rw [← Real.rpow_mul_natCast (by linarith only [hB1])]
    simpa using Real.rpow_le_rpow_of_exponent_le hB1
      (show ε * (2 : ℕ) ≤ 1 by push_cast; linarith only [hε])
  have hκ0 : 0 < κ := by linarith only [hκ1]
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁, hcψ]; positivity
  have hcψ0 : 0 < cψ := by rw [hcψ]; positivity
  have hCsum0 : 0 ≤ Csum := hCsum ▸ Finset.sum_nonneg fun j _ => hCm _
  have hδ₅0 : 0 < δ₅ := by rw [hδ₅]; positivity
  have hx₀κ : κ ^ 4 * H * ℓ ^ 2 ≤ x₀ := by
    rw [hx₀]
    have : κ ^ 4 * H * 1 * ℓ ^ 2 ≤ κ ^ 4 * H * B ^ ε * ℓ ^ 2 := by gcongr
    linarith only [this]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.pos
  have hpB : (p : ℝ) ≤ B := (Nat.cast_le.2 hpq).trans hqB
  -- the depth
  have hBV1 : 1 ≤ B ^ (4 - 2 * γ + 9 * ε) := Real.one_le_rpow hB1 (by linarith only [hγ2, hε0])
  have hHℓV : H * ℓ ≤ H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19 := by
    have h1 : H ≤ H ^ 19 := le_self_pow₀ hH (by norm_num)
    have h2 : ℓ ≤ ℓ ^ 19 := le_self_pow₀ hℓ1 (by norm_num)
    calc H * ℓ = H * 1 * ℓ := by ring
      _ ≤ H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19 := by gcongr
  have hℓV : ℓ ≤ H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19 :=
    le_trans (le_mul_of_one_le_left hℓ0.le hH) hHℓV
  have hCN0 : 0 < CN := lt_of_lt_of_le (by positivity) hCN1
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hNℓ : CN * ℓ ≤ N := le_trans (mul_le_mul_of_nonneg_left hℓV hCN0.le) hN
  have h16 : 16 * (r + L) ≤ N := by
    have h1 : 16 * CrL ≤ CN := by linarith only [hCrL, hCN1]
    have h2 : 16 * CrL * ℓ ≤ CN * ℓ := mul_le_mul_of_nonneg_right h1 hℓ0.le
    have : (16 : ℝ) * (r + L) ≤ N := by linarith only [h2, hrL, hNℓ]
    exact_mod_cast this
  -- (d) the flat block
  obtain ⟨n, m, β, α, hnN, hα0, hα12, hmα, hMF⟩ :=
    hflat H t N r L (by linarith only [hH]) ht hr2' h16 hle
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 8 / 3 * 4 ^ r := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 512 / 3 * H * (r + L) / N := ⟨_, rfl⟩
  rw [← hT, ← he] at hMF
  rw [← hT] at hmα
  have h4r : (16 : ℝ) ≤ 4 ^ r := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hr2'
    norm_num at this
    exact this
  have hT1 : 64 / 3 ≤ T := by rw [hT]; linarith only [h4r]
  have hT0 : 0 < T := by linarith only [hT1]
  have hTx₀ : x₀ ≤ T := by rw [hT]; linarith only [hr1, h4r]
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he' : e ≤ 512 / 3 * H * CrL * ℓ / N := by
    rw [he]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    have := mul_le_mul_of_nonneg_left hrL (by positivity : (0 : ℝ) ≤ 512 / 3 * H)
    linarith only [this]
  have he256 : e ≤ 1 / 256 := by
    refine he'.trans ?_
    rw [div_le_iff₀ hN0]
    have h2 : 512 / 3 * CrL * (H * ℓ) ≤
        512 / 3 * CrL * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) := by gcongr
    have h3 : 256 * (512 / 3 * CrL * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19)) ≤
        CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) := by
      have := mul_le_mul_of_nonneg_right hCN1
        (by positivity : (0 : ℝ) ≤ H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19)
      linarith only [this]
    nlinarith only [h2, h3, hN]
  have hsqe : √e ≤ 1 / 16 := by
    rw [show (1 / 16 : ℝ) = √(1 / 256) by
      rw [show (1 / 256 : ℝ) = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt he256
  have he1 : e ≤ 1 := by linarith only [he256]
  -- (e) the counting half of the window bounds
  have hcnt := (hwin n (r + L) m t T α e (1 / 4) β ht hT1 (Nat.le_add_right_of_le hr2') hα0.le
    he0 he1 le_rfl hMF).1
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ i, cutoff (β i / T) ^ 2 := ⟨_, rfl⟩
  rw [← hW] at hcnt
  have hWm : W ≤ m := by
    rw [hW]
    calc ∑ i, cutoff (β i / T) ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
          pow_le_one₀ (cutoff_nonneg _) (cutoff_le_one _)
      _ = m := by simp
  have hαT0 : 0 < α * T := mul_pos hα0 hT0
  have hαTW : α * T ≤ 16 * W := by
    have : α * T * (1 / 16) ≤ α * T * (1 / 8 - √e) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsqe]) hαT0.le
    linarith only [this, hcnt]
  have hmW : (m : ℝ) ≤ 16 * W := le_trans hmα hαTW
  have hW0 : 0 < W := by linarith only [hαTW, hαT0]
  have hm1 : (1 : ℝ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      have : W = 0 := by rw [hW]; subst hm; simp
      linarith only [this, hW0]
    · exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by linarith only [hm1]
  have hαTm : α * T ≤ 16 * m := by linarith only [hαTW, hWm]
  have hm12 : (m : ℝ) ≤ 12 * H * T := by
    have := mul_le_mul_of_nonneg_right hα12 hT0.le
    linarith only [this, hmα]
  have hmx₀ : (m : ℝ) ≤ 128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2 := by
    have hT4 : T ≤ 32 / 3 * x₀ := by rw [hT]; linarith only [hr2]
    have := mul_le_mul_of_nonneg_left hT4 (by positivity : (0 : ℝ) ≤ 12 * H)
    rw [hx₀] at this
    linarith only [this, hm12]
  have hmZ : (m : ℝ) ≤ 128 * κ ^ 4 * Z ^ 5 := by
    calc (m : ℝ) ≤ 128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2 := hmx₀
      _ ≤ 128 * κ ^ 4 * Z ^ 2 * Z * Z ^ 2 := by
          gcongr
          exact hBεB.trans hBZ
      _ = 128 * κ ^ 4 * Z ^ 5 := by ring
  -- (c) the noncancelling harmonic
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (p : ℝ) + q := ⟨_, rfl⟩
  obtain ⟨k, hk4, hk6, hkS⟩ := hharm m (fun i => cutoff (β i / T))
    (fun i => -(π * Q * β i / 4)) (fun i => cutoff_nonneg _) (hW ▸ hW0)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = Q * k / 8 := ⟨_, rfl⟩
  have hSnorm : √m / 8 ≤ ‖∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
      Complex.exp (↑(-2 * π * ξ * β i) * Complex.I)‖ := by
    have hS0 : ∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
          Complex.exp (↑(-2 * π * ξ * β i) * Complex.I) =
        ∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
          Complex.exp (↑((k : ℝ) * -(π * Q * β i / 4)) * Complex.I) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 4
      rw [hξ]
      ring
    rw [hS0]
    have h1 : (m : ℝ) / 64 ≤ ‖∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
        Complex.exp (↑((k : ℝ) * -(π * Q * β i / 4)) * Complex.I)‖ ^ 2 := by
      have h0 : W / 4 ≤ ‖∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
          Complex.exp (↑((k : ℝ) * -(π * Q * β i / 4)) * Complex.I)‖ ^ 2 := hW ▸ hkS
      linarith only [h0, hmW]
    calc √m / 8 = √((m : ℝ) / 64) := by
          rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 64),
            show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √(‖∑ i, ((cutoff (β i / T) : ℝ) : ℂ) *
          Complex.exp (↑((k : ℝ) * -(π * Q * β i / 4)) * Complex.I)‖ ^ 2) :=
        Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  -- the harmonic `k = 4^v h ≤ K`
  obtain ⟨v, h, hh, hkvh⟩ := hk4
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ k := by
    have : 1 ≤ k := by rw [hkvh]; exact Nat.mul_pos (by positivity) hh.pos
    exact_mod_cast this
  have hm2 : (m : ℝ) ^ 2 ≤ 128 ^ 2 * κ ^ 8 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 := by
    have := pow_le_pow_left₀ hm0 hmx₀ 2
    calc (m : ℝ) ^ 2 ≤ (128 * κ ^ 4 * H ^ 2 * B ^ ε * ℓ ^ 2) ^ 2 := this
      _ = _ := by ring
  have hkK : (k : ℝ) ≤ K := by
    have h6 : 6 * (128 ^ 2 * κ ^ 8 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4) =
        6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 := by ring
    linarith only [hk6, hm2, hKge, h6]
  have hhK : h ≤ K := by
    have : h ≤ k := by rw [hkvh]; exact Nat.le_mul_of_pos_left h (by positivity)
    have hK' : k ≤ K := by exact_mod_cast hkK
    exact this.trans hK'
  -- (a) the complementary lower bound
  have hAA := hbound γ B K p q k v h n hB1 hp hq hpB hqB hX hh hhK hkvh
  -- the frequency `ξ = Qk/8` and the logarithm `ℓ' = log(2 + Qk)`
  have hQ2 : 2 ≤ Q := by rw [hQ]; linarith only [hp1, hq1]
  have hQB : Q ≤ 2 * B := by rw [hQ]; linarith only [hpB, hqB]
  have hk6' : (k : ℝ) ≤ 6 * m ^ 2 := hk6.le
  have hξ14 : 1 / 4 ≤ ξ := by
    rw [hξ]
    have := mul_le_mul hQ2 hk1 (by norm_num) (by linarith only [hQ2])
    linarith only [this]
  have hξ0 : 0 < ξ := by linarith only [hξ14]
  have hξB : ξ ≤ 3 / 2 * B * m ^ 2 := by
    rw [hξ]
    have := mul_le_mul hQB hk6' hk0 (by linarith only [hB1])
    linarith only [this]
  have hBm2 : B * (m : ℝ) ^ 2 ≤ 128 ^ 2 * κ ^ 8 * Z ^ 10 := by
    calc B * (m : ℝ) ^ 2 ≤ B * (128 ^ 2 * κ ^ 8 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4) := by gcongr
      _ = 128 ^ 2 * κ ^ 8 * H ^ 4 * (B * (B ^ ε) ^ 2) * ℓ ^ 4 := by ring
      _ ≤ 128 ^ 2 * κ ^ 8 * Z ^ 4 * (Z * Z) * Z ^ 4 := by
          gcongr
          · exact hBε2.trans hBZ
      _ = 128 ^ 2 * κ ^ 8 * Z ^ 10 := by ring
  have hQk0 : 0 ≤ Q * k := mul_nonneg (by linarith only [hQ2]) hk0
  have hQk : Q * k ≤ 12 * 128 ^ 2 * κ ^ 8 * Z ^ 10 := by
    have h1 : Q * k ≤ 2 * B * (6 * m ^ 2) := mul_le_mul hQB hk6' hk0 (by linarith only [hB1])
    linarith only [h1, hBm2]
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : ℝ, ℓ' = Real.log (2 + Q * k) := ⟨_, rfl⟩
  have hℓ'0 : 0 ≤ ℓ' := hℓ' ▸ Real.log_nonneg (by linarith only [hQk0])
  have hℓ'bd : ℓ' ≤ 200018 * κ * ℓ := by
    rw [hℓ', hℓ]; exact log_two_add_le hQk0 hQk hκ1 hZ4
  -- the perturbation condition of (b)
  have hpert : 4 * |t - ((q : ℝ) - p) / ((p : ℝ) + q)| * (((p : ℝ) + q) * k / 8) *
      Real.log (2 + ((p : ℝ) + q) * k) ≤ c₀ := by
    have ht' : |t - ((q : ℝ) - p) / Q| ≤ crad / (H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5) := by
      rw [hQ, add_comm (p : ℝ) q]; exact htt₀
    have hD0 : 0 < H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5 := by positivity
    have hBexp : B * (B ^ ε) ^ 2 = B ^ (1 + 2 * ε) := by
      rw [← Real.rpow_mul_natCast (by linarith only [hB1]),
        Real.rpow_add (by linarith only [hB1]), Real.rpow_one]
      push_cast; ring_nf
    have hξℓ : ξ * ℓ' ≤ 3 / 2 * 128 ^ 2 * 200018 * κ ^ 9 * (H ^ 4 * B ^ (1 + 2 * ε) * ℓ ^ 5) := by
      have h1 : ξ * ℓ' ≤ 3 / 2 * B * m ^ 2 * (200018 * κ * ℓ) :=
        mul_le_mul hξB hℓ'bd hℓ'0 (by positivity)
      have h2 : 3 / 2 * B * (m : ℝ) ^ 2 * (200018 * κ * ℓ) ≤ 3 / 2 * 200018 * κ * ℓ *
          (B * (128 ^ 2 * κ ^ 8 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4)) := by
        have := mul_le_mul_of_nonneg_left hm2
          (by positivity : (0 : ℝ) ≤ 3 / 2 * B * (200018 * κ * ℓ))
        linarith only [this]
      have h3 : 3 / 2 * 200018 * κ * ℓ * (B * (128 ^ 2 * κ ^ 8 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4)) =
          3 / 2 * 128 ^ 2 * 200018 * κ ^ 9 * (H ^ 4 * (B * (B ^ ε) ^ 2) * ℓ ^ 5) := by ring
      rw [hBexp] at h3
      linarith only [h1, h2, h3]
    have := pert_le (abs_nonneg _) ht' hD0 hξℓ (mul_nonneg hξ0.le hℓ'0) hcrad hκ0
    rw [hℓ', hξ, hQ] at this
    exact this
  -- the box condition of (b)
  have hbox : 8 / 3 / 4 ^ n * (((p : ℝ) + q) * k / 8) ≤ 1 / 4 := by
    have hn : ((a₀ : ℝ) + 11) * Real.log Z ≤ n := by
      rw [← hℓ]
      have h1 : (N : ℝ) ≤ 2 * (n + r) := by exact_mod_cast hnN
      have h2 : (r : ℝ) ≤ CrL * ℓ := by
        have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        linarith only [hrL, this]
      have h3 : 2 * ((a₀ : ℝ) + 11 + CrL) * ℓ ≤ CN * ℓ :=
        mul_le_mul_of_nonneg_right hCN2 hℓ0.le
      nlinarith only [h1, h2, h3, hNℓ]
    have hξZ : 32 / 3 * ξ ≤ 16 * 128 ^ 2 * κ ^ 8 * Z ^ 11 := by
      have h2 : Z ^ 10 ≤ Z ^ 11 := pow_le_pow_right₀ hZ1 (by norm_num)
      have h3 : 128 ^ 2 * κ ^ 8 * Z ^ 10 ≤ 128 ^ 2 * κ ^ 8 * Z ^ 11 := by gcongr
      nlinarith only [hξB, hBm2, h3]
    have := box_le hZ4 hn ha₀ hξZ
    rw [hξ, hQ] at this
    exact this
  -- (b) the relative derivatives
  obtain ⟨hlow, hmom⟩ := hrel p q k n t hp hq ⟨v, h, hh, hkvh⟩ ht hpert hbox
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = |tailFT n t ξ| := ⟨_, rfl⟩
  have hmom' : ∀ j, ‖tailMoment n t j ξ‖ ≤ Cm j * ℓ' ^ j * ψ := by
    intro j; rw [hψ, hℓ', hξ, hQ]; exact hmom j
  have hψP : cψ ≤ ψ * ((m : ℝ) ^ 4 * B ^ (2 - γ)) := by
    have hk2 : (k : ℝ) ^ 2 ≤ 36 * (m : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ hk0 hk6' 2
      linarith only [this]
    have h1 : c₁ * (4 * B ^ (γ - 2) / (π ^ 2 * (k : ℝ) ^ 2)) ≤ ψ := by
      rw [hψ, hξ, hQ]
      exact le_trans (mul_le_mul_of_nonneg_left hAA hc₁.le) hlow
    rw [hcψ]
    exact psi_lower hc₁ hB1 (by linarith only [hk1]) (by linarith only [hm1]) hk2 h1
  have hP0 : 0 < (m : ℝ) ^ 4 * B ^ (2 - γ) := by
    have : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
    positivity
  -- (iv) the relative-derivative corrections
  have hcorr : √(m : ℝ) * ℓ' / T ≤ δ₅ :=
    corr_small hm0 hT0 hm12 (hx₀κ.trans hTx₀) hℓ'bd hℓ'0 hκ1 hH hℓ1 hδ₅0 hκℓ
  have hsqm1 : 1 ≤ √(m : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hm1
  have hδ₅1 : δ₅ ≤ 1 := by
    rw [hδ₅, div_le_one (by positivity)]
    have := mul_nonneg hCsum0 hCχ.le
    linarith only [this]
  have hℓ'T : ℓ' ≤ T := by
    have h1 : ℓ' / T ≤ √(m : ℝ) * ℓ' / T := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (div_nonneg hℓ'0 hT0.le) hsqm1
    have h2 : ℓ' / T ≤ 1 := by linarith only [h1, hcorr, hδ₅1]
    rwa [div_le_one hT0] at h2
  -- (e) the window bound at `ξ` and the window chain
  have hwinξ := (hwin n (r + L) m t T α e ξ β ht hT1 (Nat.le_add_right_of_le hr2') hα0.le he0
    he1 hξ14 hMF).2
  have hT1' : 1 ≤ T := by linarith only [hT1]
  have hh0 : 0 ≤ T / 4 ^ (r + L) := div_nonneg hT0.le (by positivity)
  have hchain := window_chain β Cm hT1' hξ14 hα0.le hh0 hℓ'0 hℓ'T hCE.le hCm hCχ.le hχ hψ
    hmom' hαTm hwinξ
  rw [← hCsum] at hchain
  -- the four error ratios
  have hTL : T / 4 ^ (r + L) = 8 / 3 / 4 ^ L := by rw [hT, pow_add]; field_simp
  have hsY := taylor_small hJ10 hm1 hm12 (hx₀ ▸ hTx₀) hH hB1 hℓ1 hκ1 hJε hε0 hδ₁0 hκY
  have hse := flat_small hm0 hmx₀ he0 he' hN0 hH hB1 hℓ1 hκ1 hδ₁0 hN hCN3
  have hsA := avg_small hm1 hκ1 hmZ hB1 hBZ hγ0 hξ0.le hξB hL1 hδ₁0 hΛδ
  rw [← hTL] at hsA
  rw [hδ₁] at hsY hse hsA
  have hsρ : √(m : ℝ) * (ℓ' / T) ≤ 1 / (64 * (Csum * Cχ + 1)) := by
    rw [← mul_div_assoc, ← hδ₅]; exact hcorr
  exact window_contra hψP hcψ0 hP0 hm1 hCE hCsum0 hCχ.le hSnorm hchain hsY hse hsA hsρ

theorem exclusion_of (hcount : ComplementaryCountStatement)
    (hbound : ComplementaryBoundStatement) (hrel : RelDerivStatement)
    (hharm : HarmonicStatement) (hflat : FlatBlockStatement) (hwin : WindowBoundStatement)
    {γ ε : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ExclusionStatement γ ε := by
  obtain ⟨CA, hCA, hcount⟩ := hcount
  obtain ⟨c₀, c₁, hc₀, hc₁, Cm, hCm, hrel⟩ := hrel
  -- the Taylor order
  obtain ⟨J, hJ10, hJε⟩ : ∃ J : ℕ, 10 ≤ J ∧ 2 - γ ≤ ε * ((J : ℝ) - 5) := by
    refine ⟨⌈(2 - γ) / ε⌉₊ + 10, by omega, ?_⟩
    have h1 : (2 - γ) / ε ≤ ⌈(2 - γ) / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε0] at h1
    push_cast
    nlinarith
  obtain ⟨CE, hCE, hwin⟩ := hwin J
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_bound_iteratedDeriv_cutoff J
  -- the constants, chosen in the order `κ`, `Λ`, the depth constant, the radius constant
  obtain ⟨Csum, hCsum⟩ : ∃ Csum : ℝ, Csum = ∑ j ∈ Finset.range J, Cm (j + 1) := ⟨_, rfl⟩
  obtain ⟨cψ, hcψ⟩ : ∃ cψ : ℝ, cψ = c₁ / (9 * π ^ 2) := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = cψ / (1088 * CE) := ⟨_, rfl⟩
  obtain ⟨δ₅, hδ₅⟩ : ∃ δ₅ : ℝ, δ₅ = 1 / (64 * (Csum * Cχ + 1)) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = max 2 (max (12 ^ 5 * 4 ^ J / δ₁) (12 * 200018 ^ 2 / δ₅ ^ 2)) :=
    ⟨_, rfl⟩
  have hκ2 : 2 ≤ κ := hκ ▸ le_max_left _ _
  have hκ1 : 1 ≤ κ := by linarith only [hκ2]
  have hκY : 12 ^ 5 * 4 ^ J / δ₁ ≤ κ := hκ ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hκℓ : 12 * 200018 ^ 2 / δ₅ ^ 2 ≤ κ := hκ ▸ (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = max 1 (4 * (128 * κ ^ 4) ^ 7 / δ₁) := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := hΛ ▸ le_max_left _ _
  have hΛδ : 4 * (128 * κ ^ 4) ^ 7 / δ₁ ≤ Λ := hΛ ▸ le_max_right _ _
  obtain ⟨CrL, hCrL⟩ : ∃ CrL : ℝ, CrL = 2 + 4 * κ + Real.log Λ + 42 := ⟨_, rfl⟩
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hCrL0 : 0 < CrL := by rw [hCrL]; linarith only [hlogΛ, hκ1]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, 16 * 128 ^ 2 * κ ^ 8 ≤ 4 ^ a₀ :=
    (pow_unbounded_of_one_lt _ (by norm_num : (1 : ℝ) < 4)).imp fun _ h => h.le
  obtain ⟨CN, hCN⟩ : ∃ CN : ℝ, CN = max (256 * (512 / 3) * CrL)
      (max (2 * ((a₀ : ℝ) + 11 + CrL)) ((128 * κ ^ 4) ^ 9 * (512 / 3) * CrL / δ₁ ^ 2)) :=
    ⟨_, rfl⟩
  have hCN1 : 256 * (512 / 3) * CrL ≤ CN := hCN ▸ le_max_left _ _
  have hCN2 : 2 * ((a₀ : ℝ) + 11 + CrL) ≤ CN := hCN ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hCN3 : (128 * κ ^ 4) ^ 9 * (512 / 3) * CrL / δ₁ ^ 2 ≤ CN :=
    hCN ▸ (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨CX, hCX⟩ : ∃ CX : ℝ, CX = CA * (6 * 128 ^ 2 * κ ^ 8 + 1) := ⟨_, rfl⟩
  have hCX0 : 0 < CX := by rw [hCX]; positivity
  obtain ⟨crad, hcrad⟩ : ∃ crad : ℝ, crad = c₀ / (6 * 128 ^ 2 * 200018 * κ ^ 9) := ⟨_, rfl⟩
  have hκ9 : 0 < κ ^ 9 := pow_pos (by linarith only [hκ1]) 9
  have hcrad0 : 0 < crad := by
    rw [hcrad]; exact div_pos hc₀ (mul_pos (by norm_num) hκ9)
  refine ⟨max CX CN, crad, lt_of_lt_of_le hCX0 (le_max_left _ _), hcrad0, fun H hH B hB => ?_⟩
  -- the scales attached to `H` and `B`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 2 + H * B := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (2 + H * B) := ⟨_, rfl⟩
  have hℓZ' : ℓ = Real.log Z := by rw [hℓ, hZ]
  rw [← hℓ]
  have hB1 : 1 ≤ B := by linarith only [hB]
  have hHB : 2 ≤ H * B := by
    have := mul_le_mul hH hB (by norm_num) (by linarith only [hH])
    linarith only [this]
  have hZ4 : 4 ≤ Z := by rw [hZ]; linarith only [hHB]
  have hZ0 : 0 < Z := by linarith only [hZ4]
  have hℓ1 : 1 ≤ ℓ := hℓZ' ▸ one_le_log_of_four_le hZ4
  have hHZ : H ≤ Z := by
    have := le_mul_of_one_le_right (by linarith only [hH] : (0 : ℝ) ≤ H) hB1
    rw [hZ]; linarith only [this]
  have hBZ : B ≤ Z := by
    have := le_mul_of_one_le_left (by linarith only [hB1] : (0 : ℝ) ≤ B) hH
    rw [hZ]; linarith only [this]
  have hBε1 : 1 ≤ B ^ ε := Real.one_le_rpow hB1 hε0.le
  have hBεB : B ^ ε ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (show ε ≤ 1 by linarith only [hε])
  have hℓZ : ℓ ≤ Z := hℓZ' ▸ log_le_self' hZ0
  -- the window scale `R = 4^r`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = κ ^ 4 * H * B ^ ε * ℓ ^ 2 := ⟨_, rfl⟩
  have hx₀1 : 1 ≤ x₀ := by
    rw [hx₀]
    have h1 : (1 : ℝ) ≤ κ ^ 4 := one_le_pow₀ hκ1
    have h2 : (1 : ℝ) ≤ ℓ ^ 2 := one_le_pow₀ hℓ1
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ κ ^ 4 * H * B ^ ε * ℓ ^ 2 := by gcongr
  have hx₀Z : x₀ ≤ κ ^ 4 * Z ^ 4 := by
    rw [hx₀]
    calc κ ^ 4 * H * B ^ ε * ℓ ^ 2 ≤ κ ^ 4 * Z * Z * Z ^ 2 := by
          gcongr
          exact hBεB.trans hBZ
      _ = κ ^ 4 * Z ^ 4 := by ring
  obtain ⟨r, hr1, hr2, hr3⟩ := exists_four_pow_between hx₀1
  have hr2' : 2 ≤ r := by
    by_contra h
    have h16 : 16 ≤ x₀ := by
      rw [hx₀]
      have h1 : (16 : ℝ) ≤ κ ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) hκ2 4
        norm_num at this
        exact this
      have h2 : (1 : ℝ) ≤ ℓ ^ 2 := one_le_pow₀ hℓ1
      calc (16 : ℝ) = 16 * 1 * 1 * 1 := by ring
        _ ≤ κ ^ 4 * H * B ^ ε * ℓ ^ 2 := by gcongr
    have : (4 : ℝ) ^ r ≤ 4 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [this, hr1, h16]
  -- the averaging resolution `4^L`
  have hΛZ : 1 ≤ Λ * Z ^ 38 :=
    one_le_mul_of_one_le_of_one_le hΛ1 (one_le_pow₀ (by linarith only [hZ4]))
  obtain ⟨L, hL1, -, hL3⟩ := exists_four_pow_between hΛZ
  have hrL : (r : ℝ) + L ≤ CrL * ℓ := by
    have hlogx : Real.log x₀ ≤ 4 * κ + 4 * ℓ := by
      calc Real.log x₀ ≤ Real.log (κ ^ 4 * Z ^ 4) :=
            Real.log_le_log (by linarith only [hx₀1]) hx₀Z
        _ = 4 * Real.log κ + 4 * ℓ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hℓZ']
          push_cast; ring
        _ ≤ 4 * κ + 4 * ℓ := by gcongr; exact log_le_self' (by linarith only [hκ1])
    have hlogL : Real.log (Λ * Z ^ 38) = Real.log Λ + 38 * ℓ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hℓZ']
      push_cast; ring
    rw [hlogL] at hL3
    have : (2 + 4 * κ + Real.log Λ) * 1 ≤ (2 + 4 * κ + Real.log Λ) * ℓ := by gcongr
    rw [hCrL]
    linarith only [this, hr3, hL3, hlogx]
  -- the harmonic budget and the exceptional set
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4⌉₊ :=
    ⟨_, rfl⟩
  have hHBℓ1 : 1 ≤ H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 := by
    have h1 : 1 ≤ H ^ 4 := one_le_pow₀ hH
    have h2 : 1 ≤ (B ^ ε) ^ 2 := one_le_pow₀ hBε1
    have h3 : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 := by gcongr
  have hKge : 6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 ≤ K := hK ▸ Nat.le_ceil _
  have hKle : (K : ℝ) ≤ (6 * 128 ^ 2 * κ ^ 8 + 1) * (H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4) := by
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 by positivity)
    rw [← hK] at this
    have e : 6 * (128 * κ ^ 4) ^ 2 * H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4 =
        6 * 128 ^ 2 * κ ^ 8 * (H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4) := by ring
    rw [e] at this
    linarith only [this, hHBℓ1]
  refine ⟨exceptionalSet B γ K, ?_, ?_⟩
  · -- the count (6)
    have hBexp : (B ^ ε) ^ 2 * B ^ (2 * sixthMomentDim + 6 * γ) =
        B ^ (2 * sixthMomentDim + 6 * γ + 2 * ε) := by
      rw [← Real.rpow_mul_natCast (by linarith only [hB1]),
        ← Real.rpow_add (by linarith only [hB1])]
      congr 1
      push_cast
      ring
    have hBpos : 0 ≤ B ^ (2 * sixthMomentDim + 6 * γ) := by positivity
    calc ((exceptionalSet B γ K).card : ℝ) ≤ CA * K * B ^ (2 * sixthMomentDim + 6 * γ) :=
          hcount γ B K hB1
      _ ≤ CA * ((6 * 128 ^ 2 * κ ^ 8 + 1) * (H ^ 4 * (B ^ ε) ^ 2 * ℓ ^ 4)) *
            B ^ (2 * sixthMomentDim + 6 * γ) := by gcongr
      _ = CX * H ^ 4 * ((B ^ ε) ^ 2 * B ^ (2 * sixthMomentDim + 6 * γ)) * ℓ ^ 4 := by
          rw [hCX]; ring
      _ = CX * H ^ 4 * B ^ (2 * sixthMomentDim + 6 * γ + 2 * ε) * ℓ ^ 4 := by rw [hBexp]
      _ ≤ max CX CN * H ^ 4 * B ^ (2 * sixthMomentDim + 6 * γ + 2 * ε) * ℓ ^ 4 := by
          gcongr
          exact le_max_left _ _
  · -- the exclusion (7)
    intro p q hp hq _hcop hpq hqB hX N hN t ht htt₀
    by_contra hle
    push Not at hle
    have hN' : CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) ≤ N := by
      refine le_trans ?_ hN
      have : CN ≤ max CX CN := le_max_right _ _
      have hV0 : 0 ≤ H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19 := by positivity
      calc CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19)
          ≤ max CX CN * (H ^ 19 * B ^ (4 - 2 * γ + 9 * ε) * ℓ ^ 19) := by gcongr
        _ = _ := by ring
    exact exclusion_pointwise hbound hharm hflat hrel hwin hγ0 hγ2 hε0 hε hJ10 hJε hc₁ hCm hCE
      hCχ hχ hCsum hcψ hδ₁ hδ₅ hκ1 hκY hκℓ hΛδ hCrL0 ha₀ hCN1 hCN2 hCN3 hcrad hH hB hZ hℓZ'
      hx₀ hr1 hr2 hr2' hL1 hrL hKge hp hq hpq hqB hX hN' ht htt₀ hle

end Favard
