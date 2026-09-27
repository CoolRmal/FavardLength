import FavardLength.Beyond.Assembly.Certificate
import FavardLength.Beyond.Assembly.LayerCake
import FavardLength.Beyond.Assembly.Superlevel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The beyond-quarter decay bound `Fav(K_n) ≤ C n^{-156307/625000}`

We assemble the final estimate of the beyond note (§5–6) from the combinatorial dichotomy, the
normalization bridge, the improved exceptional-direction estimate
`ExceptionalImprovedStatement s₀ β₀` (the old tail) and the new exceptional-energy estimate
`NewExceptionalStatement γ₀ ε₀` (the new tail).

`Favard.Assembly.favardLength_le_of_params` does the analysis for abstract exponents. For a
depth `P` and a projection threshold `u`, put `K = B/u`. By the geometric step and the two slope
tails (`Favard.Assembly.volume_superlevel_old`, `Favard.Assembly.volume_superlevel_new`),

* for `P^{-1/3} ≤ u ≤ √2`: `|{λ_P > u}| ≲ P^{-s/2} u^{-σ₁}`, `σ₁ = (5 - 2β/s + 2κ) s/2 < 1`;
* for `B P^{-z} ≤ u ≤ √2` (i.e. `K ≤ P^z`): `|{λ_P > u}| ≲ P^{5τ-(1-η)c₁/D} u^{-σ₂}`,
  `σ₂ = 4 + 20 c₁/D > 1`.

The layer cake (`Favard.Assembly.intervalIntegral_le_of_two_tails`) split at `T₀ = P^{-1/3}`
and `T₁ = B P^{-z}` gives
`Fav(K_P) ≲ P^{-1/3} + P^{-s/2 - z(1-σ₁)} + P^{5τ - (1-η)c₁/D + z(σ₂-1)}`,
each at most a constant times `P^{-a}`. The conditions on `P` (size of the denominator scale,
redundancy, depth, block length) are finitely many inequalities `M ≤ P^e` with `e > 0`, true for
all large `P`; small depths go into the constant through `Fav(K_n) ≤ √2`. All logarithms were
absorbed into small powers (`κ`, `τ`, `η`) inside the component lemmas.

`Favard.beyond_of` instantiates `s₀ = 1/2 - 10⁻⁷`, `β₀ = 3071/10000`, `γ₀ = 13/125`,
`ε₀ = 10⁻⁵`, `z = 1/625`, `κ = 1/20000`, `η = 10⁻⁴`, `τ = 10⁻⁶` and `a = 156307/625000`; the
exponent conditions are exact rational comparisons, together with
`μ(γ₀, ε₀) > 1349/25000` (`Favard.Assembly.redundancyExp_gt`, from `5^1000 < 4^1161`).
-/

open MeasureTheory Set Real Filter

namespace Favard

namespace Assembly

/-- For `e > 0`, eventually `M ≤ P^e` along the natural numbers. -/
lemma eventually_le_rpow {e : ℝ} (he : 0 < e) (M : ℝ) :
    ∀ᶠ P : ℕ in atTop, M ≤ (P : ℝ) ^ e :=
  ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

/-- The contribution `(4/π) M P^e B^σ (B P^{-z})^{1-σ}/d` of one tail to the layer cake is
`(4/π) (M B/d) P^{e - z(1-σ)}`. -/
lemma tail_term {B P : ℝ} (hB : 0 < B) (hP : 0 < P) (M e σ z d : ℝ) :
    4 / π * (M * P ^ e * B ^ σ * ((B * P ^ (-z)) ^ (1 - σ) / d)) =
      4 / π * (M * B / d) * P ^ (e - z * (1 - σ)) := by
  have h1 : B ^ σ * B ^ (1 - σ) = B := by
    rw [← rpow_add hB]
    simp
  have h2 : P ^ e * P ^ (-z * (1 - σ)) = P ^ (e - z * (1 - σ)) := by
    rw [← rpow_add hP]
    congr 1
    ring
  calc 4 / π * (M * P ^ e * B ^ σ * ((B * P ^ (-z)) ^ (1 - σ) / d))
      = 4 / π * (M * (B ^ σ * B ^ (1 - σ)) * (P ^ e * P ^ (-z * (1 - σ))) / d) := by
        rw [mul_rpow hB.le (rpow_pos_of_pos hP _).le, ← rpow_mul hP.le]
        ring
    _ = 4 / π * (M * B / d) * P ^ (e - z * (1 - σ)) := by
        rw [h1, h2]
        ring

/-- **The assembly for abstract exponents** (beyond note §5). The dichotomy, the bridge, the
improved exceptional-direction estimate with exponents `(s, β)` and a new exceptional-energy
estimate with exponents `(μ, D, c₁)` give `Fav(K_n) ≤ C n^{-a}` for every `a` below the three
exponents `1/3`, `s/2 + z(1 - σ₁)` and `(1-η) c₁/D - 5τ - z(σ₂ - 1)`, provided the auxiliary
exponents make the three conditions on the depth hold for large depths. -/
theorem favardLength_le_of_params (hD : DichotomyStatement) (hBr : BridgeStatement)
    {s β μ D c₁ κ z η τ a : ℝ} (hOld : ExceptionalImprovedStatement s β)
    (hNew : ∃ CN : ℝ, 0 < CN ∧ ∀ H : ℝ, 1 ≤ H → ∀ R : ℝ, 2 ≤ R →
      CN * H ^ 8 * Real.log (2 + H * R) ^ 9 ≤ R ^ μ →
      ∀ N : ℕ, CN * H ^ 19 * R ^ D * Real.log (2 + H * R) ^ 19 ≤ N →
        volume {t ∈ Icc (0 : ℝ) 1 | normEnergy N t ≤ H} ≤
          ENNReal.ofReal (CN * H ^ 4 * Real.log (2 + H * R) ^ 5 / R ^ c₁))
    (hs : 0 < s) (hD1 : 1 ≤ D) (hD20 : D ≤ 20) (hμ : 0 ≤ μ) (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2)
    (hη : 0 ≤ η) (hτ : 0 < τ) (hσ₁ : (5 - 2 * β / s + 2 * κ) * (s / 2) < 1)
    (hσ₂ : 1 < 4 + 20 * (c₁ / D)) (heR : 0 < (1 - η - 20 * z) / D)
    (heμ : 0 < (1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ)
    (hed : 0 < η - 19 * τ - z * κ) (ha0 : 0 ≤ a) (ha3 : a ≤ 1 / 3)
    (haold : a ≤ s / 2 + z * (1 - (5 - 2 * β / s + 2 * κ) * (s / 2)))
    (hanew : a ≤ (1 - η) * (c₁ / D) - 5 * τ - z * (4 + 20 * (c₁ / D) - 1)) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-a) := by
  -- the dichotomy, with `A ≥ 1` and `B ≥ 3`
  obtain ⟨A₀, B₀, c, -, -, hc, hD₀⟩ := hD
  set A := max A₀ 1 with hA_def
  set B := max B₀ 3 with hB_def
  have hA : 1 ≤ A := le_max_right _ _
  have hB : 3 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  have hD' : ∀ θ ∈ Icc 0 (π / 2), ∀ K : ℝ, 2 ≤ K → ∀ N J : ℕ, c * K * Real.log K ≤ J →
      B / K < projLength (N * J) θ → ∀ r ≤ N, energy r θ ≤ A * K := by
    intro θ hθ K hK N J hJ hlt r hr
    have hK0 : 0 < K := by linarith
    have h1 : B₀ / K ≤ B / K := div_le_div_of_nonneg_right (le_max_left _ _) hK0.le
    exact (hD₀ θ hθ K hK N J hJ (h1.trans_lt hlt) r hr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le)
  obtain ⟨CO, hCO, hOld'⟩ := hOld
  obtain ⟨CN, hCN, hNew'⟩ := hNew
  set C₃ := c / κ + 1 with hC₃
  have hC₃0 : 0 < C₃ := by positivity
  set L := (2 + A) ^ τ / τ with hL
  have hL0 : 0 < L := by positivity
  set σ₁ := (5 - 2 * β / s + 2 * κ) * (s / 2) with hσ₁_def
  set σ₂ := 4 + 20 * (c₁ / D) with hσ₂_def
  set X := 2 * C₃ * (2 + 1 / κ) * A ^ (4 - 2 * β / s + κ) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ A ^ (4 - 2 * β / s + κ) := rpow_nonneg (by linarith) _
    positivity
  -- the conditions on large depths
  have hev : ∀ᶠ P : ℕ in atTop, C₃ * B ^ (3 / 2 : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) ∧
      2 ≤ (P : ℝ) ^ ((1 - η - 20 * z) / D) ∧
      CN * A ^ 8 * L ^ 9 ≤ (P : ℝ) ^ ((1 - η) * μ / D - z * (8 + 20 * μ / D) - 9 * τ) ∧
      2 * C₃ * CN * A ^ 19 * L ^ 19 ≤ (P : ℝ) ^ (η - 19 * τ - z * κ) := by
    filter_upwards [eventually_le_rpow (by norm_num : (0 : ℝ) < 1 / 2) (C₃ * B ^ (3 / 2 : ℝ)),
      eventually_le_rpow heR 2, eventually_le_rpow heμ (CN * A ^ 8 * L ^ 9),
      eventually_le_rpow hed (2 * C₃ * CN * A ^ 19 * L ^ 19)] with P h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.1 hev
  -- the constant
  have hQ₁ : 0 ≤ 4 / π * (CO * X ^ (s / 2) * B / (1 - σ₁)) := by
    have : 0 ≤ X ^ (s / 2) := rpow_nonneg hX0 _
    have : 0 < 1 - σ₁ := by linarith
    positivity
  have hQ₂ : 0 ≤ 4 / π * (CN * A ^ 4 * L ^ 5 * B / (σ₂ - 1)) := by
    have : 0 < σ₂ - 1 := by linarith
    positivity
  have hP₀a : 0 ≤ √2 * (P₀ : ℝ) ^ a := mul_nonneg (sqrt_nonneg _) (rpow_nonneg (by positivity) _)
  refine ⟨√2 * (P₀ : ℝ) ^ a + 1 + 4 / π * (CO * X ^ (s / 2) * B / (1 - σ₁)) +
    4 / π * (CN * A ^ 4 * L ^ 5 * B / (σ₂ - 1)), by positivity, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 0 ≤ (n : ℝ) ^ (-a) := rpow_nonneg hn0.le _
  rcases lt_or_ge n P₀ with hlt | hge
  · -- small depths: `Fav(K_n) ≤ √2 ≤ √2 P₀^a n^{-a}`
    have h2 : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
      rw [← rpow_add hn0]
      simp
    have h3 : (n : ℝ) ^ a ≤ (P₀ : ℝ) ^ a :=
      rpow_le_rpow hn0.le (by exact_mod_cast hlt.le) ha0
    calc favardLength n ≤ √2 := favardLength_le_sqrt_two n
      _ = √2 * ((n : ℝ) ^ a * (n : ℝ) ^ (-a)) := by rw [h2, mul_one]
      _ ≤ √2 * ((P₀ : ℝ) ^ a * (n : ℝ) ^ (-a)) := by gcongr
      _ = (√2 * (P₀ : ℝ) ^ a) * (n : ℝ) ^ (-a) := by ring
      _ ≤ _ := by
          gcongr
          linarith
  -- large depths: layer cake with the old tail below `B n^{-z}` and the new tail above it
  obtain ⟨hPB, hR, hred, hdepth⟩ := hP₀ n hge
  have hT₁ : 0 < B * (n : ℝ) ^ (-z) := mul_pos hB0 (rpow_pos_of_pos hn0 _)
  have hM₁ : 0 ≤ CO * X ^ (s / 2) * (n : ℝ) ^ (-(s / 2)) * B ^ σ₁ := by
    have := rpow_nonneg hX0 (s / 2)
    have := rpow_pos_of_pos hn0 (-(s / 2))
    have := rpow_pos_of_pos hB0 σ₁
    positivity
  have hM₂ : 0 ≤ CN * A ^ 4 * L ^ 5 * (n : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) * B ^ σ₂ := by
    have := rpow_pos_of_pos hn0 (5 * τ - (1 - η) * (c₁ / D))
    have := rpow_pos_of_pos hB0 σ₂
    positivity
  have hint := intervalIntegral_le_of_two_tails (measurable_projLength n)
    (projLength_nonneg n) (b := π / 4) (T₀ := (n : ℝ) ^ (-(1 / 3 : ℝ))) (by positivity)
    (rpow_nonneg hn0.le _) hT₁ hM₁ hM₂ hσ₁ hσ₂ (projLength_le_sqrt_two n)
    (fun u hu0 _ hu1 => volume_superlevel_old hA hB hc hD' hBr hs hCO.le hOld' hκ hκ2 hn1 hPB
      hu0 hu1.le)
    (fun u hu0 huz hu1 => volume_superlevel_new hA hB hc hD' hBr hCN hNew' hD1 hD20 hμ hκ hκ2
      hη hτ hn1 hPB hR hred hdepth hu0 huz hu1.le)
  have e1 : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (n : ℝ) ^ (-a) :=
    rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e2 : (n : ℝ) ^ (-(s / 2) - z * (1 - σ₁)) ≤ (n : ℝ) ^ (-a) :=
    rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e3 : (n : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D) - z * (1 - σ₂)) ≤ (n : ℝ) ^ (-a) :=
    rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hπ : 4 / π * (π / 4) = 1 := by field_simp
  rw [favardLength_eq_quarter]
  calc 4 / π * ∫ θ in (0)..(π / 4), projLength n θ
      ≤ 4 / π * (π / 4 * (n : ℝ) ^ (-(1 / 3 : ℝ)) +
          CO * X ^ (s / 2) * (n : ℝ) ^ (-(s / 2)) * B ^ σ₁ *
            ((B * (n : ℝ) ^ (-z)) ^ (1 - σ₁) / (1 - σ₁)) +
          CN * A ^ 4 * L ^ 5 * (n : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) * B ^ σ₂ *
            ((B * (n : ℝ) ^ (-z)) ^ (1 - σ₂) / (σ₂ - 1))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (n : ℝ) ^ (-(1 / 3 : ℝ)) +
          4 / π * (CO * X ^ (s / 2) * (n : ℝ) ^ (-(s / 2)) * B ^ σ₁ *
            ((B * (n : ℝ) ^ (-z)) ^ (1 - σ₁) / (1 - σ₁))) +
          4 / π * (CN * A ^ 4 * L ^ 5 * (n : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D)) * B ^ σ₂ *
            ((B * (n : ℝ) ^ (-z)) ^ (1 - σ₂) / (σ₂ - 1))) := by
        linear_combination (n : ℝ) ^ (-(1 / 3 : ℝ)) * hπ
    _ = (n : ℝ) ^ (-(1 / 3 : ℝ)) +
          4 / π * (CO * X ^ (s / 2) * B / (1 - σ₁)) * (n : ℝ) ^ (-(s / 2) - z * (1 - σ₁)) +
          4 / π * (CN * A ^ 4 * L ^ 5 * B / (σ₂ - 1)) *
            (n : ℝ) ^ (5 * τ - (1 - η) * (c₁ / D) - z * (1 - σ₂)) := by
        rw [tail_term hB0 hn0, tail_term hB0 hn0]
    _ ≤ (n : ℝ) ^ (-a) + 4 / π * (CO * X ^ (s / 2) * B / (1 - σ₁)) * (n : ℝ) ^ (-a) +
          4 / π * (CN * A ^ 4 * L ^ 5 * B / (σ₂ - 1)) * (n : ℝ) ^ (-a) :=
        add_le_add (add_le_add e1 (mul_le_mul_of_nonneg_left e2 hQ₁))
          (mul_le_mul_of_nonneg_left e3 hQ₂)
    _ ≤ √2 * (P₀ : ℝ) ^ a * (n : ℝ) ^ (-a) + ((n : ℝ) ^ (-a) +
          4 / π * (CO * X ^ (s / 2) * B / (1 - σ₁)) * (n : ℝ) ^ (-a) +
          4 / π * (CN * A ^ 4 * L ^ 5 * B / (σ₂ - 1)) * (n : ℝ) ^ (-a)) :=
        le_add_of_nonneg_left (mul_nonneg hP₀a hna)
    _ = _ := by ring

end Assembly

/-- **The beyond-quarter decay bound** (beyond note (1)): from the combinatorial dichotomy, the
normalization bridge, the improved exceptional-direction estimate with `s₀ = 1/2 - 10⁻⁷`,
`β₀ = 3071/10000`, and the new exceptional-energy estimate with `γ₀ = 13/125`, `ε₀ = 10⁻⁵`,
`Fav(K_n) ≤ C n^{-156307/625000}` for all `n ≥ 1`. -/
theorem beyond_of (hD : DichotomyStatement) (hB : BridgeStatement)
    (hOld : ExceptionalImprovedStatement (1 / 2 - 1 / 10 ^ 7) (3071 / 10000))
    (hNew : NewExceptionalStatement (13 / 125) (1 / 100000)) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → favardLength n ≤ C * (n : ℝ) ^ (-(156307 / 625000 : ℝ)) := by
  have hμ := Assembly.redundancyExp_gt
  have hDval : (4 - 2 * (13 / 125) + 9 * (1 / 100000) : ℝ) = 379209 / 100000 := by norm_num
  obtain ⟨CN, hCN, hNew'⟩ := hNew
  refine Assembly.favardLength_le_of_params hD hB hOld ⟨CN, hCN, hNew'⟩
    (κ := 1 / 20000) (z := 1 / 625) (η := 1 / 10 ^ 4) (τ := 1 / 10 ^ 6)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hDval]
  linarith

end Favard
