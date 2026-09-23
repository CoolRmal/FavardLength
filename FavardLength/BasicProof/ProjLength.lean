import FavardLength.BasicProof.Cantor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The projection length

Finiteness, boundedness, monotonicity in the depth, measurability in the angle, and the two
reflection symmetries `θ ↦ π - θ` and `θ ↦ π/2 - θ` of the projection length
`λ(π_θ(K_n))`.

Measurability is proved without any continuity argument: for a compact `K ⊆ ℝ²`, the set
`{(θ, x) | x ∈ π_θ(K)}` is closed (it is the image of a closed set under a projection along the
compact factor `K`), so its sections have measurable measure by `measurable_measure_prodMk_left`.
-/

open MeasureTheory Set Real

namespace Favard.BasicProof

theorem volume_proj_image_fourCorner_ne_top (n : ℕ) (θ : ℝ) :
    volume (proj θ '' fourCorner n) ≠ ⊤ :=
  (isCompact_proj_image_fourCorner θ n).measure_lt_top.ne

theorem projLength_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ projLength n θ :=
  ENNReal.toReal_nonneg

/-! ### The bound `√2` -/

/-- The projection of `[0,1]²` in an arbitrary direction lies in an interval of length
`|cos θ| + |sin θ|`. -/
theorem proj_image_unitSquare_subset (θ : ℝ) :
    proj θ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆
      Icc (min 0 (cos θ) + min 0 (sin θ)) (max 0 (cos θ) + max 0 (sin θ)) := by
  rintro _ ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
  simp only [proj]
  have key : ∀ c t : ℝ, 0 ≤ t → t ≤ 1 → min 0 c ≤ t * c ∧ t * c ≤ max 0 c := by
    intro c t h0 h1
    rcases le_total 0 c with hc | hc
    · rw [min_eq_left hc, max_eq_right hc]
      constructor <;> nlinarith
    · rw [min_eq_right hc, max_eq_left hc]
      constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := key (cos θ) x hx0 hx1
  obtain ⟨h3, h4⟩ := key (sin θ) y hy0 hy1
  exact ⟨by linarith, by linarith⟩

theorem abs_cos_add_abs_sin_le_sqrt_two (θ : ℝ) : |cos θ| + |sin θ| ≤ √2 := by
  rw [Real.le_sqrt (by positivity) (by norm_num)]
  nlinarith [sq_abs (cos θ), sq_abs (sin θ), sin_sq_add_cos_sq θ,
    sq_nonneg (|cos θ| - |sin θ|)]

theorem projLength_le_sqrt_two (n : ℕ) (θ : ℝ) : projLength n θ ≤ √2 := by
  have hsub : proj θ '' fourCorner n ⊆
      Icc (min 0 (cos θ) + min 0 (sin θ)) (max 0 (cos θ) + max 0 (sin θ)) :=
    (image_mono (fourCorner_subset n)).trans (proj_image_unitSquare_subset θ)
  have hlen : (max 0 (cos θ) + max 0 (sin θ)) - (min 0 (cos θ) + min 0 (sin θ)) =
      |cos θ| + |sin θ| := by
    rcases le_total 0 (cos θ) with h | h <;> rcases le_total 0 (sin θ) with h' | h' <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, abs_of_nonneg,
        abs_of_nonpos, h, h'] <;> ring
  unfold projLength
  calc (volume (proj θ '' fourCorner n)).toReal
      ≤ (volume (Icc (min 0 (cos θ) + min 0 (sin θ))
          (max 0 (cos θ) + max 0 (sin θ)))).toReal :=
        ENNReal.toReal_mono measure_Icc_lt_top.ne (measure_mono hsub)
    _ = |cos θ| + |sin θ| := by
        rw [Real.volume_Icc, hlen, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ √2 := abs_cos_add_abs_sin_le_sqrt_two θ

/-! ### Monotonicity in the depth -/

theorem projLength_antitone {m n : ℕ} (h : m ≤ n) (θ : ℝ) :
    projLength n θ ≤ projLength m θ :=
  ENNReal.toReal_mono (volume_proj_image_fourCorner_ne_top m θ)
    (measure_mono (image_mono (fourCorner_antitone h)))

/-! ### Measurability in the angle -/

/-- For compact `K`, the set `{(θ, x) | x ∈ π_θ(K)}` is closed. -/
theorem isClosed_setOf_mem_proj_image {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    IsClosed {q : ℝ × ℝ | q.2 ∈ proj q.1 '' K} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hT : IsClosed {z : (ℝ × ℝ) × K | proj z.1.1 z.2 = z.1.2} :=
    isClosed_eq (by unfold proj; fun_prop) (by fun_prop)
  have hS : {q : ℝ × ℝ | q.2 ∈ proj q.1 '' K} =
      Prod.fst '' {z : (ℝ × ℝ) × K | proj z.1.1 z.2 = z.1.2} := by
    ext ⟨θ, x⟩
    constructor
    · rintro ⟨p, hp, hx⟩
      exact ⟨((θ, x), ⟨p, hp⟩), hx, rfl⟩
    · rintro ⟨⟨⟨θ', x'⟩, ⟨p, hp⟩⟩, hz, hEq⟩
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      exact ⟨p, hp, hz⟩
  rw [hS]
  exact isClosedMap_fst_of_compactSpace _ hT

theorem measurable_projLength (n : ℕ) : Measurable (projLength n) := by
  have hS := (isClosed_setOf_mem_proj_image (isCompact_fourCorner n)).measurableSet
  exact (measurable_measure_prodMk_left (ν := volume) hS).ennreal_toReal

/-! ### Symmetries -/

theorem proj_pi_sub (θ : ℝ) (p : ℝ × ℝ) : proj (π - θ) p = proj θ (1 - p.1, p.2) - cos θ := by
  simp only [proj, cos_pi_sub, sin_pi_sub]
  ring

/-- Reflecting `x ↦ 1 - x` maps `K_n` to itself, so `π_θ(K_n)` is a translate of
`π_{π-θ}(K_n)`. -/
theorem proj_image_fourCorner_eq_add (n : ℕ) (θ : ℝ) :
    proj θ '' fourCorner n = (fun z => cos θ + z) '' (proj (π - θ) '' fourCorner n) := by
  rw [image_image]
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(1 - p.1, p.2), ⟨one_sub_mem_cantorApprox hp.1, hp.2⟩, ?_⟩
    rw [proj_pi_sub]
    simp only [sub_sub_cancel]
    ring
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(1 - p.1, p.2), ⟨one_sub_mem_cantorApprox hp.1, hp.2⟩, ?_⟩
    rw [proj_pi_sub]
    ring

theorem projLength_pi_sub (n : ℕ) (θ : ℝ) : projLength n (π - θ) = projLength n θ := by
  unfold projLength
  rw [proj_image_fourCorner_eq_add n θ, image_add_left, measure_preimage_add]

theorem proj_pi_div_two_sub (θ : ℝ) (p : ℝ × ℝ) : proj (π / 2 - θ) p = proj θ p.swap := by
  simp only [proj, cos_pi_div_two_sub, sin_pi_div_two_sub, Prod.fst_swap, Prod.snd_swap]
  ring

theorem projLength_pi_div_two_sub (n : ℕ) (θ : ℝ) :
    projLength n (π / 2 - θ) = projLength n θ := by
  unfold projLength
  rw [show proj (π / 2 - θ) = proj θ ∘ Prod.swap from funext (proj_pi_div_two_sub θ),
    image_comp, fourCorner, image_swap_prod]

end Favard.BasicProof
