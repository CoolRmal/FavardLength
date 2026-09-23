import FavardLength.Squares
import FavardLength.BasicProof.All
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Basic facts about the four-corner approximants and their projections

Gate-0 sanity checks (generation zero is the unit square, generation one has the four intended
corner squares), the square decomposition of `K_n`, projections of squares, measurability and
boundedness of the projection length, nesting, the symmetry reduction of the Favard integral to
`[0, π/4]`, and the overlap formula for the energy.
-/

open MeasureTheory Set Real

namespace Favard

/-! ### Sanity checks of the Challenge definitions -/

theorem cantorApprox_zero : cantorApprox 0 = Icc 0 1 :=
  BasicProof.cantorApprox_zero

theorem cantorApprox_one : cantorApprox 1 = Icc 0 (1 / 4) ∪ Icc (3 / 4) 1 :=
  BasicProof.cantorApprox_one

theorem fourCorner_zero : fourCorner 0 = Icc 0 1 ×ˢ Icc 0 1 :=
  BasicProof.fourCorner_zero

/-! ### Square decomposition -/

theorem cantorApprox_eq_iUnion (n : ℕ) :
    cantorApprox n = ⋃ b : Fin n → Bool, Icc (leftEnd b) (leftEnd b + 1 / 4 ^ n) :=
  BasicProof.cantorApprox_eq_iUnion n

theorem fourCorner_eq_iUnion (n : ℕ) : fourCorner n = ⋃ w : SqCode n, square w :=
  BasicProof.fourCorner_eq_iUnion n

theorem fourCorner_subset (n : ℕ) : fourCorner n ⊆ Icc 0 1 ×ˢ Icc 0 1 :=
  BasicProof.fourCorner_subset n

/-- The approximants are nested. -/
theorem fourCorner_antitone {m n : ℕ} (h : m ≤ n) : fourCorner n ⊆ fourCorner m :=
  BasicProof.fourCorner_antitone h

theorem isCompact_fourCorner (n : ℕ) : IsCompact (fourCorner n) :=
  BasicProof.isCompact_fourCorner n

/-- For `θ ∈ [0, π/2]` the projection of a depth-`n` square is a closed interval of length
`(cos θ + sin θ) 4^{-n}` starting at the projection of the lower-left corner. -/
theorem proj_image_square {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) {n : ℕ} (w : SqCode n) :
    proj θ '' square w =
      Icc (proj θ (corner w)) (proj θ (corner w) + (cos θ + sin θ) / 4 ^ n) :=
  BasicProof.proj_image_square hθ w

theorem proj_image_fourCorner (θ : ℝ) (n : ℕ) :
    proj θ '' fourCorner n = ⋃ w : SqCode n, proj θ '' square w :=
  BasicProof.proj_image_fourCorner θ n

/-! ### The projection length -/

theorem volume_proj_image_fourCorner_ne_top (n : ℕ) (θ : ℝ) :
    volume (proj θ '' fourCorner n) ≠ ⊤ :=
  BasicProof.volume_proj_image_fourCorner_ne_top n θ

theorem projLength_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ projLength n θ :=
  BasicProof.projLength_nonneg n θ

theorem projLength_le_sqrt_two (n : ℕ) (θ : ℝ) : projLength n θ ≤ √2 :=
  BasicProof.projLength_le_sqrt_two n θ

theorem projLength_antitone {m n : ℕ} (h : m ≤ n) (θ : ℝ) :
    projLength n θ ≤ projLength m θ :=
  BasicProof.projLength_antitone h θ

theorem measurable_projLength (n : ℕ) : Measurable (projLength n) :=
  BasicProof.measurable_projLength n

theorem projLength_pi_sub (n : ℕ) (θ : ℝ) : projLength n (π - θ) = projLength n θ :=
  BasicProof.projLength_pi_sub n θ

theorem projLength_pi_div_two_sub (n : ℕ) (θ : ℝ) :
    projLength n (π / 2 - θ) = projLength n θ :=
  BasicProof.projLength_pi_div_two_sub n θ

/-- Symmetry reduction: `Fav(K_n) = (4/π) ∫_0^{π/4} λ(π_θ(K_n)) dθ`. -/
theorem favardLength_eq_quarter (n : ℕ) :
    favardLength n = 4 / π * ∫ θ in (0)..(π / 4), projLength n θ :=
  BasicProof.favardLength_eq_quarter n

theorem favardLength_nonneg (n : ℕ) : 0 ≤ favardLength n :=
  BasicProof.favardLength_nonneg n

theorem favardLength_le_sqrt_two (n : ℕ) : favardLength n ≤ √2 :=
  BasicProof.favardLength_le_sqrt_two n

/-! ### Multiplicity and energy -/

theorem count_le (n : ℕ) (θ x : ℝ) : count n θ x ≤ 4 ^ n :=
  BasicProof.count_le n θ x

theorem measurable_count (n : ℕ) (θ : ℝ) : Measurable (fun x => (count n θ x : ℝ)) :=
  BasicProof.measurable_count n θ

theorem integrable_count_sq (n : ℕ) (θ : ℝ) :
    Integrable (fun x => (count n θ x : ℝ) ^ 2) :=
  BasicProof.integrable_count_sq n θ

/-- For `θ ∈ [0, π/2]`, the total multiplicity mass is `σ = cos θ + sin θ`. -/
theorem integral_count {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    ∫ x, (count n θ x : ℝ) = cos θ + sin θ :=
  BasicProof.integral_count hθ n

/-- The energy is the sum over ordered pairs of squares of the overlaps of their projections. -/
theorem energy_eq_sum_overlap {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) (n : ℕ) :
    energy n θ = ∑ w : SqCode n, ∑ w' : SqCode n,
      max 0 ((cos θ + sin θ) / 4 ^ n - |proj θ (corner w) - proj θ (corner w')|) :=
  BasicProof.energy_eq_sum_overlap hθ n

theorem energy_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ energy n θ :=
  BasicProof.energy_nonneg n θ

end Favard
