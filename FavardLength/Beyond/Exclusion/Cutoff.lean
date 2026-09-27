import FavardLength.Beyond.Exclusion.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The smooth cutoff

Properties of `χ(x) = s(8x - 2) s(6 - 8x)` (Appendix G (9)): smoothness, `0 ≤ χ ≤ 1`,
`supp χ ⊆ (1/4, 3/4)`, `χ = 1` on `[3/8, 5/8]`, every derivative supported in `[1/4, 3/4]`,
continuous, integrable, and uniformly bounded up to any fixed order; and the Taylor expansion of
`χ` with a uniform Lagrange remainder (used in Appendix G (14)–(15)), and the decay
`|χ̂(w)| ≤ C_J |w|^{-J}` of its Fourier transform (Appendix G (19)).
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

lemma contDiff_cutoff {n : ℕ∞} : ContDiff ℝ n cutoff := by
  unfold cutoff
  have h1 : ContDiff ℝ n fun x : ℝ => Real.smoothTransition (8 * x - 2) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have h2 : ContDiff ℝ n fun x : ℝ => Real.smoothTransition (6 - 8 * x) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact h1.mul h2

lemma continuous_cutoff : Continuous cutoff :=
  (contDiff_cutoff (n := 0)).continuous

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 :=
  calc cutoff x ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma cutoff_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 4) : cutoff x = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma cutoff_eq_zero_of_ge {x : ℝ} (hx : 3 / 4 ≤ x) : cutoff x = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (x := 6 - 8 * x) (by linarith), mul_zero]

/-- The plateau: `χ = 1` on `[3/8, 5/8]`. -/
lemma cutoff_eq_one {x : ℝ} (hx : x ∈ Icc (3 / 8 : ℝ) (5 / 8)) : cutoff x = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le (by linarith [hx.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2]), one_mul]

lemma support_cutoff_subset : Function.support cutoff ⊆ Ioo (1 / 4 : ℝ) (3 / 4) := by
  intro x hx
  by_contra h
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact hx (cutoff_eq_zero_of_le h)
  · exact hx (cutoff_eq_zero_of_ge h)

/-- Every derivative of `χ` is supported in `[1/4, 3/4]`. -/
lemma support_iteratedDeriv_cutoff_subset (j : ℕ) :
    Function.support (iteratedDeriv j cutoff) ⊆ Icc (1 / 4 : ℝ) (3 / 4) := by
  induction j with
  | zero => rw [iteratedDeriv_zero]; exact support_cutoff_subset.trans Ioo_subset_Icc_self
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (support_deriv_subset).trans (closure_minimal ih isClosed_Icc)

lemma iteratedDeriv_cutoff_eq_zero (j : ℕ) {x : ℝ} (hx : x ∉ Icc (1 / 4 : ℝ) (3 / 4)) :
    iteratedDeriv j cutoff x = 0 :=
  Function.notMem_support.mp fun h => hx (support_iteratedDeriv_cutoff_subset j h)

lemma hasCompactSupport_iteratedDeriv_cutoff (j : ℕ) :
    HasCompactSupport (iteratedDeriv j cutoff) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => iteratedDeriv_cutoff_eq_zero j hx

lemma hasCompactSupport_cutoff : HasCompactSupport cutoff := by
  simpa using hasCompactSupport_iteratedDeriv_cutoff 0

lemma continuous_iteratedDeriv_cutoff (j : ℕ) : Continuous (iteratedDeriv j cutoff) :=
  (contDiff_cutoff (n := ⊤)).continuous_iteratedDeriv j (by exact_mod_cast le_top)

lemma integrable_iteratedDeriv_cutoff (j : ℕ) : Integrable (iteratedDeriv j cutoff) :=
  (continuous_iteratedDeriv_cutoff j).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_cutoff j)

/-- Uniform bounds for the derivatives of `χ` up to a fixed order. -/
lemma exists_bound_iteratedDeriv_cutoff (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ J, ∀ x, |iteratedDeriv j cutoff x| ≤ C := by
  have h : ∀ j, ∃ C : ℝ, ∀ x, ‖iteratedDeriv j cutoff x‖ ≤ C := fun j =>
    (continuous_iteratedDeriv_cutoff j).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv_cutoff j)
  choose C hC using h
  refine ⟨1 + ∑ j ∈ Finset.range (J + 1), |C j|, by positivity, fun j hj x => ?_⟩
  calc |iteratedDeriv j cutoff x| ≤ |C j| := (hC j x).trans (le_abs_self _)
    _ ≤ ∑ j ∈ Finset.range (J + 1), |C j| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_range.2 (by omega))
    _ ≤ 1 + ∑ j ∈ Finset.range (J + 1), |C j| := le_add_of_nonneg_left zero_le_one

open scoped Nat in
/-- **Taylor expansion of the cutoff** with a uniform remainder (Appendix G (14)–(15)):
`|χ(u + s) - ∑_{j ≤ J} χ^{(j)}(u) s^j / j!| ≤ C |s|^{J+1}` for all real `u, s`. -/
lemma cutoff_taylor (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u s : ℝ,
      |cutoff (u + s) - ∑ j ∈ Finset.range (J + 1), iteratedDeriv j cutoff u * s ^ j / j !| ≤
        C * |s| ^ (J + 1) := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_iteratedDeriv_cutoff (J + 1)
  refine ⟨C, hC, fun u s => ?_⟩
  rcases eq_or_ne s 0 with rfl | hs
  · rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [zero_pow hj])
      (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos J)) h)]
    simp
  have hne : u ≠ u + s := by intro h; exact hs (by linarith)
  obtain ⟨x', -, hx'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := cutoff) (n := J) hne
    ((contDiff_cutoff (n := ⊤)).contDiffOn.of_le (by exact_mod_cast le_top))
  have htay : taylorWithinEval cutoff J (uIcc u (u + s)) u (u + s) =
      ∑ j ∈ Finset.range (J + 1), iteratedDeriv j cutoff u * s ^ j / j ! := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((contDiff_cutoff (n := ⊤)).contDiffAt.of_le (by exact_mod_cast le_top)) left_mem_uIcc,
      smul_eq_mul, add_sub_cancel_left]
    ring
  rw [← htay, hx', add_sub_cancel_left, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hfac : (1 : ℝ) ≤ ((J + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (J + 1)
  calc |iteratedDeriv (J + 1) cutoff x'| * |s| ^ (J + 1) / ((J + 1)! : ℝ)
      ≤ |iteratedDeriv (J + 1) cutoff x'| * |s| ^ (J + 1) / 1 := by
        gcongr
    _ ≤ C * |s| ^ (J + 1) := by
        rw [div_one]
        gcongr
        exact hbd (J + 1) le_rfl x'

/-- The derivatives of the complexified cutoff are the complexified derivatives. -/
lemma iteratedDeriv_ofReal_cutoff (j : ℕ) :
    iteratedDeriv j (fun x => (cutoff x : ℂ)) = fun x => ((iteratedDeriv j cutoff x : ℝ) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv j cutoff) x :=
      ((contDiff_cutoff (n := ⊤)).differentiable_iteratedDeriv j
        (by exact_mod_cast WithTop.coe_lt_top _)) x
    exact (hd.hasDerivAt.ofReal_comp).deriv

open scoped FourierTransform in
/-- **Fourier decay of the cutoff** (Appendix G (19)): `‖χ̂(w)‖ ≤ C_J / |w|^J` for `w ≠ 0`,
with Mathlib's normalization `χ̂(w) = ∫ e^{-2πixw} χ(x) dx`. -/
lemma norm_fourier_cutoff_le (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, w ≠ 0 → ‖𝓕 (fun x => (cutoff x : ℂ)) w‖ ≤ C / |w| ^ J := by
  set g : ℝ → ℂ := fun x => (cutoff x : ℂ) with hg
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp contDiff_cutoff
  have hint : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n g) := fun n _ => by
    rw [hg, iteratedDeriv_ofReal_cutoff]
    exact (integrable_iteratedDeriv_cutoff n).ofReal
  have hF := Real.fourier_iteratedDeriv hgc hint (n := J) (by exact_mod_cast le_top)
  set C : ℝ := ∫ x, |iteratedDeriv J cutoff x| with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => abs_nonneg _
  refine ⟨C + 1, by positivity, fun w hw => ?_⟩
  have hbound : ‖𝓕 (iteratedDeriv J g) w‖ ≤ C := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hC]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg, iteratedDeriv_ofReal_cutoff, smul_eq_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖2 * π * Complex.I * (w : ℂ)‖ = 2 * π * |w| := by
    simp [Complex.norm_real, abs_of_pos pi_pos]
  rw [hF] at hbound
  simp only [smul_eq_mul] at hbound
  rw [norm_mul, norm_pow, hnorm] at hbound
  have hw0 : 0 < |w| := abs_pos.2 hw
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have hpow : |w| ^ J ≤ (2 * π * |w|) ^ J := by
    gcongr
    nlinarith
  rw [le_div_iff₀ (pow_pos hw0 J)]
  calc ‖𝓕 g w‖ * |w| ^ J ≤ ‖𝓕 g w‖ * (2 * π * |w|) ^ J := by gcongr
    _ = (2 * π * |w|) ^ J * ‖𝓕 g w‖ := by ring
    _ ≤ C := hbound
    _ ≤ C + 1 := by linarith

end Favard.Exclusion
