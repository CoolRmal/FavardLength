import FavardLength.Beyond.Exclusion.Density
import FavardLength.Beyond.Exclusion.Statements

/-!
# Martingale cell selection

We prove `Favard.Exclusion.cellSelection : CellSelectionStatement`, the martingale cell
selection (d1) of Appendix D (1)–(3) of `references/beyond/favard-beyond-quarter-complete.md`,
in a finite-sum form that needs no conditional-expectation API.

Let `f` be integrable with `f²` integrable, vanishing outside the root interval
`[-ρ/2, ρ/2] = [-4/3, 4/3]` (`ρ = 8/3`), with `∫ f = 1` and `∫ f² ≤ H`. Write `ℓ_j = ρ 4^{-j}`
for the length of a level-`j` cell `[cellLeft j i, cellLeft j (i+1)]`, `m_{j,i}` for its mass
and `E_j = ∑_i m_{j,i}²/ℓ_j` for the energy of the level-`j` conditional expectation.

* `E_j ≤ ∫ f² ≤ H` (Cauchy–Schwarz on every cell, `CellSelection.levelEnergy_le`).
* **Pythagoras**: `E_{j+L} - E_j = ∑_i V_i`, where
  `V_i = ∑_{c < 4^L} (m_{j+L, 4^L i + c} - a_i ℓ_{j+L})²/ℓ_{j+L}` and `a_i = m_{j,i}/ℓ_j`
  (`CellSelection.levelEnergy_add_sub`).
* **Block selection**: the `K + 1` blocks `[kL, (k+1)L]`, `k ≤ K = ⌊N/(2L)⌋`, telescope to at
  most `H`, so one of them has increment `D ≤ H/(K+1) ≤ 2HL/N`, and its level `j = kL` has
  `2j ≤ N`.
* **Good cells**: cells with `a_i < 3/32 = 1/(4ρ)` carry mass at most `1/4`, and cells with
  `a_i > 12H` carry mass at most `E_j/(12H) ≤ 1/12` (Markov); so the good cells, with
  `3/32 ≤ a_i ≤ 12H`, carry mass at least `2/3` and coarse energy `∑ a_i² ℓ_j ≥ 1/16`. Hence
  some good cell has `V_i ≤ 16 D a_i² ℓ_j ≤ 32 (HL/N) a_i² ℓ_j`, which is stronger than the
  contract's `(512/3)(HL/N) a_i² ℓ_j`.

The neighbour condition of Appendix D (2) is not needed: the direct Markov bound on `a_i` gives
`a_i ≤ 12H`.
-/

open MeasureTheory Set Real

namespace Favard.Exclusion

namespace CellSelection

/-! ### Four-adic cells of the root interval -/

lemma cellLeft_succ (j i : ℕ) : cellLeft j (i + 1) = cellLeft j i + 8 / 3 / 4 ^ j := by
  unfold cellLeft
  push_cast
  ring

lemma cellLeft_le_succ (j i : ℕ) : cellLeft j i ≤ cellLeft j (i + 1) := by
  rw [cellLeft_succ]
  linarith [show (0 : ℝ) < 8 / 3 / 4 ^ j by positivity]

lemma cellLeft_zero (j : ℕ) : cellLeft j 0 = -(4 / 3) := by
  simp [cellLeft]

lemma cellLeft_pow (j : ℕ) : cellLeft j (4 ^ j) = 4 / 3 := by
  unfold cellLeft
  push_cast
  field_simp
  ring

/-- The `c`-th level-`(j+L)` sub-cell of the level-`j` cell `i` starts at
`cellLeft j i + c ρ4^{-(j+L)}`. -/
lemma cellLeft_refine (j L i c : ℕ) :
    cellLeft (j + L) (4 ^ L * i + c) = cellLeft j i + c * (8 / 3 / 4 ^ (j + L)) := by
  unfold cellLeft
  push_cast
  rw [pow_add]
  field_simp
  ring

lemma cellLeft_refine_pow (j L i : ℕ) :
    cellLeft (j + L) (4 ^ L * i + 4 ^ L) = cellLeft j (i + 1) := by
  rw [cellLeft_refine, cellLeft_succ, pow_add]
  push_cast
  field_simp

/-! ### Cell masses and level energies -/

/-- The mass `m_{j,i} = ∫_{I_{j,i}} f` of the level-`j` cell `i`. -/
noncomputable def cellMass (f : ℝ → ℝ) (j i : ℕ) : ℝ :=
  ∫ y in cellLeft j i..cellLeft j (i + 1), f y

/-- The energy `E_j = ∑_i m_{j,i}²/ℓ_j` of the level-`j` conditional expectation. -/
noncomputable def levelEnergy (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (4 ^ j), cellMass f j i ^ 2 / (8 / 3 / 4 ^ j)

variable {f : ℝ → ℝ}

lemma levelEnergy_nonneg (j : ℕ) : 0 ≤ levelEnergy f j :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- A level-`j` cell mass is the sum of the masses of its `4^L` level-`(j+L)` sub-cells. -/
lemma cellMass_eq_sum (hf : Integrable f) (j L i : ℕ) :
    cellMass f j i = ∑ c ∈ Finset.range (4 ^ L), cellMass f (j + L) (4 ^ L * i + c) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun c => cellLeft (j + L) (4 ^ L * i + c)) (n := 4 ^ L)
    (fun k _ => hf.intervalIntegrable)
  have h0 : cellLeft (j + L) (4 ^ L * i) = cellLeft j i := by
    simpa using cellLeft_refine j L i 0
  simp only [add_zero, cellLeft_refine_pow, h0] at h
  exact h.symm

/-- The level-`j` cell masses add up to the total mass. -/
lemma sum_cellMass (hf : Integrable f) (hsupp : ∀ x, x ∉ Icc (-(4 / 3) : ℝ) (4 / 3) → f x = 0)
    (j : ℕ) : ∑ i ∈ Finset.range (4 ^ j), cellMass f j i = ∫ x, f x := by
  unfold cellMass
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf.intervalIntegrable),
    cellLeft_zero, cellLeft_pow, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]

/-- **Cauchy–Schwarz on an interval**: `(∫_a^b f)² ≤ (b - a) ∫_a^b f²`. -/
lemma sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set m := ∫ x in a..b, f x
  set c := m / (b - a)
  have h0 : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hexp : ∫ x in a..b, (f x - c) ^ 2 =
      (∫ x in a..b, f x ^ 2) - 2 * c * m + c ^ 2 * (b - a) := by
    have e : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
      ext x
      ring
    rw [e, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hba : 0 < b - a := sub_pos.2 hlt
  rw [hexp] at h0
  have key : (b - a) * (∫ x in a..b, f x ^ 2) - m ^ 2 =
      (b - a) * ((∫ x in a..b, f x ^ 2) - 2 * c * m + c ^ 2 * (b - a)) := by
    simp only [c]
    field_simp
    ring
  nlinarith [mul_nonneg hba.le h0]

/-- **Energy bound**: `E_j ≤ ∫ f²`. -/
lemma levelEnergy_le (hf : Integrable f) (hf2 : Integrable fun x => f x ^ 2) (j : ℕ) :
    levelEnergy f j ≤ ∫ x, f x ^ 2 := by
  have hℓ : (0 : ℝ) < 8 / 3 / 4 ^ j := by positivity
  calc levelEnergy f j
      ≤ ∑ i ∈ Finset.range (4 ^ j), ∫ x in cellLeft j i..cellLeft j (i + 1), f x ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := sq_intervalIntegral_le (cellLeft_le_succ j i) hf.intervalIntegrable
          hf2.intervalIntegrable
        have hlen : cellLeft j (i + 1) - cellLeft j i = 8 / 3 / 4 ^ j := by
          rw [cellLeft_succ]
          ring
        rw [hlen] at h
        rw [div_le_iff₀ hℓ, mul_comm]
        exact h
    _ = ∫ x in (-(4 / 3) : ℝ)..(4 / 3), f x ^ 2 := by
        rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf2.intervalIntegrable),
          cellLeft_zero, cellLeft_pow]
    _ ≤ ∫ x, f x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
        exact setIntegral_le_integral hf2 (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-! ### Pythagoras within the cells -/

/-- Regrouping `range (m n)` into `n` consecutive blocks of length `m`. -/
lemma sum_range_mul (g : ℕ → ℝ) (m n : ℕ) :
    ∑ k ∈ Finset.range (m * n), g k =
      ∑ i ∈ Finset.range n, ∑ c ∈ Finset.range m, g (m * i + c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **Pythagoras for one cell**: splitting a mass `S = ∑_{c<K} M_c` evenly over `K` sub-cells
of length `ℓ'`, `∑_c (M_c - S/(Kℓ') ℓ')²/ℓ' = ∑_c M_c²/ℓ' - S²/(Kℓ')`. -/
lemma sum_sq_sub_mean (M : ℕ → ℝ) (K : ℕ) (hK : 0 < K) {ℓ ℓ' : ℝ} (hℓ' : 0 < ℓ')
    (hℓ : ℓ = K * ℓ') :
    ∑ c ∈ Finset.range K, (M c - (∑ c ∈ Finset.range K, M c) / ℓ * ℓ') ^ 2 / ℓ' =
      ∑ c ∈ Finset.range K, M c ^ 2 / ℓ' - (∑ c ∈ Finset.range K, M c) ^ 2 / ℓ := by
  set S := ∑ c ∈ Finset.range K, M c
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have e : ∀ c, (M c - S / ℓ * ℓ') ^ 2 / ℓ' =
      M c ^ 2 / ℓ' + (-(2 * S / ℓ) * M c + S ^ 2 / ℓ ^ 2 * ℓ') := by
    intro c
    rw [hℓ]
    field_simp
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hℓ]
  field_simp
  ring

/-- The **relative block variance** `V_i = ∑_c (m_{j+L, 4^L i + c} - a_i ℓ_{j+L})²/ℓ_{j+L}` of
the level-`j` cell `i` at level `j + L`, with `a_i = m_{j,i}/ℓ_j`. -/
noncomputable def blockVar (f : ℝ → ℝ) (j L i : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (4 ^ L),
    (cellMass f (j + L) (4 ^ L * i + c) - cellMass f j i / (8 / 3 / 4 ^ j) *
      (8 / 3 / 4 ^ (j + L))) ^ 2 / (8 / 3 / 4 ^ (j + L))

lemma blockVar_nonneg (j L i : ℕ) : 0 ≤ blockVar f j L i :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **Orthogonality of martingale increments**: `E_{j+L} - E_j = ∑_i V_i`. -/
lemma levelEnergy_add_sub (hf : Integrable f) (j L : ℕ) :
    levelEnergy f (j + L) - levelEnergy f j =
      ∑ i ∈ Finset.range (4 ^ j), blockVar f j L i := by
  have hℓ' : (0 : ℝ) < 8 / 3 / 4 ^ (j + L) := by positivity
  have hℓ : (8 / 3 / 4 ^ j : ℝ) = ((4 ^ L : ℕ) : ℝ) * (8 / 3 / 4 ^ (j + L)) := by
    push_cast
    rw [pow_add]
    field_simp
  unfold levelEnergy
  rw [show (4 : ℕ) ^ (j + L) = 4 ^ L * 4 ^ j by rw [pow_add, mul_comm], sum_range_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold blockVar
  rw [cellMass_eq_sum hf j L i]
  exact (sum_sq_sub_mean _ _ (by positivity) hℓ' hℓ).symm

/-! ### Selection of a block and of a good cell -/

/-- **Block selection**: if `0 ≤ e 0` and `e ≤ H`, one of the `K + 1` increments
`e (k+1) - e k`, `k ≤ K`, is at most `H/(K+1)`. -/
lemma exists_increment_le (e : ℕ → ℝ) {H : ℝ} (h0 : 0 ≤ e 0) (hle : ∀ n, e n ≤ H) (K : ℕ) :
    ∃ k ∈ Finset.range (K + 1), e (k + 1) - e k ≤ H / (K + 1) := by
  refine Finset.exists_le_of_sum_le (f := fun k => e (k + 1) - e k) (g := fun _ => H / (K + 1))
    Finset.nonempty_range_add_one ?_
  rw [Finset.sum_range_sub, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  rw [mul_div_cancel₀ _ (by positivity)]
  linarith [hle (K + 1)]

/-- **Good cells** (Appendix D (1), (6)): if masses `m_i` on `#s` cells of length `ℓ`,
`#s ℓ = ρ`, have total `1` and energy `∑ m_i²/ℓ ≤ H`, then the cells with average
`3/32 ≤ m_i/ℓ ≤ 12H` carry coarse energy at least `1/16`. Cells with average below
`3/32 = 1/(4ρ)` carry mass at most `1/4`, and cells with average above `12H` carry mass at most
`1/12` by Markov's inequality. -/
lemma one_div_sixteen_le_sum_good {ι : Type*} (s : Finset ι) (m : ι → ℝ) {ℓ H : ℝ}
    (hℓ : 0 < ℓ) (hH : 0 < H) (hcard : (s.card : ℝ) * ℓ = 8 / 3) (hmass : ∑ i ∈ s, m i = 1)
    (hE : ∑ i ∈ s, m i ^ 2 / ℓ ≤ H) :
    1 / 16 ≤ ∑ i ∈ s.filter (fun i => 3 / 32 ≤ m i / ℓ ∧ m i / ℓ ≤ 12 * H), m i ^ 2 / ℓ := by
  set p : ι → Prop := fun i => 3 / 32 ≤ m i / ℓ ∧ m i / ℓ ≤ 12 * H
  have hpt : ∀ i, m i ≤ (if p i then m i else 0) + 3 / 32 * ℓ + m i ^ 2 / ℓ / (12 * H) := by
    intro i
    have hq : 0 ≤ m i ^ 2 / ℓ / (12 * H) := by positivity
    have hc : 0 ≤ 3 / 32 * ℓ := by positivity
    by_cases hp : p i
    · simp only [hp, ↓reduceIte]
      linarith
    · simp only [hp, ↓reduceIte]
      simp only [p, not_and_or, not_le] at hp
      rcases hp with h | h
      · rw [div_lt_iff₀ hℓ] at h
        linarith
      · rw [lt_div_iff₀ hℓ] at h
        have hm : 0 < m i := lt_trans (by positivity) h
        have : m i ≤ m i ^ 2 / ℓ / (12 * H) := by
          rw [le_div_iff₀ (by positivity), le_div_iff₀ hℓ]
          nlinarith
        linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ s) => hpt i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, ← Finset.sum_div, hmass] at hsum
  have h1 : (∑ i ∈ s, m i ^ 2 / ℓ) / (12 * H) ≤ 1 / 12 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h2 : (s.card : ℝ) * (3 / 32 * ℓ) = 1 / 4 := by
    rw [mul_left_comm, hcard]
    norm_num
  have hgood : 2 / 3 ≤ ∑ i ∈ s.filter p, m i := by linarith
  calc (1 / 16 : ℝ) = 3 / 32 * (2 / 3) := by norm_num
    _ ≤ 3 / 32 * ∑ i ∈ s.filter p, m i := by gcongr
    _ = ∑ i ∈ s.filter p, 3 / 32 * m i := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s.filter p, m i ^ 2 / ℓ := Finset.sum_le_sum fun i hi => by
        have h3 := ((Finset.mem_filter.1 hi).2).1
        have hm : 0 ≤ m i := by
          have := mul_le_mul_of_nonneg_right h3 hℓ.le
          rw [div_mul_cancel₀ _ hℓ.ne'] at this
          linarith
        rw [show m i ^ 2 / ℓ = m i / ℓ * m i by ring]
        exact mul_le_mul_of_nonneg_right h3 hm

/-- **Selection of a cell**: if the nonnegative variances `V_i` sum to at most `B` and the good
cells carry weight `∑_G w_i ≥ 1/16`, some good cell has `V_i ≤ 16 B w_i`. -/
lemma exists_le_mul_of_sum_le {ι : Type*} {s G : Finset ι} (hG : G ⊆ s) {V w : ι → ℝ}
    (hV : ∀ i ∈ s, 0 ≤ V i) {B : ℝ} (hB : 0 ≤ B) (hsum : ∑ i ∈ s, V i ≤ B)
    (hw : 1 / 16 ≤ ∑ i ∈ G, w i) : ∃ i ∈ G, V i ≤ 16 * B * w i := by
  have hne : G.Nonempty := by
    rcases G.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hw
      norm_num at hw
    · exact h
  refine Finset.exists_le_of_sum_le (f := V) (g := fun i => 16 * B * w i) hne ?_
  calc ∑ i ∈ G, V i ≤ ∑ i ∈ s, V i :=
        Finset.sum_le_sum_of_subset_of_nonneg hG fun i hi _ => hV i hi
    _ ≤ B := hsum
    _ = 16 * B * (1 / 16) := by ring
    _ ≤ 16 * B * ∑ i ∈ G, w i := by gcongr
    _ = ∑ i ∈ G, 16 * B * w i := Finset.mul_sum _ _ _

/-- **Martingale cell selection for a general density** (Appendix D (1)–(3)): if `f` and `f²`
are integrable, `f` vanishes outside `[-4/3, 4/3]`, `∫ f = 1` and `∫ f² ≤ H`, then for
`N ≥ 16L` some level-`j` cell `i` with `2j ≤ N` has average `0 < a ≤ 12H` and relative block
variance at level `j + L` at most `64ρHL/N`. -/
theorem exists_cell (hf : Integrable f) (hf2 : Integrable fun x => f x ^ 2)
    (hsupp : ∀ x, x ∉ Icc (-(4 / 3) : ℝ) (4 / 3) → f x = 0) (hmass : ∫ x, f x = 1) {H : ℝ}
    (hH : 0 < H) (hE : ∫ x, f x ^ 2 ≤ H) {N L : ℕ} (hL : 1 ≤ L) (hN : 16 * L ≤ N) :
    ∃ (j i : ℕ) (a : ℝ), 2 * j ≤ N ∧ i < 4 ^ j ∧ cellMass f j i = a * (8 / 3 / 4 ^ j) ∧
      0 < a ∧ a ≤ 12 * H ∧
      ∑ c ∈ Finset.range (4 ^ L),
          (cellMass f (j + L) (4 ^ L * i + c) - a * (8 / 3 / 4 ^ (j + L))) ^ 2 ≤
        512 / 3 * H * L / N * a ^ 2 * (8 / 3 / 4 ^ j) * (8 / 3 / 4 ^ (j + L)) := by
  have hEle : ∀ j, levelEnergy f j ≤ H := fun j => (levelEnergy_le hf hf2 j).trans hE
  -- block selection among the levels `kL`, `k ≤ K = ⌊N/(2L)⌋`
  set K := N / (2 * L) with hK
  obtain ⟨k, hk, hD⟩ := exists_increment_le (fun k => levelEnergy f (k * L))
    (levelEnergy_nonneg _) (fun n => hEle _) K
  simp only [add_one_mul] at hD
  set j := k * L with hj
  have h2j : 2 * j ≤ N := by
    have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    calc 2 * j = k * (2 * L) := by rw [hj]; ring
      _ ≤ K * (2 * L) := Nat.mul_le_mul_right _ hkK
      _ ≤ N := Nat.div_mul_le_self N (2 * L)
  have hNK : (N : ℝ) ≤ (2 * L) * (K + 1) := by
    have := Nat.lt_mul_div_succ N (show 0 < 2 * L by omega)
    exact_mod_cast this.le
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set B := H / (K + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBle : B ≤ 2 * H * L / N := by
    rw [hB, div_le_div_iff₀ (by positivity) hNpos]
    nlinarith
  -- good cells at level `j`
  set ℓ : ℝ := 8 / 3 / 4 ^ j with hℓdef
  set ℓ' : ℝ := 8 / 3 / 4 ^ (j + L) with hℓ'def
  have hℓ : 0 < ℓ := by positivity
  have hℓ' : 0 < ℓ' := by positivity
  have hgood := one_div_sixteen_le_sum_good (Finset.range (4 ^ j)) (cellMass f j) hℓ hH
    (by rw [Finset.card_range, hℓdef]; push_cast; field_simp)
    ((sum_cellMass hf hsupp j).trans hmass) (hEle j)
  obtain ⟨i, hiG, hVi⟩ := exists_le_mul_of_sum_le (Finset.filter_subset _ _)
    (V := blockVar f j L) (fun i _ => blockVar_nonneg j L i) hB0
    ((levelEnergy_add_sub hf j L).symm.le.trans hD) hgood
  obtain ⟨hi, ha1, ha2⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hiG
  set a := cellMass f j i / ℓ with ha
  refine ⟨j, i, a, h2j, hi, by rw [ha, div_mul_cancel₀ _ hℓ.ne'], by linarith, ha2, ?_⟩
  have hsum : ∑ c ∈ Finset.range (4 ^ L),
      (cellMass f (j + L) (4 ^ L * i + c) - a * ℓ') ^ 2 = blockVar f j L i * ℓ' := by
    unfold blockVar
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [div_mul_cancel₀ _ hℓ'.ne']
  have hw : cellMass f j i ^ 2 / ℓ = a ^ 2 * ℓ := by
    rw [ha]
    field_simp
  rw [hsum]
  have hX : 0 ≤ H * L / N * (a ^ 2 * ℓ * ℓ') := by positivity
  calc blockVar f j L i * ℓ' ≤ 16 * B * (a ^ 2 * ℓ) * ℓ' := by
        rw [← hw]
        exact mul_le_mul_of_nonneg_right hVi hℓ'.le
    _ ≤ 16 * (2 * H * L / N) * (a ^ 2 * ℓ) * ℓ' := by gcongr
    _ = 32 * (H * L / N * (a ^ 2 * ℓ * ℓ')) := by ring
    _ ≤ 512 / 3 * (H * L / N * (a ^ 2 * ℓ * ℓ')) := by linarith
    _ = 512 / 3 * H * L / N * a ^ 2 * ℓ * ℓ' := by ring

end CellSelection

open CellSelection in
/-- **(d1) Martingale cell selection** (Appendix D (1)–(3)). -/
theorem cellSelection : CellSelectionStatement := by
  intro H t N L hH ht hL hN hE
  have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have hf := integrable_tailDensity N t
  have hf2 : Integrable fun x => tailDensity N t x ^ 2 := by
    refine (hf.const_mul (3 / 8 * 4 ^ N)).mono' (hf.aestronglyMeasurable.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right (tailDensity_le N t x) (tailDensity_nonneg N t x)
  have hsupp : ∀ x, x ∉ Icc (-(4 / 3) : ℝ) (4 / 3) → tailDensity N t x = 0 :=
    fun x hx => Function.notMem_support.1 fun h => hx (support_tailDensity_subset ht' N h)
  exact exists_cell hf hf2 hsupp (integral_tailDensity N t) hH
    ((integral_tailDensity_sq N t).trans_le hE) hL hN

end Favard.Exclusion
