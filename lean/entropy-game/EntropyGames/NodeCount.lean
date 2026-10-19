/-
Section 4 (Lemma 4.4) and Section 9 (Proposition 9.1) of the paper: the function `B`, the
bound `B₀ ≤ 2 + 6 log₂ n`, and the lower bound on the number of nodes of the recursion tree.
-/
import EntropyGames.Localisation

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

/-! ### The function `B` -/

theorem Bfun_set_nonempty {μ : ℚ} (hμ : 0 < μ) : {j : ℕ | 1 < (32 / 25 : ℚ) ^ j * μ}.Nonempty := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / μ) (show (1 : ℚ) < 32 / 25 by norm_num)
  refine ⟨j, ?_⟩
  rw [Set.mem_setOf_eq]
  rwa [div_lt_iff₀ hμ] at hj

theorem Bfun_spec {μ : ℚ} (hμ : 0 < μ) : 1 < (32 / 25 : ℚ) ^ Bfun μ * μ :=
  Nat.sInf_mem (Bfun_set_nonempty hμ)

theorem Bfun_le {μ : ℚ} {j : ℕ} (h : 1 < (32 / 25 : ℚ) ^ j * μ) : Bfun μ ≤ j :=
  Nat.sInf_le h

theorem Bfun_eq_zero {μ : ℚ} (h : 1 < μ) : Bfun μ = 0 :=
  Nat.le_zero.mp (Bfun_le (by simpa using h))

/-- Minimality: `ρ^j μ ≤ 1` for `j < B(μ)`. -/
theorem Bfun_min {μ : ℚ} {j : ℕ} (h : j < Bfun μ) : (32 / 25 : ℚ) ^ j * μ ≤ 1 := by
  by_contra hcon
  exact absurd (Bfun_le (not_le.mp hcon)) (not_le.mpr h)

section tree

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem LInput.mu_pos {I : LInput ι} (hI : I.Valid) : 0 < I.mu := by
  unfold LInput.mu
  rw [Finset.lt_inf'_iff]
  exact fun i _ => mul_pos (hI.a_pos i) (hI.b_pos i)

theorem LInput.B_eq_zero_of_massBase {I : LInput ι} (hm : I.massBase) : I.B = 0 := by
  apply Bfun_eq_zero
  unfold LInput.mu
  rw [Finset.lt_inf'_iff]
  exact fun i _ => hm i

theorem LInput.B_pos {I : LInput ι} (hI : I.Valid) (hm : ¬ I.massBase) : 1 ≤ I.B := by
  by_contra hcon
  have h0 : I.B = 0 := by omega
  have h1 := Bfun_spec (LInput.mu_pos hI)
  have h0' : Bfun I.mu = 0 := h0
  rw [h0', pow_zero, one_mul] at h1
  exact hm fun i => lt_of_lt_of_le h1 (Finset.inf'_le _ (Finset.mem_univ i))

theorem LInput.provCall_valid {I : LInput ι} (hI : I.Valid) (kf : ι → ℤ) :
    (I.provCall kf).Valid := ⟨hI.h_ge, hI.h_le, hI.a_pos, hI.b_pos⟩

theorem LInput.contCall_valid {I : LInput ι} (hI : I.Valid) (l0 : ι → Bool) :
    (I.contCall l0).Valid := by
  refine ⟨hI.h_ge, hI.h_le, fun i => ?_, fun i => ?_⟩
  · have := hI.a_pos i
    simp only [LInput.contCall]
    split_ifs <;> positivity
  · have := hI.b_pos i
    simp only [LInput.contCall]
    split_ifs <;> positivity

/-- The continuation multiplies all products `a_i b_i` by `ρ = 32/25`, so `B` decreases by at
most one. -/
theorem LInput.B_contCall {I : LInput ι} (hI : I.Valid) (l0 : ι → Bool) :
    I.B ≤ (I.contCall l0).B + 1 := by
  have h1 := Bfun_spec (LInput.mu_pos (LInput.contCall_valid hI l0))
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
    (fun i => I.a i * I.b i)
  have hle : (I.contCall l0).mu ≤ 32 / 25 * I.mu := by
    have h2 : (I.contCall l0).mu ≤ (I.contCall l0).a i0 * (I.contCall l0).b i0 :=
      Finset.inf'_le _ (Finset.mem_univ i0)
    refine h2.trans (le_of_eq ?_)
    unfold LInput.mu
    rw [hi0]
    simp only [LInput.contCall]
    split_ifs <;> ring
  apply Bfun_le
  have hpow : (0 : ℚ) < (32 / 25) ^ Bfun (I.contCall l0).mu := by positivity
  calc (1 : ℚ) < (32 / 25) ^ Bfun (I.contCall l0).mu * (I.contCall l0).mu := h1
    _ ≤ (32 / 25) ^ Bfun (I.contCall l0).mu * (32 / 25 * I.mu) :=
      mul_le_mul_of_nonneg_left hle hpow.le
    _ = (32 / 25) ^ ((I.contCall l0).B + 1) * I.mu := by
      unfold LInput.B; ring

/-- **Proposition 9.1, first sentence**: the recursion tree has at least `C(d - 11 + B, B)`
nodes when `d ≥ 11`. -/
theorem node_lower_bound {F : (ι → ℝ) → ι → ℝ} {I : LInput ι} (hI : I.Valid)
    (hd : 11 ≤ I.d) {l : ι → Bool} {n : ℕ} (hrun : Run F I l n) :
    Nat.choose (I.d - 11 + I.B) I.B ≤ n := by
  revert hI hd
  refine Run.rec (F := F)
    (motive_1 := fun I _ n _ => I.Valid → 11 ≤ I.d → Nat.choose (I.d - 11 + I.B) I.B ≤ n)
    (motive_2 := fun _ _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrun
  · intro I hm _ _
    rw [LInput.B_eq_zero_of_massBase hm, Nat.choose_zero_right]
  · intro I _ hd12 _ _ _ _ hd
    have : I.d - 11 = 0 := by omega
    rw [this, zero_add, Nat.choose_self]
  · intro I hm hd12 kdown kf l0 lc c1 c2 n1 n2 n3 n4 _ _ _ _ _ _ ih3 ih4 hI _
    have hB := LInput.B_pos hI hm
    have h3 := ih3 (LInput.provCall_valid hI kf) (show 11 ≤ I.d - 1 by omega)
    have h4 := ih4 (LInput.contCall_valid hI l0) (show 11 ≤ I.d by omega)
    have hBc := LInput.B_contCall hI l0
    have e3 : (I.provCall kf).B = I.B := rfl
    have ed3 : (I.provCall kf).d = I.d - 1 := rfl
    have ed4 : (I.contCall l0).d = I.d := rfl
    rw [e3, ed3] at h3
    rw [ed4] at h4
    obtain ⟨m, hm'⟩ : ∃ m, I.d = m + 12 := ⟨I.d - 12, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, I.B = b + 1 := ⟨I.B - 1, by omega⟩
    obtain ⟨B', hB'⟩ : ∃ B', B' = (I.contCall l0).B := ⟨_, rfl⟩
    rw [← hB'] at h4 hBc
    rw [hm', hb] at h3 ⊢
    rw [hm'] at h4
    rw [hb] at hBc
    have e1 : m + 12 - 11 + (b + 1) = (m + 1 + b) + 1 := by omega
    have e2 : m + 12 - 1 - 11 + (b + 1) = m + 1 + b := by omega
    have e4 : m + 12 - 11 + B' = m + 1 + B' := by omega
    rw [e1, Nat.choose_succ_succ']
    rw [e2] at h3
    rw [e4] at h4
    have h5 : Nat.choose (m + 1 + b) b ≤ Nat.choose (m + 1 + B') B' := by
      rw [← Nat.choose_symm_of_eq_add (rfl : m + 1 + b = (m + 1) + b),
        ← Nat.choose_symm_of_eq_add (rfl : m + 1 + B' = (m + 1) + B')]
      exact Nat.choose_le_choose _ (by omega)
    omega
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

end tree

/-! ### `B₀ = B(1/n²)` -/

theorem log_rho_bounds : Real.log 2 ≤ 3 * Real.log (32 / 25) ∧
    5 * Real.log (32 / 25) ≤ 2 * Real.log 2 ∧ 0 < Real.log (32 / 25) := by
  refine ⟨?_, ?_, Real.log_pos (by norm_num)⟩
  · rw [← Real.log_rpow (by norm_num) 3]
    exact Real.log_le_log (by norm_num) (by norm_num)
  · rw [← Real.log_rpow (by norm_num) 5, ← Real.log_rpow (by norm_num) 2]
    exact Real.log_le_log (by norm_num) (by norm_num)

/-- `ρ^j > n²` in terms of logarithms. -/
theorem one_lt_rho_pow_iff {n j : ℕ} (hn : 1 ≤ n) :
    1 < (32 / 25 : ℚ) ^ j * (1 / (n : ℚ) ^ 2) ↔ 2 * Real.log n < j * Real.log (32 / 25) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnq : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  rw [mul_one_div, lt_div_iff₀ hnq, one_mul]
  have e : ((n : ℚ) ^ 2 < (32 / 25 : ℚ) ^ j) ↔ ((n : ℝ) ^ 2 < (32 / 25 : ℝ) ^ j) := by
    constructor
    · intro h
      have : (((n : ℚ) ^ 2 : ℚ) : ℝ) < (((32 / 25 : ℚ) ^ j : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at this
      exact this
    · intro h
      have : (((n : ℚ) ^ 2 : ℚ) : ℝ) < (((32 / 25 : ℚ) ^ j : ℚ) : ℝ) := by
        push_cast
        exact h
      exact_mod_cast this
  rw [e, ← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  norm_num

/-- Lemma 4.4, the bound `B₀ = B(1/n²) ≤ 2 + 6 log₂ n` (for a natural number `n ≥ 1`). -/
theorem B0_le_nat {n : ℕ} (hn : 1 ≤ n) :
    (Bfun (1 / (n : ℚ) ^ 2) : ℝ) ≤ 2 + 6 * Real.logb 2 n := by
  obtain ⟨h1, _, h3⟩ := log_rho_bounds
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn'
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 n := ⟨_, rfl⟩
  have hLn : L * Real.log 2 = Real.log n := by
    rw [hL, Real.logb, div_mul_cancel₀ _ hlog2.ne']
  have hL0 : 0 ≤ L := by
    rw [hL]; exact div_nonneg hlogn hlog2.le
  rw [← hL]
  have hfl : 6 * L < (⌊6 * L⌋₊ + 1 : ℕ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hfl2 : ((⌊6 * L⌋₊ : ℕ) : ℝ) ≤ 6 * L := Nat.floor_le (by positivity)
  have hB : Bfun (1 / (n : ℚ) ^ 2) ≤ ⌊6 * L⌋₊ + 1 := by
    apply Bfun_le
    rw [one_lt_rho_pow_iff hn, ← hLn]
    have h4 : 6 * L * Real.log (32 / 25) < ((⌊6 * L⌋₊ + 1 : ℕ) : ℝ) * Real.log (32 / 25) :=
      mul_lt_mul_of_pos_right hfl h3
    have h5 : 2 * L * Real.log 2 ≤ 2 * L * (3 * Real.log (32 / 25)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith only [h4, h5]
  have hB' : (Bfun (1 / (n : ℚ) ^ 2) : ℝ) ≤ ((⌊6 * L⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hB
  push_cast at hB'
  linarith only [hB', hfl2]

/-- `B₀ > 5 log₂ n`. -/
theorem B0_gt_nat {n : ℕ} (hn : 1 ≤ n) :
    5 * Real.logb 2 n < (Bfun (1 / (n : ℚ) ^ 2) : ℝ) := by
  obtain ⟨_, h2, h3⟩ := log_rho_bounds
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn'
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 n := ⟨_, rfl⟩
  have hLn : L * Real.log 2 = Real.log n := by
    rw [hL, Real.logb, div_mul_cancel₀ _ hlog2.ne']
  have hL0 : 0 ≤ L := by
    rw [hL]; exact div_nonneg hlogn hlog2.le
  rw [← hL]
  have hspec := Bfun_spec (μ := 1 / (n : ℚ) ^ 2) (by positivity)
  rw [one_lt_rho_pow_iff hn, ← hLn] at hspec
  have h5 : L * (5 * Real.log (32 / 25)) ≤ L * (2 * Real.log 2) :=
    mul_le_mul_of_nonneg_left h2 hL0
  have h6 : 5 * L * Real.log (32 / 25) < (Bfun (1 / (n : ℚ) ^ 2) : ℝ) * Real.log (32 / 25) := by
    linarith only [hspec, h5]
  exact lt_of_mul_lt_mul_right h6 h3.le

/-- `(n/B)^B ≤ C(n + B, B)`. -/
theorem div_pow_le_choose (n B : ℕ) :
    ((n : ℝ) / B) ^ B ≤ (Nat.choose (n + B) B : ℝ) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  have h1 := Nat.pow_le_choose (α := ℝ) B (n + B)
  have e : n + B + 1 - B = n + 1 := by omega
  rw [e] at h1
  refine le_trans ?_ h1
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hfac : (0 : ℝ) < (B.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos B
  rw [div_pow, div_le_div_iff₀ (by positivity) hfac]
  have h2 : (B.factorial : ℝ) ≤ (B : ℝ) ^ B := by exact_mod_cast Nat.factorial_le_pow B
  have h3 : (n : ℝ) ^ B ≤ ((n + 1 : ℕ) : ℝ) ^ B :=
    pow_le_pow_left₀ (by positivity) (by push_cast; linarith) B
  calc (n : ℝ) ^ B * B.factorial ≤ ((n + 1 : ℕ) : ℝ) ^ B * (B : ℝ) ^ B :=
    mul_le_mul h3 h2 hfac.le (by positivity)

/-- Proposition 9.1, last sentence, for a natural number `n ≥ 2^7`. -/
theorem choose_lower_bound_nat {n : ℕ} (hn : 2 ^ 7 ≤ n) :
    ((n : ℝ) / (7 * Real.logb 2 n)) ^ (5 * Real.logb 2 n)
      ≤ Nat.choose (n + Bfun (1 / (n : ℚ) ^ 2)) (Bfun (1 / (n : ℚ) ^ 2)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn' : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' := Real.log_two_gt_d9
  have hup := B0_le_nat hn1
  have hlo := B0_gt_nat hn1
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 n := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Bfun (1 / (n : ℚ) ^ 2) := ⟨_, rfl⟩
  rw [← hL, ← hB] at hup hlo ⊢
  have hLn : L * Real.log 2 = Real.log n := by
    rw [hL, Real.logb, div_mul_cancel₀ _ hlog2.ne']
  -- `L ≥ 7`
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hL7 : 7 ≤ L := by
    have : Real.log 128 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
    rw [h128, ← hLn] at this
    exact le_of_mul_le_mul_right this hlog2
  -- `7 L < n`
  have h7L : 7 * L < n := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 128 by positivity)
    rw [Real.log_div (by positivity) (by norm_num), h128, ← hLn] at h1
    have h2 : 7 * L * Real.log 2 < n * Real.log 2 := by
      have h3 : (0 : ℝ) ≤ n / 128 - 1 := by
        rw [sub_nonneg, le_div_iff₀ (by norm_num)]; linarith
      have h4 : n * Real.log 2 = 128 * (n / 128 - 1) * Real.log 2 + 128 * Real.log 2 := by ring
      have h5 : 128 * (n / 128 - 1) * 0.6931471803 ≤ 128 * (n / 128 - 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2'.le (by positivity)
      have h6 := Real.log_two_lt_d9
      rw [h4]
      nlinarith only [h1, h3, h5, hlog2', h6]
    exact lt_of_mul_lt_mul_right h2 hlog2.le
  have hLpos : 0 < L := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hB7 : (B : ℝ) ≤ 7 * L := by linarith
  have hx1 : 1 ≤ (n : ℝ) / (7 * L) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ((n : ℝ) / (7 * L)) ^ (5 * L) ≤ ((n : ℝ) / (7 * L)) ^ (B : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hlo.le
    _ = ((n : ℝ) / (7 * L)) ^ B := Real.rpow_natCast _ _
    _ ≤ ((n : ℝ) / B) ^ B := by
        refine pow_le_pow_left₀ (by positivity) ?_ B
        exact div_le_div_of_nonneg_left (by positivity) hBpos hB7
    _ ≤ _ := div_pow_le_choose n B

section card

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Lemma 4.4, the bound `B₀ = B(1/n²) ≤ 2 + 6 log₂ n`.** -/
theorem B0_le : (Bfun (1 / (Fintype.card ι : ℚ) ^ 2) : ℝ)
    ≤ 2 + 6 * Real.logb 2 (Fintype.card ι) :=
  B0_le_nat Fintype.card_pos

/-- **Proposition 9.1, last sentence**: `C(n + B₀, B₀) ≥ (n / (7 log₂ n))^{5 log₂ n}` for
`n ≥ 2^7`, `B₀ = B(1/n²)`. -/
theorem choose_lower_bound (hn : 2 ^ 7 ≤ Fintype.card ι) :
    ((Fintype.card ι : ℝ) / (7 * Real.logb 2 (Fintype.card ι)))
        ^ (5 * Real.logb 2 (Fintype.card ι))
      ≤ Nat.choose (Fintype.card ι + Bfun (1 / (Fintype.card ι : ℚ) ^ 2))
          (Bfun (1 / (Fintype.card ι : ℚ) ^ 2)) :=
  choose_lower_bound_nat hn

end card

/-! ### Lemma 4.4: the node count -/

/-- `Σ_{k ≤ r} Σ_{j ≤ b} C(k, j) s^j`, the paper's bound for the number of nodes of a tree of
depth at most `r` with at most `b` edges that decrease `B` on every path (`C(k, j) = 0` for
`j > k`). -/
def Tsum (s r b : ℕ) : ℕ := ∑ k ∈ range (r + 1), ∑ j ∈ range (b + 1), Nat.choose k j * s ^ j

theorem one_le_Tsum (s r b : ℕ) : 1 ≤ Tsum s r b := by
  unfold Tsum
  have h1 : ∑ j ∈ range (b + 1), Nat.choose 0 j * s ^ j
      ≤ ∑ k ∈ range (r + 1), ∑ j ∈ range (b + 1), Nat.choose k j * s ^ j :=
    Finset.single_le_sum (f := fun k => ∑ j ∈ range (b + 1), Nat.choose k j * s ^ j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos r))
  have h2 : Nat.choose 0 0 * s ^ 0 ≤ ∑ j ∈ range (b + 1), Nat.choose 0 j * s ^ j :=
    Finset.single_le_sum (f := fun j => Nat.choose 0 j * s ^ j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos b))
  simp only [Nat.choose_self, pow_zero, mul_one] at h2
  exact h2.trans h1

theorem Tsum_mono (s : ℕ) {r r' b b' : ℕ} (hr : r ≤ r') (hb : b ≤ b') :
    Tsum s r b ≤ Tsum s r' b' := by
  unfold Tsum
  calc ∑ k ∈ range (r + 1), ∑ j ∈ range (b + 1), Nat.choose k j * s ^ j
      ≤ ∑ k ∈ range (r + 1), ∑ j ∈ range (b' + 1), Nat.choose k j * s ^ j :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset
          (f := fun j => Nat.choose k j * s ^ j) (Finset.range_mono (by omega))
    _ ≤ ∑ k ∈ range (r' + 1), ∑ j ∈ range (b' + 1), Nat.choose k j * s ^ j :=
        Finset.sum_le_sum_of_subset
          (f := fun k => ∑ j ∈ range (b' + 1), Nat.choose k j * s ^ j)
          (Finset.range_mono (by omega))

theorem sum_choose_col (r j : ℕ) : ∑ k ∈ range (r + 1), Nat.choose k j = Nat.choose (r + 1) (j + 1) := by
  induction r with
  | zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · simp [Nat.choose_eq_zero_of_lt hj, Nat.choose_eq_zero_of_lt (show 1 < j + 1 by omega)]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' (r + 1) j]
    omega

/-- The recurrence of the count: a node, its `B`-preserving child, and at most `s` other
children. -/
theorem Tsum_rec (s r b : ℕ) :
    1 + Tsum s r (b + 1) + s * Tsum s r b ≤ Tsum s (r + 1) (b + 1) := by
  have h1 : Tsum s (r + 1) (b + 1)
      = Tsum s r (b + 1) + ∑ j ∈ range (b + 1 + 1), Nat.choose (r + 1) j * s ^ j := by
    unfold Tsum
    rw [Finset.sum_range_succ]
  have h2 : ∑ j ∈ range (b + 1 + 1), Nat.choose (r + 1) j * s ^ j
      = ∑ j ∈ range (b + 1), Nat.choose (r + 1) (j + 1) * s ^ (j + 1) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  have h3 : s * Tsum s r b = ∑ j ∈ range (b + 1), Nat.choose (r + 1) (j + 1) * s ^ (j + 1) := by
    unfold Tsum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_choose_col, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1, h2, h3]
  omega

theorem Tsum_le (s : ℕ) {r : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (b : ℕ) :
    Tsum s r b ≤ (r + 1) * (b + 1) * (r * s) ^ b := by
  unfold Tsum
  have hrs : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hterm : ∀ k ∈ range (r + 1), ∀ j ∈ range (b + 1), Nat.choose k j * s ^ j ≤ (r * s) ^ b := by
    intro k hk j hj
    rw [Finset.mem_range] at hk hj
    calc Nat.choose k j * s ^ j ≤ k ^ j * s ^ j := Nat.mul_le_mul_right _ (Nat.choose_le_pow k j)
      _ ≤ r ^ j * s ^ j := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) j)
      _ = (r * s) ^ j := (Nat.mul_pow r s j).symm
      _ ≤ (r * s) ^ b := Nat.pow_le_pow_right hrs (by omega)
  calc ∑ k ∈ range (r + 1), ∑ j ∈ range (b + 1), Nat.choose k j * s ^ j
      ≤ ∑ _k ∈ range (r + 1), ∑ _j ∈ range (b + 1), (r * s) ^ b :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun j hj => hterm k hk j hj
    _ = (r + 1) * (b + 1) * (r * s) ^ b := by
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

section count

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The node count for an arbitrary valid input: at most `Σ_{k ≤ Λ} Σ_{j ≤ B} C(k,j) s_*^j`
nodes, `Λ = d + B` the rank, `s_* = 2048 n + 3`. -/
theorem node_count_general (hB : Assumption31b ι) (hC : Assumption31c ι) {γ : ℝ}
    {F : (ι → ℝ) → ι → ℝ} (hF : IsEq31 γ F) {I : LInput ι} (hI : I.Valid)
    {l : ι → Bool} {n : ℕ} (hrun : Run F I l n) :
    n ≤ Tsum (2048 * Fintype.card ι + 3) I.rank I.B := by
  revert hI
  refine Run.rec (F := F)
    (motive_1 := fun I _ n _ => I.Valid → n ≤ Tsum (2048 * Fintype.card ι + 3) I.rank I.B)
    (motive_2 := fun I k _ c n _ => I.Valid → ¬ I.massBase → 12 ≤ I.d → DownReach F I k →
      n ≤ c * Tsum (2048 * Fintype.card ι + 3) (I.rank - 1) (I.B - 1))
    (motive_3 := fun I k _ c n _ => I.Valid → ¬ I.massBase → 12 ≤ I.d → UpReach F I k →
      n ≤ c * Tsum (2048 * Fintype.card ι + 3) (I.rank - 1) (I.B - 1))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrun
  · intro I _ _
    exact one_le_Tsum _ _ _
  · intro I _ _ _ _ _ _
    exact one_le_Tsum _ _ _
  · intro I hm hd kdown kf l0 lc c1 c2 n1 n2 n3 n4 hdown hup hprov hcont ih1 ih2 ih3 ih4 hI
    have h1 := ih1 hI hm hd DownReach.start
    have h2 := ih2 hI hm hd (UpReach.start hdown)
    have hpc : ProvChild F I (I.provCall kf) := ProvChild.mk hdown hup
    have hoc : OtherChild F I (I.contCall l0) := OtherChild.cont hdown hup hprov
    have h3 := ih3 (hB.child γ F hF I hI hm hd _ (Or.inl hpc)).1
    have h4 := ih4 (hB.child γ F hF I hI hm hd _ (Or.inr hoc)).1
    have r3 := hC.rank_lt γ F hF I hI hm hd _ (Or.inl hpc)
    have r4 := hC.rank_lt γ F hF I hI hm hd _ (Or.inr hoc)
    have b3 := (hC.prov γ F hF I hI hm hd _ hpc).1
    have b4 := (hC.other γ F hF I hI hm hd _ hoc).1
    have hcnt := hC.other_count γ F hF I hI hm hd kdown c1 n1 hdown kf c2 n2 hup
    have h3' : n3 ≤ Tsum (2048 * Fintype.card ι + 3) (I.rank - 1) I.B := by
      refine h3.trans ?_
      rw [b3]
      exact Tsum_mono _ (by omega) le_rfl
    have h4' : n4 ≤ Tsum (2048 * Fintype.card ι + 3) (I.rank - 1) (I.B - 1) :=
      h4.trans (Tsum_mono _ (by omega) (by omega))
    obtain ⟨r, hr⟩ : ∃ r, I.rank = r + 1 := ⟨I.rank - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, I.B = b + 1 := ⟨I.B - 1, by omega⟩
    rw [hr, hb] at h1 h2 h3' h4' ⊢
    simp only [Nat.add_sub_cancel] at h1 h2 h3' h4'
    have hrec := Tsum_rec (2048 * Fintype.card ι + 3) r b
    obtain ⟨T1, hT1⟩ : ∃ T, T = Tsum (2048 * Fintype.card ι + 3) r b := ⟨_, rfl⟩
    obtain ⟨T2, hT2⟩ : ∃ T, T = Tsum (2048 * Fintype.card ι + 3) r (b + 1) := ⟨_, rfl⟩
    rw [← hT1] at h1 h2 h4' hrec
    rw [← hT2] at h3' hrec
    have hs : (c1 + c2 + 1) * T1 ≤ (2048 * Fintype.card ι + 3) * T1 :=
      Nat.mul_le_mul_right _ hcnt
    refine le_trans ?_ hrec
    nlinarith only [h1, h2, h3', h4', hs]
  · intro I k l n hcall hfix ih hI hm hd hreach
    have hoc : OtherChild F I (I.downCall k) := OtherChild.down hreach
    have h := ih (hB.child γ F hF I hI hm hd _ (Or.inr hoc)).1
    have r := hC.rank_lt γ F hF I hI hm hd _ (Or.inr hoc)
    have b := (hC.other γ F hF I hI hm hd _ hoc).1
    rw [one_mul]
    exact h.trans (Tsum_mono _ (by omega) (by omega))
  · intro I k kfin l n c n' hcall hne rest ih ihrest hI hm hd hreach
    have hoc : OtherChild F I (I.downCall k) := OtherChild.down hreach
    have h := ih (hB.child γ F hF I hI hm hd _ (Or.inr hoc)).1
    have r := hC.rank_lt γ F hF I hI hm hd _ (Or.inr hoc)
    have b := (hC.other γ F hF I hI hm hd _ hoc).1
    have h' := h.trans (Tsum_mono (2048 * Fintype.card ι + 3) (show (I.downCall k).rank ≤ I.rank - 1 by omega)
      (show (I.downCall k).B ≤ I.B - 1 by omega))
    have h2 := ihrest hI hm hd (DownReach.next hreach hcall)
    rw [add_mul, one_mul]
    omega
  · intro I k l n hcall hfix ih hI hm hd hreach
    have hoc : OtherChild F I (I.upCall k) := OtherChild.up hreach
    have h := ih (hB.child γ F hF I hI hm hd _ (Or.inr hoc)).1
    have r := hC.rank_lt γ F hF I hI hm hd _ (Or.inr hoc)
    have b := (hC.other γ F hF I hI hm hd _ hoc).1
    rw [one_mul]
    exact h.trans (Tsum_mono _ (by omega) (by omega))
  · intro I k kfin l n c n' hcall hne rest ih ihrest hI hm hd hreach
    have hoc : OtherChild F I (I.upCall k) := OtherChild.up hreach
    have h := ih (hB.child γ F hF I hI hm hd _ (Or.inr hoc)).1
    have r := hC.rank_lt γ F hF I hI hm hd _ (Or.inr hoc)
    have b := (hC.other γ F hF I hI hm hd _ hoc).1
    have h' := h.trans (Tsum_mono (2048 * Fintype.card ι + 3) (show (I.upCall k).rank ≤ I.rank - 1 by omega)
      (show (I.upCall k).B ≤ I.B - 1 by omega))
    have h2 := ihrest hI hm hd (UpReach.next hreach hcall)
    rw [add_mul, one_mul]
    omega

/-- **Lemma 4.4, node count**: a call `𝓛(A, h 2^d, a, b)` with `a_i = b_i = 1/n` has a
recursion tree with at most `(Λ+1)(B₀+1)(Λ s_*)^{B₀}` nodes, `Λ = d + B₀`, `s_* = 2048 n + 3`.
(The remaining sentences of Lemma 4.4, on boxes and on where `⌊F⌋` is evaluated, are
Assumption 3.1(b) and the definition of `Run`.) -/
theorem node_count (hB : Assumption31b ι) (hC : Assumption31c ι) {γ : ℝ}
    {F : (ι → ℝ) → ι → ℝ} (hF : IsEq31 γ F) (A : ι → ℤ) {h d : ℕ}
    (hh : 128 ≤ h ∧ h ≤ 255) {l : ι → Bool} {n : ℕ} (hrun : Run F (loopInput ι A h d) l n) :
    n ≤ (d + Bfun (1 / (Fintype.card ι : ℚ) ^ 2) + 1) * (Bfun (1 / (Fintype.card ι : ℚ) ^ 2) + 1)
        * ((d + Bfun (1 / (Fintype.card ι : ℚ) ^ 2)) * (2048 * Fintype.card ι + 3))
          ^ Bfun (1 / (Fintype.card ι : ℚ) ^ 2) := by
  have hcard : (0 : ℚ) < (Fintype.card ι : ℚ) := by exact_mod_cast Fintype.card_pos
  have hvalid : (loopInput ι A h d).Valid :=
    ⟨hh.1, hh.2, fun _ => by simp only [loopInput]; positivity,
      fun _ => by simp only [loopInput]; positivity⟩
  have hmu : (loopInput ι A h d).mu = 1 / (Fintype.card ι : ℚ) ^ 2 := by
    unfold LInput.mu
    simp only [loopInput]
    rw [Finset.inf'_const]
    ring
  have hBI : (loopInput ι A h d).B = Bfun (1 / (Fintype.card ι : ℚ) ^ 2) := by
    unfold LInput.B; rw [hmu]
  have hrank : (loopInput ι A h d).rank = d + Bfun (1 / (Fintype.card ι : ℚ) ^ 2) := by
    unfold LInput.rank; rw [hBI]; rfl
  have h1 := node_count_general hB hC hF hvalid hrun
  rw [hrank, hBI] at h1
  have hB1 : 1 ≤ Bfun (1 / (Fintype.card ι : ℚ) ^ 2) := by
    by_contra hcon
    have h0 : Bfun (1 / (Fintype.card ι : ℚ) ^ 2) = 0 := by omega
    have hspec := Bfun_spec (μ := 1 / (Fintype.card ι : ℚ) ^ 2) (by positivity)
    rw [h0, pow_zero, one_mul, lt_div_iff₀ (by positivity), one_mul] at hspec
    have : (1 : ℚ) ≤ (Fintype.card ι : ℚ) := by exact_mod_cast Fintype.card_pos
    nlinarith
  exact h1.trans (Tsum_le _ (by omega) (by omega) _)

end count

end EntropyGames
