/-
Section 8 of the paper, paragraph "Parameters": the parameter choices imply the hypotheses of
Lemma 5.3 (accuracy `ε = 1/(64H)`) and the inequality `θ R ≤ 1/(64H)`.
Bit lengths are `Nat.size`.
-/
import EntropyGames.Game

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

/-- `ln x ≤ bitlength(x)` for a positive integer `x`. -/
theorem log_le_size {x : ℕ} (hx : 1 ≤ x) : Real.log x ≤ Nat.size x := by
  have h1 : (x : ℝ) < 2 ^ (Nat.size x) := by exact_mod_cast Nat.lt_size_self x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have h2 : Real.log x < Real.log (2 ^ (Nat.size x)) := Real.log_lt_log hxpos h1
  rw [Real.log_pow] at h2
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have h4 : (Nat.size x : ℝ) * Real.log 2 ≤ Nat.size x :=
    mul_le_of_le_one_right (by positivity) h3
  linarith

/-- `log₂ x ≤ bitlength(x)` for a positive integer `x`. -/
theorem logb_le_size {x : ℕ} (hx : 1 ≤ x) : Real.logb 2 x ≤ Nat.size x := by
  have h1 : (x : ℝ) ≤ 2 ^ (Nat.size x) := by exact_mod_cast (Nat.lt_size_self x).le
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have h2 : Real.logb 2 x ≤ Real.logb 2 (2 ^ (Nat.size x)) :=
    Real.logb_le_logb_of_le (by norm_num) hxpos h1
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2

/-- Section 8: with `K₀ = bitlength(256 H n a_max) + bitlength(2q)` and
`r = max(6 K₀, bitlength(512 H) + 1)`, the surrogate of the normalised game (weights `a_e / q`
with integers `1 ≤ a_e ≤ a_max`) satisfies `‖f̃ - f‖_∞ ≤ ε = 1/(64H)`. -/
theorem params_accuracy {D T P : Type*} [Fintype D] (Γ : EntropyGame D T P)
    {q amax H K0 r : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H)
    (hw : ∀ p, ∀ j ∈ Γ.outP p, ∃ a : ℕ, 1 ≤ a ∧ a ≤ amax ∧ Γ.m p j = (a : ℝ) / q)
    (hK0 : K0 = Nat.size (256 * H * Fintype.card D * amax) + Nat.size (2 * q))
    (hr : r = max (6 * K0) (Nat.size (512 * H) + 1)) (t : D → ℝ) (d : D) :
    |Γ.ft (surE r) t d - Γ.f t d| ≤ 1 / (64 * (H : ℝ)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hn : 1 ≤ Fintype.card D := Fintype.card_pos_iff.mpr ⟨d⟩
  -- a_max ≥ 1 because the game has an arc
  have hamax : 1 ≤ amax := by
    obtain ⟨θ, _⟩ := Γ.outD_nonempty d
    obtain ⟨p, _⟩ := Γ.outT_nonempty θ
    obtain ⟨j, hj⟩ := Γ.outP_nonempty p
    obtain ⟨a, ha1, ha2, _⟩ := hw p j hj
    omega
  have hn' : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast hn
  have hamax' : (1 : ℝ) ≤ amax := by exact_mod_cast hamax
  have hSum : ∀ p, ∑ j ∈ Γ.outP p, Γ.m p j ≤ (Fintype.card D : ℝ) * amax := by
    intro p
    calc ∑ j ∈ Γ.outP p, Γ.m p j ≤ ∑ _j ∈ Γ.outP p, (amax : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨a, ha1, ha2, hm⟩ := hw p j hj
          rw [hm, div_le_iff₀ (by linarith)]
          have : (a : ℝ) ≤ amax := by exact_mod_cast ha2
          nlinarith
      _ = ((Γ.outP p).card : ℝ) * amax := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card D : ℝ) * amax := by
          have : ((Γ.outP p).card : ℝ) ≤ Fintype.card D := by exact_mod_cast Finset.card_le_univ _
          exact mul_le_mul_of_nonneg_right this (by linarith)
  have hmin : ∀ p, ∀ j ∈ Γ.outP p, 1 / (q : ℝ) ≤ Γ.m p j := by
    intro p j hj
    obtain ⟨a, ha1, ha2, hm⟩ := hw p j hj
    rw [hm]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    gcongr
  have hK1 : Real.log (4 * ((Fintype.card D : ℝ) * amax) / (1 / (64 * (H : ℝ)))) ≤ (K0 : ℝ) := by
    have h1 : 4 * ((Fintype.card D : ℝ) * amax) / (1 / (64 * (H : ℝ)))
        = ((256 * H * Fintype.card D * amax : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    rw [h1, hK0]
    have := log_le_size (x := 256 * H * Fintype.card D * amax) (by
      have : 1 ≤ H * Fintype.card D * amax :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith)
    push_cast at this ⊢
    have h2 : (0 : ℝ) ≤ Nat.size (2 * q) := by positivity
    linarith
  have hK2 : Real.log (2 / (1 / (q : ℝ))) ≤ (K0 : ℝ) := by
    have h1 : 2 / (1 / (q : ℝ)) = ((2 * q : ℕ) : ℝ) := by push_cast; field_simp
    rw [h1, hK0]
    have := log_le_size (x := 2 * q) (by omega)
    have h2 : (0 : ℝ) ≤ Nat.size (256 * H * Fintype.card D * amax) := by positivity
    push_cast at this ⊢
    linarith
  have hr6 : 6 * K0 ≤ r := by rw [hr]; exact le_max_left _ _
  have hrs : Nat.size (512 * H) + 1 ≤ r := by rw [hr]; exact le_max_right _ _
  have hr1 : 2 * Real.exp 1 * (K0 : ℝ) ≤ r + 1 := by
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h6 : (6 : ℝ) * K0 ≤ r := by exact_mod_cast hr6
    have hK : (0 : ℝ) ≤ K0 := by positivity
    nlinarith
  have hr2 : Real.logb 2 (2 / (1 / (64 * (H : ℝ)) / 4)) ≤ r + 1 := by
    have h1 : 2 / (1 / (64 * (H : ℝ)) / 4) = ((512 * H : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    rw [h1]
    have := logb_le_size (x := 512 * H) (by omega)
    have h2 : ((Nat.size (512 * H) + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hrs
    push_cast at h2
    linarith
  exact Γ.abs_ft_sub_f_le' (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    hSum (by positivity) hmin hK1 hK2 hr1 hr2 t d

/-- Section 8: the choice of `N = 2^s` with `64 H · 3n(2s + 4nΩ̂ + 2) ≤ 2^s` gives
`θ R ≤ 1/(64H)` for `R = 3n(2 ln N + 4nΩ + 2)` and `Ω ≤ Ω̂`. -/
theorem params_discount {n H s Ωh : ℕ} {Ω : ℝ} (hH : 1 ≤ H) (hΩ : Ω ≤ Ωh)
    (hs : 64 * H * (3 * n * (2 * s + 4 * n * Ωh + 2)) ≤ 2 ^ s) :
    3 * (n : ℝ) * (2 * Real.log ((2 ^ s : ℕ) : ℝ) + 4 * n * Ω + 2) / ((2 ^ s : ℕ) : ℝ)
      ≤ 1 / (64 * (H : ℝ)) := by
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hs' : (64 : ℝ) * H * (3 * n * (2 * s + 4 * n * Ωh + 2)) ≤ 2 ^ s := by exact_mod_cast hs
  have hlog : Real.log ((2 ^ s : ℕ) : ℝ) ≤ s := by
    push_cast
    rw [Real.log_pow]
    have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    exact mul_le_of_le_one_right (by positivity) h3
  have h2s : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ h2s (by positivity), one_mul]
  have hn : (0 : ℝ) ≤ n := by positivity
  have h1 : 3 * (n : ℝ) * (2 * Real.log ((2 ^ s : ℕ) : ℝ) + 4 * n * Ω + 2)
      ≤ 3 * n * (2 * s + 4 * n * Ωh + 2) := by
    have : 4 * (n : ℝ) * Ω ≤ 4 * n * Ωh := by nlinarith
    have h3n : (0 : ℝ) ≤ 3 * n := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h3n
  have h64 : (0 : ℝ) ≤ 64 * H := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 h64
  push_cast at h2 ⊢
  linarith

end EntropyGames
