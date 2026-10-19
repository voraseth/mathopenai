/-
Theorem 3(ii) of the note, REDUCED to the partition bound: we prove
`Lemma2WeakStatement → Theorem3iiStatement` with the explicit threshold `n₁ = max n₀ 2560000`,
and the rewriting `n^{√n/400} e^{-4√n} = n^{√n/400 - 4√n/ln n}` for `n ≥ 2`.
Lemma 2 itself is proved in `Lemma2.lean`, which also concludes Theorem 3(ii).
-/
import Depth3Note.Theorem3

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset

noncomputable section

/-- the rewriting printed in Theorem 3(ii) -/
theorem theorem3ii_rewrite : Theorem3iiRewriteStatement := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log n ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact (Real.log_pos this).ne'
  have hb : (n : ℝ) ^ (4 * Real.sqrt n / Real.log n) = Real.exp (4 * Real.sqrt n) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    field_simp
  rw [Real.rpow_sub hn0, hb, neg_mul, Real.exp_neg]
  exact (div_eq_mul_inv _ _).symm

/-- `2 (e^{3x} + x² + 2) ≤ e^{4x}` for `x ≥ 2` -/
theorem exp_aux {x : ℝ} (hx : 2 ≤ x) :
    2 * (Real.exp (3 * x) + x ^ 2 + 2) ≤ Real.exp (4 * x) := by
  have h1 : 4 ≤ Real.exp x := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ x)
    nlinarith
  have h3 : x ^ 2 + 2 ≤ Real.exp (3 * x) := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * x)
    nlinarith
  have h4 : Real.exp (4 * x) = Real.exp (3 * x) * Real.exp x := by
    rw [← Real.exp_add]
    ring_nf
  have hpos := Real.exp_pos (3 * x)
  rw [h4]
  nlinarith

/-- `n³ + 1 ≤ ½ n^{√n/400}` for `n ≥ 2560000` -/
theorem pow_aux {n : ℕ} (hn : 2560000 ≤ n) :
    (n : ℝ) ^ 3 + 1 ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) / 2 := by
  have hn' : (2560000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ n := by linarith
  have hs : (1600 : ℝ) ≤ Real.sqrt n := by
    rw [show (1600 : ℝ) = Real.sqrt (1600 ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have h4 : (n : ℝ) ^ (4 : ℝ) ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h4' : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4'] at h4
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have h5 : (n : ℝ) ^ 4 = n * (n : ℝ) ^ 3 := by ring
  have h6 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ h1
  nlinarith

/-- **Theorem 3(ii)**, conditional on the partition bound `p(n) ≤ e^{3√n}` (Lemma 2). -/
theorem theorem3ii_of_lemma2 (hp : Lemma2WeakStatement) : Theorem3iiStatement.{u} := by
  intro n₀
  refine ⟨max n₀ 2560000, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro hA K _ _ n hn τ _ ι S hS
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 2560000 ≤ n := le_trans (le_max_right _ _) hn
  have hi := theorem3i n₀ hA K n hn0 τ ι S hS
  push_cast at hi ⊢
  set x := Real.sqrt (n : ℝ) with hx
  set R := (n : ℝ) ^ (x / 400) with hR
  have hnr : (2560000 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx2 : x ^ 2 = n := Real.sq_sqrt (by linarith)
  have hxge : (2 : ℝ) ≤ x := by
    rw [hx, show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have he := exp_aux hxge
  rw [hx2] at he
  have hpw := pow_aux hn1
  have hpn : (p n : ℝ) ≤ Real.exp (3 * x) := hp n
  have hs0 : (0 : ℝ) ≤ S.s := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ S.B := Nat.cast_nonneg _
  have hE3 := Real.exp_pos (3 * x)
  have hE4 := Real.exp_pos (4 * x)
  -- left-hand side of (i) is at most (s + B)(e^{3x} + n + 2) + n³ + 1
  have hkey : R / 2 ≤ ((S.s : ℝ) + S.B) * (Real.exp (4 * x) / 2) := by
    have hsp : (S.s : ℝ) * p n ≤ S.s * Real.exp (3 * x) := mul_le_mul_of_nonneg_left hpn hs0
    nlinarith [mul_nonneg hs0 hE3.le, mul_nonneg hB0 hE3.le, mul_nonneg hs0 (by linarith : (0:ℝ) ≤ n),
      mul_nonneg hB0 (by linarith : (0:ℝ) ≤ n),
      mul_le_mul_of_nonneg_left he (add_nonneg hs0 hB0)]
  have hneg : Real.exp (-4 * x) = (Real.exp (4 * x))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hE4]
  linarith

end

end Depth3Note
