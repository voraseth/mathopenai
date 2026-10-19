/-
Corollary 5 of the note, DETERMINANT HALF: under Hypothesis A, every `ΣΠΣ` circuit computing the
`M × M` determinant has `s + B ≥ M^{c M^{1/4}}` for `M ≥ M₀(n₀)`, with the absolute constant
`c = 1/4800` (the paper says "any `c < 1/800` will do"; the statement only asks for some `c > 0`).
(The permanent half is not formalised.)
-/
import Depth3Note.Lemma4

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset

noncomputable section

/-! ### Affine substitutions and scaling in `ΣΠΣ` expressions -/

namespace SPS

variable {K : Type u} [CommSemiring K] {σ ρ : Type} [Fintype σ] [Fintype ρ]

/-- substitute the affine form `g0 v + ∑_w g1 v w · x_w` for the variable `v`; `s` and `B` are
unchanged -/
def subst (S : SPS K σ) (g0 : σ → K) (g1 : σ → ρ → K) : SPS K ρ where
  s := S.s
  B := S.B
  c := S.c
  a := fun j => S.a j + ∑ v, S.l j v * g0 v
  l := fun j w => ∑ v, S.l j v * g1 v w
  m := S.m

theorem subst_value (S : SPS K σ) (g0 : σ → K) (g1 : σ → ρ → K) :
    (S.subst g0 g1).value =
      aeval (fun v => C (g0 v) + ∑ w, C (g1 v w) * (X w : MvPolynomial ρ K)) S.value := by
  have hform : ∀ j : Fin S.B,
      C (S.a j + ∑ v, S.l j v * g0 v) + ∑ w, C (∑ v, S.l j v * g1 v w) * (X w : MvPolynomial ρ K) =
        C (S.a j) + ∑ v, C (S.l j v) * (C (g0 v) + ∑ w, C (g1 v w) * X w) := by
    intro j
    simp only [C_add, map_sum, C_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, add_assoc]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  have hformval : ∀ j : Fin S.B, (S.subst g0 g1).form j =
      aeval (fun v => C (g0 v) + ∑ w, C (g1 v w) * (X w : MvPolynomial ρ K)) (S.form j) := by
    intro j
    have e : aeval (fun v => C (g0 v) + ∑ w, C (g1 v w) * (X w : MvPolynomial ρ K)) (S.form j) =
        C (S.a j) + ∑ v, C (S.l j v) * (C (g0 v) + ∑ w, C (g1 v w) * X w) := by
      simp only [form, lin, map_add, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
    rw [e]
    exact hform j
  have hval : (S.subst g0 g1).value = ∑ i, C (S.c i) * ∏ j, (S.subst g0 g1).form j ^ S.m i j := rfl
  rw [hval]
  simp only [hformval, value, map_sum, map_mul, map_prod, map_pow, aeval_C, algebraMap_eq]
  rfl

/-- multiply every top coefficient by `r`; `s` and `B` are unchanged -/
def scale (S : SPS K σ) (r : K) : SPS K σ where
  s := S.s
  B := S.B
  c := fun i => r * S.c i
  a := S.a
  l := S.l
  m := S.m

theorem scale_value (S : SPS K σ) (r : K) : (S.scale r).value = C r * S.value := by
  simp only [value, form, lin, scale, Finset.mul_sum, C_mul, mul_assoc]
  rfl

end SPS

theorem entry_affine {K : Type u} [CommSemiring K] {ρ : Type} [Fintype ρ]
    (q : MvPolynomial ρ K) (h : q = 0 ∨ q = 1 ∨ ∃ v, q = X v) :
    ∃ (a0 : K) (a1 : ρ → K), q = C a0 + ∑ w, C (a1 w) * X w := by
  classical
  rcases h with rfl | rfl | ⟨v, rfl⟩
  · exact ⟨0, fun _ => 0, by simp⟩
  · exact ⟨1, fun _ => 0, by simp⟩
  · refine ⟨0, fun w => if w = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [hw]
    · intro hv
      exact absurd (Finset.mem_univ v) hv

/-- The projection in the proof of Corollary 5: a `ΣΠΣ` expression for `det_M` gives one for
`IMM_{n,n}` with the same `s` and `B`, when `n ≥ 2` and `n² - n + 1 ≤ M`. -/
theorem det_circuit_to_imm (K : Type u) [Field K] (n M : ℕ) (hn : 2 ≤ n)
    (hM : n ^ 2 - n + 1 ≤ M) (S : SPS K (Fin M × Fin M))
    (hS : S.value = (genericMatrix K M).det) :
    ∃ S' : SPS K (ImmVar n), S'.s = S.s ∧ S'.B = S.B ∧ S'.value = imm K n := by
  obtain ⟨A, hA, hdet⟩ := exists_matrix_det K n hn M hM
  choose g0 g1 hg using fun q : Fin M × Fin M => entry_affine (A q.1 q.2) (hA q.1 q.2)
  refine ⟨(S.subst g0 g1).scale ((-1) ^ (n - 1)), rfl, rfl, ?_⟩
  rw [SPS.scale_value, SPS.subst_value, hS, AlgHom.map_det]
  have hmat : (aeval fun v : Fin M × Fin M => C (g0 v) + ∑ w, C (g1 v w) * X w).mapMatrix
      (genericMatrix K M) = A := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, genericMatrix, aeval_X]
    exact (hg (i, j)).symm
  rw [hmat, hdet, ← mul_assoc]
  have : (C ((-1 : K) ^ (n - 1)) : MvPolynomial (ImmVar n) K) * (-1) ^ (n - 1) = 1 := by
    rw [C_pow, ← mul_pow]
    simp
  rw [this, one_mul]

/-! ### The numerical inequality -/

/-- For `n = ⌊√M⌋` with `ln n ≥ 3200`: `M^{M^{1/4}/4800} ≤ n^{√n/400} e^{-4√n}`. -/
theorem numeric_aux (M n : ℕ) (h2 : M < (n + 1) ^ 2)
    (hlog : Real.exp 3200 ≤ n) :
    (M : ℝ) ^ ((1 / 4800 : ℝ) * (M : ℝ) ^ (1 / 4 : ℝ)) ≤
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) * Real.exp (-4 * Real.sqrt n) := by
  have hn3 : (3 : ℝ) ≤ n := by
    have := Real.add_one_le_exp (3200 : ℝ)
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  set x := Real.sqrt (n : ℝ) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = n := Real.sq_sqrt hn0.le
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hMle : (M : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by exact_mod_cast h2.le
  -- M ≤ n³
  have hMn3 : (M : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  -- M^{1/4} ≤ 2 √n
  set y := (M : ℝ) ^ (1 / 4 : ℝ) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hM0 _
  have hy4 : y ^ 4 = M := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hM0]
    norm_num
  have hyx : y ≤ 2 * x := by
    by_contra hcon
    push Not at hcon
    have h2x : 0 ≤ 2 * x := by positivity
    have : (2 * x) ^ 4 < y ^ 4 := pow_lt_pow_left₀ hcon h2x (by norm_num)
    have e : (2 * x) ^ 4 = 16 * (x ^ 2) ^ 2 := by ring
    rw [e, hx2, hy4] at this
    nlinarith
  -- first part: M^{y/4800} ≤ n^{x/800}
  have hpart1 : (M : ℝ) ^ ((1 / 4800 : ℝ) * y) ≤ (n : ℝ) ^ (x / 800) := by
    calc (M : ℝ) ^ ((1 / 4800 : ℝ) * y) ≤ ((n : ℝ) ^ (3 : ℝ)) ^ ((1 / 4800 : ℝ) * y) :=
          Real.rpow_le_rpow hM0 hMn3 (by positivity)
      _ = (n : ℝ) ^ (3 * ((1 / 4800 : ℝ) * y)) := by rw [← Real.rpow_mul hn0.le]
      _ ≤ (n : ℝ) ^ (x / 800) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  -- second part: e^{4x} ≤ n^{x/800}
  have hlog' : (3200 : ℝ) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).2 hlog
  have hpart2 : Real.exp (4 * x) ≤ (n : ℝ) ^ (x / 800) := by
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.2
    nlinarith
  have hsplit : (n : ℝ) ^ (x / 400) = (n : ℝ) ^ (x / 800) * (n : ℝ) ^ (x / 800) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hneg : Real.exp (-4 * x) = (Real.exp (4 * x))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  have hE := Real.exp_pos (4 * x)
  have hP : 0 ≤ (n : ℝ) ^ (x / 800) := Real.rpow_nonneg hn0.le _
  rw [hsplit, hneg, mul_assoc]
  refine hpart1.trans ?_
  have : 1 ≤ (n : ℝ) ^ (x / 800) * (Real.exp (4 * x))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hE]
    linarith
  nlinarith

/-! ### Corollary 5, determinant half -/

/-- **Corollary 5, determinant half**, with `c = 1/4800`. Hypothesis A is the explicit hypothesis
`HypothesisA n₀`. -/
theorem corollary5_det : Corollary5DetStatement.{u} := by
  refine ⟨1 / 4800, by norm_num, ?_⟩
  intro n₀
  obtain ⟨n₁, hn₁, h3⟩ := theorem3ii.{u} n₀
  refine ⟨(max n₁ ⌈Real.exp 3200⌉₊) ^ 2, ?_⟩
  intro hA K _ _ M hM τ _ ι S hS
  set n := Nat.sqrt M with hn
  have hsq1 : n ^ 2 ≤ M := Nat.sqrt_le' M
  have hsq2 : M < (n + 1) ^ 2 := Nat.lt_succ_sqrt' M
  have hbig : max n₁ ⌈Real.exp 3200⌉₊ ≤ n := Nat.le_sqrt'.2 hM
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hbig
  have hn2 : 2 ≤ n := le_trans hn₁ hn1
  have hexp : Real.exp 3200 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hbig)
  have hMn : n ^ 2 - n + 1 ≤ M := by
    have : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    omega
  -- the circuit restricted to the M² matrix entries computes det_M
  have hS1 : (S.restrict ι).value = (genericMatrix K M).det := S.restrict_value_of_rename ι _ hS
  obtain ⟨S', hs, hB, hval⟩ := det_circuit_to_imm K n M hn2 hMn (S.restrict ι) hS1
  have h := h3 hA K n hn1 (ImmVar n) (Function.Embedding.refl _) S' (by rw [hval]; exact (rename_id_apply _).symm)
  have hsB : S'.s + S'.B = S.s + S.B := by rw [hs, hB]; rfl
  rw [hsB] at h
  exact (numeric_aux M n hsq2 hexp).trans h

end

end Depth3Note
