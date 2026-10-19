/-
Section 6 of the paper: Remark 6.3, the algebraic part.
-/
import EntropyGames.Lam

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

/-- Remark 6.3, the algebraic part: for `M = [[1,1],[0,1]]` the fixed point has `v_2 = 0` and
`X = e^{v_1}` solves `X^{N/(N-1)} = X + 1`.  (The asymptotic `v_1 = ln N - ln ln N + o(1)` is
not stated.) -/
theorem remark_6_3 {N : ℕ} (hN : 2 ≤ N) {v : Fin 2 → ℝ}
    (hv : Psi (1 - 1 / (N : ℝ)) (fun i j : Fin 2 => if i = 1 ∧ j = 0 then 0 else 1) v = v) :
    v 1 = 0 ∧ Real.exp (v 0) ^ ((N : ℝ) / (N - 1)) = Real.exp (v 0) + 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hγ : 1 - 1 / (N : ℝ) = (N - 1) / N := by field_simp
  have h1 := congrFun hv 1
  have h0 := congrFun hv 0
  simp only [Psi, Fin.sum_univ_two] at h1 h0
  simp at h1 h0
  have hθ : 0 < (N : ℝ)⁻¹ := by positivity
  have hv1 : v 1 = 0 := by
    have : (N : ℝ)⁻¹ * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hθ.ne'
    · exact h
  refine ⟨hv1, ?_⟩
  rw [hv1, Real.exp_zero] at h0
  have hpos : 0 < Real.exp (v 0) + 1 := by positivity
  rw [← Real.exp_mul]
  have e : v 0 * ((N : ℝ) / (N - 1)) = Real.log (Real.exp (v 0) + 1) := by
    have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
    obtain ⟨L, hL⟩ : ∃ L, L = Real.log (Real.exp (v 0) + 1) := ⟨_, rfl⟩
    rw [← hL] at h0 ⊢
    rw [← h0]
    field_simp
  rw [e, Real.exp_log hpos]

/-- Remark 6.3: for `M = [[1,1],[0,1]]` one has `λ_1 = λ_2 = 0`. -/
theorem remark_6_3_lam (i : Fin 2) :
    lam (fun i j : Fin 2 => if i = 1 ∧ j = 0 then 0 else 1) i = 0 := by
  obtain ⟨M, hMdef⟩ : ∃ M : Fin 2 → Fin 2 → ℝ,
      M = fun i j : Fin 2 => if i = 1 ∧ j = 0 then 0 else 1 := ⟨_, rfl⟩
  rw [← hMdef]
  have hM : MatHyp M 1 1 (Real.log (Fintype.card (Fin 2) * max 1 (max (1 / 1) 1))) := by
    refine ⟨fun a b => ?_, fun a => ⟨1, ?_⟩, one_pos, fun a b h => ?_, fun a b => ?_, le_rfl⟩
    · rw [hMdef]; simp only; split_ifs <;> norm_num
    · rw [hMdef]; simp
    · rw [hMdef] at h ⊢; simp only at h ⊢; split_ifs at h ⊢ <;> simp_all
    · rw [hMdef]; simp only; split_ifs <;> norm_num
  have hall : ∀ x ∈ lamSet M i, x = 0 := by
    rintro _ ⟨C, ρ, U, _, _, ⟨hρ, hU1, ⟨k0, hk0C, _⟩, hMU⟩, rfl⟩
    have hρ1 : ρ = 1 := by
      by_cases h1 : (1 : Fin 2) ∈ C
      · have h := hMU 1 h1
        have hU := hU1 1 h1
        rw [← Finset.univ_inter C, ← Finset.sum_ite_mem, Fin.sum_univ_two] at h
        rw [hMdef] at h
        simp [h1] at h
        nlinarith
      · have h0 : (0 : Fin 2) ∈ C := by
          fin_cases k0
          · exact hk0C
          · exact absurd hk0C h1
        have h := hMU 0 h0
        have hU := hU1 0 h0
        rw [← Finset.univ_inter C, ← Finset.sum_ite_mem, Fin.sum_univ_two] at h
        rw [hMdef] at h
        simp [h1, h0] at h
        nlinarith
    rw [hρ1, Real.log_one]
  obtain ⟨x, hx⟩ := lamSet_nonempty hM i
  have hS : lamSet M i = {0} := by
    ext y
    constructor
    · intro hy; exact hall y hy
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy, ← hall x hx]; exact hx
  rw [lam_eq_sSup, hS, csSup_singleton]

end EntropyGames
