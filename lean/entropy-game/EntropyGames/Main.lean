/-
Section 8 of the paper: Theorem 1.1, correctness part, for the normalised game.
Unconditional: it uses only Assumption 3.1(a) and the cited existence theorem as hypotheses.
-/
import EntropyGames.Lemma72
import EntropyGames.Params

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EntropyGames

open Finset Classical

/-! ## Section 8: Theorem 1.1 -/

section main

variable {D T P : Type*} [Fintype D] [Nonempty D] (Γ : EntropyGame D T P)

/-- **Theorem 1.1, correctness part, for the normalised game** (threshold `1`).

Hypotheses: Assumption 3.1(a) (`hA`); the cited existence theorem for this game (`hV`).
Parameters as in Section 8: `H = n (q + 2 n a_max)^n`, `Ω̂ = bitlength(n max(a_max, q))`,
`N = 2^s` with `2^s ≥ 2n` and `64 H · 3n(2s + 4nΩ̂ + 2) ≤ 2^s`,
`K₀ = bitlength(256 H n a_max) + bitlength(2q)`, `r = max(6K₀, bitlength(512H) + 1)`,
`δ = 1/(2^15 H)`, `K = 256(N+1)`, `J = 2^15 H N (Ω̂+1) + N + 1`, `128 · 2^{d₀} ≥ 2J`.
Conclusion: the loop terminates after at most `128(d₀+1)` calls of `𝓛` and the output test
`A_d ≥ -2^13 N` holds exactly for the `d` with `V_d ≥ 1`.

Scope with respect to the printed theorem: no Turing machine and no step count; `s` and
`d₀` are any numbers satisfying the inequalities (the paper takes the least ones). -/
theorem main_correctness (hA : Assumption31a D) {V : D → ℝ} (hV : IsValueWithPolicies Γ V)
    {q amax : ℕ} (hnorm : IsNormalised Γ q amax) {H Ωh s K0 r d0 : ℕ}
    (hH : H = Fintype.card D * (q + 2 * Fintype.card D * amax) ^ Fintype.card D)
    (hΩh : Ωh = Nat.size (Fintype.card D * max amax q))
    (hs1 : 2 * Fintype.card D ≤ 2 ^ s)
    (hs2 : 64 * H * (3 * Fintype.card D * (2 * s + 4 * Fintype.card D * Ωh + 2)) ≤ 2 ^ s)
    (hK0 : K0 = Nat.size (256 * H * Fintype.card D * amax) + Nat.size (2 * q))
    (hr : r = max (6 * K0) (Nat.size (512 * H) + 1))
    (hd0 : 2 * ((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ) ≤ 128 * 2 ^ d0) :
    (∃ Afin c, Loop (Γ.G (surE r) (1 / (2 ^ 15 * (H : ℝ))) (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c) ∧
    ∀ Afin c, Loop (Γ.G (surE r) (1 / (2 ^ 15 * (H : ℝ))) (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c →
      c ≤ 128 * (d0 + 1) ∧ ∀ d, (-(2 ^ 13 * ((2 ^ s : ℕ) : ℤ)) ≤ Afin d ↔ 1 ≤ V d) := by
  obtain ⟨hq, hw⟩ := hnorm
  have hn : 1 ≤ Fintype.card D := Fintype.card_pos
  have hH1 : 1 ≤ H := by
    rw [hH]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hN : 2 ≤ 2 ^ s := by omega
  have hr1 : 1 ≤ r := by rw [hr]; exact le_trans (by omega) (le_max_right _ _)
  have hacc := params_accuracy Γ hq hH1 hw hK0 hr
  set Ω : ℝ := Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ)) with hΩdef
  have hΩle : Ω ≤ Ωh := by
    have h1 := log_le_size (x := Fintype.card D * max amax q)
      (Nat.one_le_iff_ne_zero.mpr (by
        have : 1 ≤ max amax q := le_max_of_le_right hq
        positivity))
    rw [hΩh, hΩdef]
    rw [Nat.cast_mul] at h1
    exact h1
  have hR := params_discount (n := Fintype.card D) hH1 hΩle hs2
  have hγ0 : (0 : ℝ) ≤ 1 - 1 / ((2 ^ s : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast hN
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hγ1 : 1 - 1 / ((2 ^ s : ℕ) : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / ((2 ^ s : ℕ) : ℝ) := by positivity
    linarith
  obtain ⟨v, hv, _⟩ := (Γ.gf_isDiscounted hγ0).existsUnique_fixed hγ0 hγ1
  have hv' : ∀ d, v d = (1 - 1 / ((2 ^ s : ℕ) : ℝ)) * Γ.f v d := fun d => (congrFun hv d).symm
  have hχ : ∀ d, |Real.log (V d)| ≤ (Ωh : ℝ) := fun d =>
    (chi_bound Γ hV ⟨hq, hw⟩ d).trans hΩle
  have hdisc := fun d => lemma_7_1_c Γ hV ⟨hq, hw⟩ hN hs1 hv' d
  have hsep : ∀ d, Real.log (V d) < 0 → Real.log (V d) ≤ -1 / (H : ℝ) := by
    intro d hneg
    rcases lemma_7_2 Γ hV ⟨hq, hw⟩ d with h | h
    · linarith
    · rw [← hH, abs_of_neg hneg] at h
      rw [neg_div]; linarith
  obtain ⟨hex, hall⟩ := decision_correct Γ hA hN hH1 hr1 hacc hR hv' hχ hdisc hsep hd0
  refine ⟨hex, fun Afin c hloop => ?_⟩
  obtain ⟨hc, hiff⟩ := hall Afin c hloop
  refine ⟨hc, fun d => ?_⟩
  rw [hiff d, Real.log_nonneg_iff (lemma_7_1_a Γ hV d).1]

end main

end EntropyGames
