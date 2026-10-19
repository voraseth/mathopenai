/-
Section 2 of the paper, paragraph "Normalisation", and Theorem 1.1 (correctness part) for the
GIVEN game and threshold `r`:

* `main_correctness_threshold`: the output test of the algorithm, run on the game with all
  weights divided by `r`, holds exactly for the `d` with `V_d ≥ r`, `V` the value of the given
  game;
* `normQ`, `normA`, `normAmax`: the paper's integers `q = r₁ ∏_e c_e`,
  `a_e = b_e r₂ ∏_{e' ≠ e} c_{e'}`, `a_max = max_e a_e`;
* `norm_identity`: `m_e / r = a_e / q`; `isNormalised_rational`: the game with weights `m_e / r`
  is normalised with these integers;
* `main_correctness_rational`: the two joined, for positive rational weights `b_e / c_e` and
  a positive rational threshold `r₁ / r₂`.

The bit bound "at most `L` bits" is not formalised.
-/
import EntropyGames.Main
import EntropyGames.Scale

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EntropyGames

open Finset Classical

section threshold

variable {D T P : Type*} [Fintype D] [Nonempty D] (Γ : EntropyGame D T P)

/-- **Theorem 1.1, correctness part, for the given game and threshold `r > 0`.**

`V` is the value of the given game `Γ` (saddle-point condition over all strategies, `hV`).
The algorithm is run on the game with all weights divided by `r`, which is assumed to be
normalised with integers `q`, `a_max` (`hnorm`; see `isNormalised_rational` for rational data)
and to satisfy the cited existence theorem (`hE`).  Parameters as in `main_correctness`.
Conclusion: the loop terminates after at most `128(d₀+1)` calls of `𝓛`, and the output test
`A_d ≥ -2^13 N` holds exactly for the `d` with `V_d ≥ r`. -/
theorem main_correctness_threshold (hA : Assumption31a D) {r : ℝ} (hr : 0 < r) {V : D → ℝ}
    (hV : IsValue Γ V)
    (hE : ExistenceTheorem (scale Γ (1 / r) (one_div_pos.mpr hr)))
    {q amax : ℕ} (hnorm : IsNormalised (scale Γ (1 / r) (one_div_pos.mpr hr)) q amax)
    {H Ωh s K0 ζ d0 : ℕ}
    (hH : H = Fintype.card D * (q + 2 * Fintype.card D * amax) ^ Fintype.card D)
    (hΩh : Ωh = Nat.size (Fintype.card D * max amax q))
    (hs1 : 2 * Fintype.card D ≤ 2 ^ s)
    (hs2 : 64 * H * (3 * Fintype.card D * (2 * s + 4 * Fintype.card D * Ωh + 2)) ≤ 2 ^ s)
    (hK0 : K0 = Nat.size (256 * H * Fintype.card D * amax) + Nat.size (2 * q))
    (hζ : ζ = max (6 * K0) (Nat.size (512 * H) + 1))
    (hd0 : 2 * ((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ) ≤ 128 * 2 ^ d0) :
    (∃ Afin c, Loop ((scale Γ (1 / r) (one_div_pos.mpr hr)).G (surE ζ) (1 / (2 ^ 15 * (H : ℝ)))
        (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c) ∧
    ∀ Afin c, Loop ((scale Γ (1 / r) (one_div_pos.mpr hr)).G (surE ζ) (1 / (2 ^ 15 * (H : ℝ)))
        (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c →
      c ≤ 128 * (d0 + 1) ∧ ∀ d, (-(2 ^ 13 * ((2 ^ s : ℕ) : ℤ)) ≤ Afin d ↔ r ≤ V d) := by
  obtain ⟨V', hV'⟩ := hE
  obtain ⟨hex, hall⟩ := main_correctness _ hA hV' hnorm hH hΩh hs1 hs2 hK0 hζ hd0
  refine ⟨hex, fun Afin c hl => ?_⟩
  obtain ⟨hc, hiff⟩ := hall Afin c hl
  exact ⟨hc, fun d => (hiff d).trans (threshold_scale Γ hr hV hV'.isValue d)⟩

end threshold

section rational

variable {D T P : Type*} [Fintype D] [Fintype P] (Γ : EntropyGame D T P)

/-- The arcs `e = (p, d) ∈ E ∩ (P × D)`. -/
noncomputable def arcsPD : Finset (P × D) := Finset.univ.filter fun e => e.2 ∈ Γ.outP e.1

/-- `q = r₁ ∏_e c_e`. -/
noncomputable def normQ (c : P → D → ℕ) (r1 : ℕ) : ℕ := r1 * ∏ e ∈ arcsPD Γ, c e.1 e.2

/-- `a_e = b_e r₂ ∏_{e' ≠ e} c_{e'}`. -/
noncomputable def normA (b c : P → D → ℕ) (r2 : ℕ) (p : P) (d : D) : ℕ :=
  b p d * r2 * ∏ e ∈ (arcsPD Γ).erase (p, d), c e.1 e.2

/-- `a_max = max_e a_e`. -/
noncomputable def normAmax (b c : P → D → ℕ) (r2 : ℕ) : ℕ :=
  (arcsPD Γ).sup fun e => normA Γ b c r2 e.1 e.2

variable {Γ} {b c : P → D → ℕ} {r1 r2 : ℕ}

theorem mem_arcsPD {p : P} {d : D} : (p, d) ∈ arcsPD Γ ↔ d ∈ Γ.outP p := by
  simp [arcsPD]

theorem normQ_pos (hc : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ c p d) (hr1 : 1 ≤ r1) : 1 ≤ normQ Γ c r1 := by
  unfold normQ
  have : 0 < ∏ e ∈ arcsPD Γ, c e.1 e.2 :=
    Finset.prod_pos fun e he => hc e.1 e.2 (mem_arcsPD.mp he)
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

theorem normA_pos (hb : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ b p d) (hc : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ c p d)
    (hr2 : 1 ≤ r2) {p : P} {d : D} (hd : d ∈ Γ.outP p) : 1 ≤ normA Γ b c r2 p d := by
  unfold normA
  have : 0 < ∏ e ∈ (arcsPD Γ).erase (p, d), c e.1 e.2 :=
    Finset.prod_pos fun e he => hc e.1 e.2 (mem_arcsPD.mp (Finset.mem_of_mem_erase he))
  have := hb p d hd
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))

/-- Section 2, "Normalisation": `m_e / r = a_e / q` for `m_e = b_e / c_e`, `r = r₁ / r₂`. -/
theorem norm_identity (hc : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ c p d) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    {p : P} {d : D} (hd : d ∈ Γ.outP p) :
    ((b p d : ℝ) / c p d) / ((r1 : ℝ) / r2) = (normA Γ b c r2 p d : ℝ) / normQ Γ c r1 := by
  have hmem : (p, d) ∈ arcsPD Γ := mem_arcsPD.mpr hd
  have hprod : ∏ e ∈ arcsPD Γ, c e.1 e.2
      = c p d * ∏ e ∈ (arcsPD Γ).erase (p, d), c e.1 e.2 :=
    (Finset.mul_prod_erase (arcsPD Γ) (fun e => c e.1 e.2) hmem).symm
  have hX : 0 < ∏ e ∈ (arcsPD Γ).erase (p, d), c e.1 e.2 :=
    Finset.prod_pos fun e he => hc e.1 e.2 (mem_arcsPD.mp (Finset.mem_of_mem_erase he))
  unfold normA normQ
  rw [hprod]
  obtain ⟨X, hXdef⟩ : ∃ X, X = ∏ e ∈ (arcsPD Γ).erase (p, d), c e.1 e.2 := ⟨_, rfl⟩
  rw [← hXdef] at hX ⊢
  have h1 : (0 : ℝ) < c p d := by exact_mod_cast hc p d hd
  have h2 : (0 : ℝ) < r1 := by exact_mod_cast hr1
  have h3 : (0 : ℝ) < r2 := by exact_mod_cast hr2
  have h4 : (0 : ℝ) < X := by exact_mod_cast hX
  push_cast
  field_simp

/-- Section 2, "Normalisation": for weights `m_e = b_e / c_e` and threshold `r = r₁ / r₂`
(positive integers), the game with weights `m_e / r` is normalised with the paper's integers
`q = r₁ ∏ c_e`, `a_e = b_e r₂ ∏_{e' ≠ e} c_{e'}`, `a_max = max a_e`. -/
theorem isNormalised_rational (hb : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ b p d)
    (hc : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ c p d)
    (hm : ∀ p, ∀ d ∈ Γ.outP p, Γ.m p d = (b p d : ℝ) / c p d) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    {r : ℝ} (hr : 0 < r) (hrr : r = (r1 : ℝ) / r2) :
    IsNormalised (scale Γ (1 / r) (one_div_pos.mpr hr)) (normQ Γ c r1) (normAmax Γ b c r2) := by
  refine ⟨normQ_pos hc hr1, fun p d hd => ?_⟩
  have hd' : d ∈ Γ.outP p := hd
  refine ⟨normA Γ b c r2 p d, normA_pos hb hc hr2 hd', ?_, ?_⟩
  · exact Finset.le_sup (f := fun e : P × D => normA Γ b c r2 e.1 e.2) (mem_arcsPD.mpr hd')
  · rw [← norm_identity hc hr1 hr2 hd', ← hm p d hd', ← hrr]
    show 1 / r * Γ.m p d = Γ.m p d / r
    ring

variable (Γ) [Nonempty D]

/-- **Theorem 1.1, correctness part, for an entropy game with positive rational weights
`m_e = b_e / c_e` and a positive rational threshold `r = r₁ / r₂`.**

Hypotheses: Assumption 3.1(a) for the index set `D`; `V` is the value of the given game; the
cited existence theorem for the game with weights `m_e / r`.  `q`, `a_max` are the paper's
integers; the other parameters as in Section 8.  Conclusion: the loop terminates after at most
`128(d₀+1)` calls of `𝓛` and the output test holds exactly for the `d` with `V_d ≥ r`.
(No Turing machine, no step count, no bit bound; `s`, `d₀` any admissible numbers.) -/
theorem main_correctness_rational (hA : Assumption31a D)
    (hb : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ b p d) (hc : ∀ p, ∀ d ∈ Γ.outP p, 1 ≤ c p d)
    (hm : ∀ p, ∀ d ∈ Γ.outP p, Γ.m p d = (b p d : ℝ) / c p d) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    {r : ℝ} (hr : 0 < r) (hrr : r = (r1 : ℝ) / r2) {V : D → ℝ} (hV : IsValue Γ V)
    (hE : ExistenceTheorem (scale Γ (1 / r) (one_div_pos.mpr hr)))
    {q amax H Ωh s K0 ζ d0 : ℕ} (hq : q = normQ Γ c r1) (hamax : amax = normAmax Γ b c r2)
    (hH : H = Fintype.card D * (q + 2 * Fintype.card D * amax) ^ Fintype.card D)
    (hΩh : Ωh = Nat.size (Fintype.card D * max amax q))
    (hs1 : 2 * Fintype.card D ≤ 2 ^ s)
    (hs2 : 64 * H * (3 * Fintype.card D * (2 * s + 4 * Fintype.card D * Ωh + 2)) ≤ 2 ^ s)
    (hK0 : K0 = Nat.size (256 * H * Fintype.card D * amax) + Nat.size (2 * q))
    (hζ : ζ = max (6 * K0) (Nat.size (512 * H) + 1))
    (hd0 : 2 * ((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ) ≤ 128 * 2 ^ d0) :
    (∃ Afin c', Loop ((scale Γ (1 / r) (one_div_pos.mpr hr)).G (surE ζ)
        (1 / (2 ^ 15 * (H : ℝ))) (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c') ∧
    ∀ Afin c', Loop ((scale Γ (1 / r) (one_div_pos.mpr hr)).G (surE ζ)
        (1 / (2 ^ 15 * (H : ℝ))) (2 ^ s)) (256 * ((2 ^ s : ℕ) + 1))
        (fun _ => -((2 ^ 15 * H * 2 ^ s * (Ωh + 1) + 2 ^ s + 1 : ℕ) : ℤ)) 128 d0 Afin c' →
      c' ≤ 128 * (d0 + 1) ∧ ∀ d, (-(2 ^ 13 * ((2 ^ s : ℕ) : ℤ)) ≤ Afin d ↔ r ≤ V d) := by
  subst hq hamax
  exact main_correctness_threshold Γ hA hr hV hE
    (isNormalised_rational hb hc hm hr1 hr2 hr hrr) hH hΩh hs1 hs2 hK0 hζ hd0

end rational

end EntropyGames
