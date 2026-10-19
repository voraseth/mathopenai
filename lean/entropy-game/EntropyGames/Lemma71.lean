/-
Section 7 of the paper: Lemma 7.1(c) and the consequences of Lemma 7.1(a) used later, with
the conclusion of Lemma 7.1(a) (`χ_d = min_σ max_τ λ^{στ}_d`) as an explicit hypothesis:
  `ha1 : ∃ σ, ∀ τ, λ^{στ}_d ≤ χ_d`  and  `ha2 : ∀ σ, ∃ τ, χ_d ≤ λ^{στ}_d`.
Lemma 7.1(a) itself (which uses the cited existence theorem and Lemma 6.1(d)) is not proved
here.
-/
import EntropyGames.Theorem62
import EntropyGames.Value
import EntropyGames.Decision

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

variable {D T P : Type*} [Fintype D] (Γ : EntropyGame D T P)

/-- The normalised game of Section 2: weights `a_e / q` with integers `1 ≤ a_e ≤ a_max`. -/
def IsNormalised (q amax : ℕ) : Prop :=
  1 ≤ q ∧ ∀ p, ∀ j ∈ Γ.outP p, ∃ a : ℕ, 1 ≤ a ∧ a ≤ amax ∧ Γ.m p j = (a : ℝ) / q

variable {Γ} {q amax : ℕ}

/-- Section 7, first sentence: `Ω = ln(n max(a_max, q))` satisfies Equation (6.1) for every
matrix `M^{στ}` of the normalised game, with `m_min = 1/q`, `m_max = a_max`. -/
theorem polMatrix_matHyp (hnorm : IsNormalised Γ q amax) (σ : DespotPolicy Γ)
    (τ : TribunePolicy Γ) :
    MatHyp (polMatrix Γ σ τ) (1 / (q : ℝ)) (amax : ℝ)
      (Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ))) := by
  obtain ⟨hq, hw⟩ := hnorm
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨?_, ?_, by positivity, ?_, ?_, ?_⟩
  · intro d d'
    unfold polMatrix
    split_ifs with h
    · exact (Γ.m_pos _ _ h).le
    · exact le_rfl
  · intro d
    obtain ⟨j, hj⟩ := Γ.outP_nonempty (τ.move (σ.move d))
    exact ⟨j, by unfold polMatrix; rw [if_pos hj]; exact Γ.m_pos _ _ hj⟩
  · intro d d' hpos
    unfold polMatrix at hpos ⊢
    split_ifs at hpos ⊢ with h
    · obtain ⟨a, ha1, _, hm⟩ := hw _ _ h
      rw [hm]
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      gcongr
    · exact absurd hpos (lt_irrefl _)
  · intro d d'
    unfold polMatrix
    split_ifs with h
    · obtain ⟨a, _, ha2, hm⟩ := hw _ _ h
      rw [hm, div_le_iff₀ (by linarith)]
      have : (a : ℝ) ≤ amax := by exact_mod_cast ha2
      have h0 : (0 : ℝ) ≤ amax := by positivity
      nlinarith
    · positivity
  · have e : max (amax : ℝ) (max (1 / (1 / (q : ℝ))) 1) = ((max amax q : ℕ) : ℝ) := by
      rw [one_div_one_div, max_eq_left hq', Nat.cast_max]
    rw [e]

/-- `Ψ_{M^{στ}}(t)_d = γ ℓ_{τ(σ(d))}(t)`. -/
theorem Psi_polMatrix (γ : ℝ) (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) (t : D → ℝ) (d : D) :
    Psi γ (polMatrix Γ σ τ) t d = γ * Γ.ell (τ.move (σ.move d)) t := by
  unfold Psi polMatrix EntropyGame.ell lse
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Lemma 7.1(c)**, given the conclusion of Lemma 7.1(a) at `d`: if `N ≥ 2n` and `v` is the
fixed point of `γ f`, then `|θ v_d - χ_d| ≤ θ R`, `R` as in Theorem 6.2 with
`Ω = ln(n max(a_max, q))`. -/
theorem lemma_7_1_c_of_a (hnorm : IsNormalised Γ q amax) {N : ℕ} (hN : 2 ≤ N)
    (hNn : 2 * Fintype.card D ≤ N) {v : D → ℝ}
    (hv : ∀ d, v d = (1 - 1 / (N : ℝ)) * Γ.f v d) {χ : D → ℝ} (d : D)
    (ha1 : ∃ σ : DespotPolicy Γ, ∀ τ : TribunePolicy Γ, lam (polMatrix Γ σ τ) d ≤ χ d)
    (ha2 : ∀ σ : DespotPolicy Γ, ∃ τ : TribunePolicy Γ, χ d ≤ lam (polMatrix Γ σ τ) d) :
    |v d / N - χ d|
      ≤ 3 * Fintype.card D * (2 * Real.log N
          + 4 * Fintype.card D * Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ)) + 2) / N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hθpos : 0 < 1 / (N : ℝ) := by positivity
  have hθ1 : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]; linarith
  have hγ0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by linarith
  have hγ1 : 1 - 1 / (N : ℝ) < 1 := by linarith
  have hex : ∀ (σ : DespotPolicy Γ) (τ : TribunePolicy Γ),
      ∃ w : D → ℝ, Psi (1 - 1 / (N : ℝ)) (polMatrix Γ σ τ) w = w := fun σ τ =>
    ((Psi_isDiscounted hγ0 (polMatrix_matHyp hnorm σ τ).nonneg
      (polMatrix_matHyp hnorm σ τ).row).existsUnique_fixed hγ0 hγ1).exists
  choose vpol hvpol using hex
  have hypol : ∀ σ τ d, vpol σ τ d
      = (1 - 1 / (N : ℝ)) * Γ.ell (τ.move (σ.move d)) (vpol σ τ) := fun σ τ d =>
    (congrFun (hvpol σ τ) d).symm.trans (Psi_polMatrix _ σ τ _ d)
  obtain ⟨⟨σs, h1⟩, h2⟩ := minmax_fixed_point Γ hγ0 hγ1 (fun p => Γ.ell p)
    (fun p => Γ.ell_mono p) (fun p t c => Γ.ell_shift p t c) hv vpol hypol
  have T62 := fun σ τ => abs_le.mp
    (theorem_6_2 (polMatrix_matHyp hnorm σ τ) hN hNn (hvpol σ τ) d)
  set Rθ : ℝ := 1 / (N : ℝ) * (3 * Fintype.card D * (2 * Real.log N
      + 4 * Fintype.card D * Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ)) + 2)) with hRθ
  have e1 : v d / N = 1 / (N : ℝ) * v d := by ring
  have e2 : 3 * Fintype.card D * (2 * Real.log N
      + 4 * Fintype.card D * Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ)) + 2) / N = Rθ := by
    rw [hRθ]; ring
  rw [e1, e2, abs_le]
  constructor
  · -- χ_d ≤ λ^{σ*τ}_d ≤ θ v^{σ*τ}_d + θR ≤ θ v_d + θR
    obtain ⟨τ, hτ⟩ := ha2 σs
    have h3 := (T62 σs τ).1
    have h4 := mul_le_mul_of_nonneg_left (h1 τ d) hθpos.le
    linarith
  · -- θ v_d ≤ θ v^{σ°τ}_d ≤ λ^{σ°τ}_d + θR ≤ χ_d + θR
    obtain ⟨σo, hσo⟩ := ha1
    obtain ⟨τ, hτ⟩ := h2 σo
    have h3 := (T62 σo τ).2
    have h4 := mul_le_mul_of_nonneg_left (hτ d) hθpos.le
    linarith [hσo τ]

/-- `|χ_d| ≤ Ω` (used in the proof of Theorem 1.1), given the conclusion of Lemma 7.1(a). -/
theorem chi_bound_of_a (hnorm : IsNormalised Γ q amax) {χ : D → ℝ} (d : D)
    (ha1 : ∃ σ : DespotPolicy Γ, ∀ τ : TribunePolicy Γ, lam (polMatrix Γ σ τ) d ≤ χ d)
    (ha2 : ∀ σ : DespotPolicy Γ, ∃ τ : TribunePolicy Γ, χ d ≤ lam (polMatrix Γ σ τ) d) :
    |χ d| ≤ Real.log (Fintype.card D * ((max amax q : ℕ) : ℝ)) := by
  obtain ⟨σo, hσo⟩ := ha1
  obtain ⟨τ, hτ⟩ := ha2 σo
  have h1 := abs_le.mp (lemma_6_1_a_lam (polMatrix_matHyp hnorm σo τ) d)
  rw [abs_le]
  constructor <;> linarith [hσo τ]

/-- `χ_d` is one of the numbers `λ^{στ}_d` (used in the proof of Lemma 7.2), given the
conclusion of Lemma 7.1(a). -/
theorem chi_eq_lam_of_a {χ : D → ℝ} (d : D)
    (ha1 : ∃ σ : DespotPolicy Γ, ∀ τ : TribunePolicy Γ, lam (polMatrix Γ σ τ) d ≤ χ d)
    (ha2 : ∀ σ : DespotPolicy Γ, ∃ τ : TribunePolicy Γ, χ d ≤ lam (polMatrix Γ σ τ) d) :
    ∃ (σ : DespotPolicy Γ) (τ : TribunePolicy Γ), χ d = lam (polMatrix Γ σ τ) d := by
  obtain ⟨σo, hσo⟩ := ha1
  obtain ⟨τ, hτ⟩ := ha2 σo
  exact ⟨σo, τ, le_antisymm hτ (hσo τ)⟩

end EntropyGames
