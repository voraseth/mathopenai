/-
Section 7 of the paper: Lemma 7.1(a), `χ_d = min_σ max_τ λ^{στ}_d`, from the cited existence
theorem (hypothesis `IsValueWithPolicies`) and Lemma 6.1(d); and the unconditional forms of
Lemma 7.1(c), of `|χ_d| ≤ Ω` and of "χ_d is one of the λ^{στ}_d".
-/
import EntropyGames.Lemma71
import EntropyGames.Lemma61d

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

/-- Every nonnegative matrix with nonzero rows satisfies the standing hypotheses of Section 6
for suitable `m_min`, `m_max`, `Ω`. -/
theorem exists_matHyp {ι : Type*} [Fintype ι] {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∃ j, 0 < M i j) : ∃ mmin mmax Ω : ℝ, MatHyp M mmin mmax Ω := by
  obtain ⟨mmin, hmin0, hmin⟩ : ∃ mmin : ℝ, 0 < mmin ∧ ∀ i j, 0 < M i j → mmin ≤ M i j := by
    by_cases hne : ((Finset.univ : Finset (ι × ι)).filter fun p => 0 < M p.1 p.2).Nonempty
    · obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image _ (fun p : ι × ι => M p.1 p.2) hne
      refine ⟨M p.1 p.2, (Finset.mem_filter.mp hp).2, fun i j hij => ?_⟩
      exact hpmin (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      exact absurd ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩ hne
  refine ⟨mmin, ∑ i, ∑ j, M i j, _, hM, hrow, hmin0, hmin, fun i j => ?_, le_rfl⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, M i j)
    (fun i _ => Finset.sum_nonneg fun j _ => hM i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => M i j) (fun j _ => hM i j) (Finset.mem_univ j)

variable {D T P : Type*} [Fintype D] (Γ : EntropyGame D T P)

theorem polMatrix_nonneg (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) (d d' : D) :
    0 ≤ polMatrix Γ σ τ d d' := by
  unfold polMatrix
  split_ifs with h
  · exact (Γ.m_pos _ _ h).le
  · exact le_rfl

theorem polMatrix_row (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) (d : D) :
    ∃ d', 0 < polMatrix Γ σ τ d d' := by
  obtain ⟨j, hj⟩ := Γ.outP_nonempty (τ.move (σ.move d))
  exact ⟨j, by unfold polMatrix; rw [if_pos hj]; exact Γ.m_pos _ _ hj⟩

/-- Proof of Lemma 7.1(a), first step: `R^∞_d(σ, τ) = exp(λ^{στ}_d)` for policies. -/
theorem payInf_policy (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) (d : D) :
    payInf σ.toStrategy τ.toStrategy d = Real.exp (lam (polMatrix Γ σ τ) d) := by
  obtain ⟨mmin, mmax, Ω, hM⟩ := exists_matHyp (polMatrix_nonneg Γ σ τ) (polMatrix_row Γ σ τ)
  have hlim := lemma_6_1_d hM d
  have hlim2 := (Real.continuous_exp.tendsto _).comp hlim
  unfold payInf
  refine Filter.Tendsto.limsup_eq ?_
  refine hlim2.congr fun k => ?_
  simp only [Function.comp]
  rw [pay_policy, ← pw_eq, Real.rpow_def_of_pos (pw_pos hM.nonneg hM.row k d), mul_comm]

/-- **Lemma 7.1(a)**: `χ_d = min_σ max_τ λ^{στ}_d`, with `χ_d = ln V_d`, written without `min`
and `max`: some `σ` has all `λ^{στ}_d ≤ χ_d`, and every `σ` has some `τ` with
`λ^{στ}_d ≥ χ_d`.  Also `V_d > 0`. -/
theorem lemma_7_1_a {V : D → ℝ} (hV : IsValueWithPolicies Γ V) (d : D) :
    0 < V d ∧
    (∃ σ : DespotPolicy Γ, ∀ τ : TribunePolicy Γ, lam (polMatrix Γ σ τ) d ≤ Real.log (V d)) ∧
    (∀ σ : DespotPolicy Γ, ∃ τ : TribunePolicy Γ, Real.log (V d) ≤ lam (polMatrix Γ σ τ) d) := by
  obtain ⟨σs, τs, h⟩ := hV
  have hpos : 0 < V d := by
    have := (h d σs.toStrategy τs.toStrategy).2
    rw [payInf_policy] at this
    exact lt_of_lt_of_le (Real.exp_pos _) this
  refine ⟨hpos, ⟨σs, fun τ => ?_⟩, fun σ => ⟨τs, ?_⟩⟩
  · have := (h d σs.toStrategy τ.toStrategy).2
    rw [payInf_policy] at this
    exact (Real.le_log_iff_exp_le hpos).mpr this
  · have := (h d σ.toStrategy τs.toStrategy).1
    rw [payInf_policy] at this
    exact (Real.log_le_iff_le_exp hpos).mpr this

/-- **Lemma 7.1(c)**: `|θ v_d - χ_d| ≤ θ R` for the fixed point `v` of `γ f`, `N ≥ 2n`,
in the normalised game with `Ω = ln(n max(a_max, q))`. -/
theorem lemma_7_1_c {V : D → ℝ} (hV : IsValueWithPolicies Γ V) {q amax : ℕ}
    (hnorm : IsNormalised Γ q amax) {N : ℕ} (hN : 2 ≤ N) (hNn : 2 * Fintype.card D ≤ N)
    {v : D → ℝ} (hv : ∀ d, v d = (1 - 1 / (N : ℝ)) * Γ.f v d) (d : D) :
    |v d / N - Real.log (V d)|
      ≤ 3 * Fintype.card D * (2 * Real.log N
          + 4 * Fintype.card D * Real.log (Fintype.card D * max amax q) + 2) / N :=
  lemma_7_1_c_of_a hnorm hN hNn hv (χ := fun d => Real.log (V d)) d
    (lemma_7_1_a Γ hV d).2.1 (lemma_7_1_a Γ hV d).2.2

/-- `|χ_d| ≤ Ω` (used in the proof of Theorem 1.1; from Lemma 6.1(a) and Lemma 7.1(a)). -/
theorem chi_bound {V : D → ℝ} (hV : IsValueWithPolicies Γ V) {q amax : ℕ}
    (hnorm : IsNormalised Γ q amax) (d : D) :
    |Real.log (V d)| ≤ Real.log (Fintype.card D * max amax q) :=
  chi_bound_of_a hnorm (χ := fun d => Real.log (V d)) d
    (lemma_7_1_a Γ hV d).2.1 (lemma_7_1_a Γ hV d).2.2

end EntropyGames
