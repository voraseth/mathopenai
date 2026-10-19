/-
Section 6 of the paper: the standing hypotheses (Equation (5) of the paper),
the numbers `λ_i`, Lemma 6.1(a),(b) for a nontrivial class, and the uniqueness of the Perron
root of a class.
-/
import EntropyGames.Classes

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

variable {ι : Type*} [Fintype ι]

/-- The standing hypotheses of Section 6: `M ≥ 0`, every row has a positive entry, the positive
entries lie in `[m_min, m_max]`, and `Ω ≥ ln(n max(m_max, 1/m_min, 1))`. -/
structure MatHyp (M : ι → ι → ℝ) (mmin mmax Ω : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ M i j
  row : ∀ i, ∃ j, 0 < M i j
  mmin_pos : 0 < mmin
  lo : ∀ i j, 0 < M i j → mmin ≤ M i j
  hi : ∀ i j, M i j ≤ mmax
  hΩ : Real.log (Fintype.card ι * max mmax (max (1 / mmin) 1)) ≤ Ω

/-- `λ_i = max {ln ρ_C : C nontrivial and accessible from i}`. -/
noncomputable def lam (M : ι → ι → ℝ) (i : ι) : ℝ :=
  sSup {x | ∃ C ρ U, IsNontrivialClass M C ∧ (∃ j ∈ C, Acc M i j) ∧ IsPerronPair M C ρ U ∧
    x = Real.log ρ}

/-- Consequences of Equation (6.1): `n m_max ≤ e^Ω`, `1/m_min ≤ e^Ω`, `Ω ≥ 0`. -/
theorem MatHyp.exp_bounds [Nonempty ι] {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}
    (h : MatHyp M mmin mmax Ω) :
    Fintype.card ι * mmax ≤ Real.exp Ω ∧ 1 / mmin ≤ Real.exp Ω ∧ 0 ≤ Ω ∧ 0 < mmax := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmaxpos : 0 < mmax := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨j, hj⟩ := h.row i
    exact hj.trans_le (h.hi i j)
  have hmin0 := h.mmin_pos
  have hexpΩ : Fintype.card ι * max mmax (max (1 / mmin) 1) ≤ Real.exp Ω :=
    (Real.log_le_iff_le_exp (by positivity)).mp h.hΩ
  have hA1 : Fintype.card ι * mmax ≤ Real.exp Ω :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)) hexpΩ
  have hA2 : 1 / mmin ≤ Real.exp Ω := by
    refine le_trans ?_ hexpΩ
    calc 1 / mmin ≤ max mmax (max (1 / mmin) 1) := (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ Fintype.card ι * max mmax (max (1 / mmin) 1) :=
        le_mul_of_one_le_left (by positivity) hn
  have hA3 : (1 : ℝ) ≤ Real.exp Ω := by
    refine le_trans ?_ hexpΩ
    calc (1 : ℝ) ≤ max mmax (max (1 / mmin) 1) := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ Fintype.card ι * max mmax (max (1 / mmin) 1) :=
        le_mul_of_one_le_left (by positivity) hn
  exact ⟨hA1, hA2, by rw [← Real.exp_le_exp, Real.exp_zero]; exact hA3, hmaxpos⟩

/-- A class, as a matrix on the subtype, satisfies the cut condition. -/
theorem IsClass.subtype_cut {M : ι → ι → ℝ} {C : Finset ι} (hC : IsClass M C)
    (S : Finset {j // j ∈ C}) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < M i.1 j.1 := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ : ∃ t, t ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hSu (Finset.eq_univ_of_forall hcon)
  obtain ⟨a, haC, haS, b, hbC, hbS, hab⟩ :=
    hC.cut {x | ∃ h : x ∈ C, (⟨x, h⟩ : {j // j ∈ C}) ∈ S} ⟨s.1, s.2, s.2, hs⟩
      ⟨t.1, t.2, fun ⟨_, h'⟩ => ht h'⟩
  obtain ⟨_, haS'⟩ := haS
  exact ⟨⟨a, haC⟩, haS', ⟨b, hbC⟩, fun h' => hbS ⟨hbC, h'⟩, hab⟩

/-- Lemma 6.1(a), for a class: `m_min ≤ ρ_C ≤ n m_max` and `|ln ρ_C| ≤ Ω`. -/
theorem lemma_6_1_a_class [Nonempty ι] {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}
    (hM : MatHyp M mmin mmax Ω) {C : Finset ι} (hC : IsNontrivialClass M C) {ρ : ℝ}
    {U : ι → ℝ} (hU : IsPerronPair M C ρ U) :
    (mmin ≤ ρ ∧ ρ ≤ Fintype.card ι * mmax) ∧ |Real.log ρ| ≤ Ω := by
  obtain ⟨hρ, hU1, _, hMU⟩ := hU
  obtain ⟨i0, hi0⟩ := hC.1.1
  haveI : Nonempty {j // j ∈ C} := ⟨⟨i0, hi0⟩⟩
  obtain ⟨hA1, hA2, hΩ0, hmaxpos⟩ := hM.exp_bounds
  have hb := perron_root_bounds (ι := {j // j ∈ C}) (M := fun i j => M i.1 j.1)
    (U := fun i => U i.1) (ρ := ρ) (mmin := mmin) (mmax := mmax)
    (fun i => lt_of_lt_of_le one_pos (hU1 i.1 i.2))
    (fun i => by rw [Finset.sum_coe_sort C (fun j => M i.1 j * U j)]; exact hMU i.1 i.2)
    (fun i j => hM.nonneg _ _)
    (fun i => by obtain ⟨j, hj, hij⟩ := hC.row i.2; exact ⟨⟨j, hj⟩, hij⟩)
    (fun i j h => hM.lo _ _ h) (fun i j => hM.hi _ _)
  have hcard : (Fintype.card {j // j ∈ C} : ℝ) ≤ Fintype.card ι := by
    rw [Fintype.card_coe]; exact_mod_cast Finset.card_le_univ C
  have hhi : ρ ≤ Fintype.card ι * mmax :=
    hb.2.trans (mul_le_mul_of_nonneg_right hcard hmaxpos.le)
  refine ⟨⟨hb.1, hhi⟩, ?_⟩
  rw [abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le hρ, Real.exp_neg]
    refine le_trans ?_ hb.1
    rw [inv_le_comm₀ (Real.exp_pos _) hM.mmin_pos, ← one_div]
    exact hA2
  · exact (Real.log_le_iff_le_exp hρ).mpr (hhi.trans hA1)

/-- Lemma 6.1(b): `0 ≤ ln U^C_i ≤ O_n = 2(n-1)Ω` for `i ∈ C`. -/
theorem lemma_6_1_b [Nonempty ι] {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}
    (hM : MatHyp M mmin mmax Ω) {C : Finset ι} (hC : IsNontrivialClass M C) {ρ : ℝ}
    {U : ι → ℝ} (hU : IsPerronPair M C ρ U) :
    ∀ i ∈ C, 0 ≤ Real.log (U i) ∧ Real.log (U i) ≤ 2 * (Fintype.card ι - 1) * Ω := by
  obtain ⟨⟨hρlo, hρhi⟩, _⟩ := lemma_6_1_a_class hM hC hU
  obtain ⟨hρ, hU1, ⟨k0, hk0C, hk0⟩, hMU⟩ := hU
  obtain ⟨hA1, hA2, hΩ0, hmaxpos⟩ := hM.exp_bounds
  have hUpos : ∀ i ∈ C, 0 < U i := fun i hi => lt_of_lt_of_le one_pos (hU1 i hi)
  intro i hi
  refine ⟨Real.log_nonneg (hU1 i hi), ?_⟩
  set c := Real.exp (2 * Ω) with hc
  have hρm : ρ / mmin ≤ c := by
    rw [hc, two_mul, Real.exp_add, div_eq_mul_one_div]
    exact mul_le_mul (hρhi.trans hA1) hA2 (by have := hM.mmin_pos; positivity) (Real.exp_pos _).le
  have hc1 : 1 ≤ c := by
    rw [hc, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have harc : ∀ a b : {j // j ∈ C}, 0 < M a.1 b.1 → U b.1 ≤ c * U a.1 := by
    intro a b hab
    have h1 : M a.1 b.1 * U b.1 ≤ ρ * U a.1 := by
      rw [← hMU a.1 a.2]
      exact Finset.single_le_sum (f := fun j => M a.1 j * U j)
        (fun j hj => mul_nonneg (hM.nonneg _ _) (hUpos j hj).le) b.2
    have h2 : mmin * U b.1 ≤ ρ * U a.1 :=
      (mul_le_mul_of_nonneg_right (hM.lo _ _ hab) (hUpos b.1 b.2).le).trans h1
    have h3 : U b.1 ≤ ρ / mmin * U a.1 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hM.mmin_pos]; linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hρm (hUpos a.1 a.2).le)
  have h1 := le_pow_mul_of_arcs (ι := {j // j ∈ C}) (M := fun a b => M a.1 b.1)
    (U := fun a => U a.1) hc1 (fun S hS hSu => hC.1.subtype_cut S hS hSu) harc
    (i0 := ⟨k0, hk0C⟩) (by simp [hk0]) ⟨i, hi⟩
  simp only [hk0, mul_one] at h1
  have hcardC : Fintype.card {j // j ∈ C} - 1 ≤ Fintype.card ι - 1 := by
    rw [Fintype.card_coe]; exact Nat.sub_le_sub_right (Finset.card_le_univ C) 1
  have h2 : U i ≤ c ^ (Fintype.card ι - 1) := h1.trans (pow_le_pow_right₀ hc1 hcardC)
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos]; simp
  calc Real.log (U i) ≤ Real.log (c ^ (Fintype.card ι - 1)) := Real.log_le_log (hUpos i hi) h2
    _ = 2 * (Fintype.card ι - 1) * Ω := by rw [Real.log_pow, hc, Real.log_exp, hcast]; ring

/-- The Perron root of a class does not depend on the eigenvector (stated in Lemma 6.1(d) of
the paper; proved here directly by comparing two eigenvectors at the index where their ratio
is largest). -/
theorem perron_root_unique {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j) {C : Finset ι}
    {ρ ρ' : ℝ} {U U' : ι → ℝ} (hU : IsPerronPair M C ρ U) (hU' : IsPerronPair M C ρ' U') :
    ρ = ρ' := by
  have key : ∀ {ρ ρ' : ℝ} {U U' : ι → ℝ}, IsPerronPair M C ρ U → IsPerronPair M C ρ' U' →
      ρ' ≤ ρ := by
    intro ρ ρ' U U' hU hU'
    obtain ⟨hρ, hU1, ⟨k0, hk0C, _⟩, hMU⟩ := hU
    obtain ⟨hρ', hU1', _, hMU'⟩ := hU'
    have hUpos : ∀ i ∈ C, 0 < U i := fun i hi => lt_of_lt_of_le one_pos (hU1 i hi)
    have hUpos' : ∀ i ∈ C, 0 < U' i := fun i hi => lt_of_lt_of_le one_pos (hU1' i hi)
    obtain ⟨i, hiC, hi⟩ := Finset.exists_max_image C (fun i => U' i / U i) ⟨k0, hk0C⟩
    set t := U' i / U i with ht
    have htU : ∀ j ∈ C, U' j ≤ t * U j := fun j hj => by
      have := hi j hj
      rwa [div_le_iff₀ (hUpos j hj)] at this
    have h1 : ρ' * U' i ≤ t * (ρ * U i) := by
      rw [← hMU' i hiC, ← hMU i hiC, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have := mul_le_mul_of_nonneg_left (htU j hj) (hM i j)
      linarith
    have h2 : t * U i = U' i := by rw [ht]; field_simp [(hUpos i hiC).ne']
    have h3 : ρ' * U' i ≤ ρ * U' i := by
      calc ρ' * U' i ≤ t * (ρ * U i) := h1
        _ = ρ * (t * U i) := by ring
        _ = ρ * U' i := by rw [h2]
    exact le_of_mul_le_mul_right h3 (hUpos' i hiC)
  exact le_antisymm (key hU' hU) (key hU hU')

end EntropyGames
