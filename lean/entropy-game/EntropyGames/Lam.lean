/-
Section 6 of the paper: bookkeeping for the numbers `λ_i`.
The class of a state, existence of a nontrivial class accessible from every state,
Lemma 6.1(a) (the part on `λ_i`) and Lemma 6.1(c).
-/
import EntropyGames.Lemma61

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

variable {ι : Type*} [Fintype ι]

/-- The set of states accessible from `i`. -/
noncomputable def reach (M : ι → ι → ℝ) (i : ι) : Finset ι := Finset.univ.filter fun j => Acc M i j

/-- The class of `i`. -/
noncomputable def cls (M : ι → ι → ℝ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => Acc M i j ∧ Acc M j i

theorem mem_reach {M : ι → ι → ℝ} {i j : ι} : j ∈ reach M i ↔ Acc M i j := by simp [reach]

theorem mem_cls {M : ι → ι → ℝ} {i j : ι} : j ∈ cls M i ↔ Acc M i j ∧ Acc M j i := by
  simp [cls]

theorem self_mem_cls (M : ι → ι → ℝ) (i : ι) : i ∈ cls M i :=
  mem_cls.mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem self_mem_reach (M : ι → ι → ℝ) (i : ι) : i ∈ reach M i :=
  mem_reach.mpr Relation.ReflTransGen.refl

theorem Acc.of_arc {M : ι → ι → ℝ} {i j : ι} (h : 0 < M i j) : Acc M i j :=
  Relation.ReflTransGen.single (r := fun i j => 0 < M i j) h

theorem isClass_cls (M : ι → ι → ℝ) (i : ι) : IsClass M (cls M i) := by
  refine ⟨⟨i, self_mem_cls M i⟩, fun a ha j => ?_⟩
  rw [mem_cls] at ha
  rw [mem_cls]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨ha.2.trans h1, h2.trans ha.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ha.1.trans h1, h2.trans ha.2⟩

theorem reach_subset {M : ι → ι → ℝ} {i j : ι} (h : Acc M i j) : reach M j ⊆ reach M i := by
  intro x hx
  rw [mem_reach] at hx ⊢
  exact h.trans hx

/-- From every state a class without outgoing arcs is accessible. -/
theorem exists_closed_class (M : ι → ι → ℝ) (i : ι) :
    ∃ j, Acc M i j ∧ ∀ a ∈ cls M j, ∀ b, 0 < M a b → b ∈ cls M j := by
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (reach M i) (fun j => (reach M j).card)
    ⟨i, self_mem_reach M i⟩
  rw [mem_reach] at hj
  refine ⟨j, hj, fun a ha b hab => ?_⟩
  rw [mem_cls] at ha
  have hjb : Acc M j b := ha.1.trans (Acc.of_arc hab)
  have hsub : reach M b ⊆ reach M j := reach_subset hjb
  have hcard := hmin b (mem_reach.mpr (hj.trans hjb))
  have heq : reach M b = reach M j := Finset.eq_of_subset_of_card_le hsub hcard
  have : j ∈ reach M b := heq ▸ self_mem_reach M j
  exact mem_cls.mpr ⟨hjb, mem_reach.mp this⟩

/-- "From every state some nontrivial class is accessible" (paragraph "Classes"). -/
theorem exists_nontrivial_class {M : ι → ι → ℝ} (hrow : ∀ i, ∃ j, 0 < M i j) (i : ι) :
    ∃ C, IsNontrivialClass M C ∧ ∃ j ∈ C, Acc M i j := by
  obtain ⟨j, hj, hclosed⟩ := exists_closed_class M i
  obtain ⟨b, hb⟩ := hrow j
  exact ⟨cls M j, ⟨isClass_cls M j, j, self_mem_cls M j, b,
    hclosed j (self_mem_cls M j) b hb, hb⟩, j, self_mem_cls M j, hj⟩

/-- The set whose maximum is `λ_i`. -/
def lamSet (M : ι → ι → ℝ) (i : ι) : Set ℝ :=
  {x | ∃ C ρ U, IsNontrivialClass M C ∧ (∃ j ∈ C, Acc M i j) ∧ IsPerronPair M C ρ U ∧
    x = Real.log ρ}

theorem lam_eq_sSup (M : ι → ι → ℝ) (i : ι) : lam M i = sSup (lamSet M i) := rfl

section

variable {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}

theorem lamSet_nonempty (hM : MatHyp M mmin mmax Ω) (i : ι) : (lamSet M i).Nonempty := by
  obtain ⟨C, hC, hacc⟩ := exists_nontrivial_class hM.row i
  obtain ⟨ρ, U, hU⟩ := perron_frobenius hM.nonneg hC
  exact ⟨Real.log ρ, C, ρ, U, hC, hacc, hU, rfl⟩

theorem lamSet_abs_le (hM : MatHyp M mmin mmax Ω) (i : ι) {x : ℝ} (hx : x ∈ lamSet M i) :
    |x| ≤ Ω := by
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨C, ρ, U, hC, _, hU, rfl⟩ := hx
  exact (lemma_6_1_a_class hM hC hU).2

theorem lamSet_bddAbove (hM : MatHyp M mmin mmax Ω) (i : ι) : BddAbove (lamSet M i) :=
  ⟨Ω, fun _ hx => (abs_le.mp (lamSet_abs_le hM i hx)).2⟩

/-- `ln ρ_C ≤ λ_i` for every nontrivial class `C` accessible from `i`. -/
theorem log_le_lam (hM : MatHyp M mmin mmax Ω) {i : ι} {C : Finset ι}
    (hC : IsNontrivialClass M C) (hacc : ∃ j ∈ C, Acc M i j) {ρ : ℝ} {U : ι → ℝ}
    (hU : IsPerronPair M C ρ U) : Real.log ρ ≤ lam M i :=
  le_csSup (lamSet_bddAbove hM i) ⟨C, ρ, U, hC, hacc, hU, rfl⟩

/-- `λ_i ≤ x` if `ln ρ_C ≤ x` for every nontrivial class `C` accessible from `i`. -/
theorem lam_le (hM : MatHyp M mmin mmax Ω) {i : ι} {x : ℝ}
    (h : ∀ C ρ U, IsNontrivialClass M C → (∃ j ∈ C, Acc M i j) → IsPerronPair M C ρ U →
      Real.log ρ ≤ x) : lam M i ≤ x := by
  refine csSup_le (lamSet_nonempty hM i) ?_
  rintro _ ⟨C, ρ, U, hC, hacc, hU, rfl⟩
  exact h C ρ U hC hacc hU

/-- Lemma 6.1(a), the part on `λ_i`: `|λ_i| ≤ Ω`. -/
theorem lemma_6_1_a_lam (hM : MatHyp M mmin mmax Ω) (i : ι) : |lam M i| ≤ Ω := by
  obtain ⟨x, hx⟩ := lamSet_nonempty hM i
  have h1 := abs_le.mp (lamSet_abs_le hM i hx)
  have h2 : x ≤ lam M i := le_csSup (lamSet_bddAbove hM i) hx
  have h3 : lam M i ≤ Ω := csSup_le ⟨x, hx⟩ fun y hy => (abs_le.mp (lamSet_abs_le hM i hy)).2
  rw [abs_le]
  constructor <;> linarith [h1.1]

/-- `λ` is nonincreasing along accessibility. -/
theorem lam_mono_acc (hM : MatHyp M mmin mmax Ω) {i j : ι} (hij : Acc M i j) :
    lam M j ≤ lam M i :=
  lam_le hM fun _ _ _ hC ⟨k, hk, hjk⟩ hU => log_le_lam hM hC ⟨k, hk, hij.trans hjk⟩ hU

/-- Lemma 6.1(c): if `i → j` then `λ_j ≤ λ_i`. -/
theorem lemma_6_1_c (hM : MatHyp M mmin mmax Ω) {i j : ι} (hij : 0 < M i j) :
    lam M j ≤ lam M i :=
  lam_mono_acc hM (Acc.of_arc hij)

/-- `λ` is constant on a class. -/
theorem lam_eq_of_mem_cls (hM : MatHyp M mmin mmax Ω) {i a : ι} (ha : a ∈ cls M i) :
    lam M a = lam M i := by
  rw [mem_cls] at ha
  exact le_antisymm (lam_mono_acc hM ha.1) (lam_mono_acc hM ha.2)

end

section attained

variable {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}

/-- The set of the numbers `ln ρ_C` is finite (one number for each class). -/
theorem lamSet_finite (hM : ∀ i j, 0 ≤ M i j) (i : ι) : (lamSet M i).Finite := by
  let F : Finset ι → ℝ := fun C =>
    if h : ∃ ρ, ∃ U, IsPerronPair M C ρ U then Real.log (Classical.choose h) else 0
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨C, ρ, U, _, _, hU, rfl⟩
  refine ⟨C, ?_⟩
  have h : ∃ ρ, ∃ U, IsPerronPair M C ρ U := ⟨ρ, U, hU⟩
  simp only [F, dif_pos h]
  obtain ⟨U', hU'⟩ := Classical.choose_spec h
  rw [perron_root_unique hM hU' hU]

/-- The maximum in the definition of `λ_i` is attained: `λ_i = ln ρ_C` for some nontrivial
class `C` accessible from `i`. -/
theorem lam_mem (hM : MatHyp M mmin mmax Ω) (i : ι) :
    ∃ C ρ U, IsNontrivialClass M C ∧ (∃ j ∈ C, Acc M i j) ∧ IsPerronPair M C ρ U ∧
      lam M i = Real.log ρ :=
  (lamSet_nonempty hM i).csSup_mem (lamSet_finite hM.nonneg i)

end attained

end EntropyGames
