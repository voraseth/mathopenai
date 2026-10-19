/-
Section 6 of the paper, paragraph "Classes": accessibility, classes, nontrivial classes, and
the Perron–Frobenius theorem for a nontrivial class, with the normalisation `min U = 1`.
-/
import EntropyGames.PerronFrobenius

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

variable {ι : Type*}

/-- `j` is accessible from `i` (a path of length `≥ 0`). -/
def Acc (M : ι → ι → ℝ) : ι → ι → Prop := Relation.ReflTransGen fun i j => 0 < M i j

/-- `C` is a class (a strongly connected component). -/
def IsClass (M : ι → ι → ℝ) (C : Finset ι) : Prop :=
  C.Nonempty ∧ ∀ i ∈ C, ∀ j, j ∈ C ↔ (Acc M i j ∧ Acc M j i)

/-- `C` is a nontrivial class: it contains an arc. -/
def IsNontrivialClass (M : ι → ι → ℝ) (C : Finset ι) : Prop :=
  IsClass M C ∧ ∃ i ∈ C, ∃ j ∈ C, 0 < M i j

/-- `ρ > 0` and `U ∈ ℝ^C_{>0}` with `M_{CC} U = ρ U`, normalised by `min U = 1`. -/
def IsPerronPair (M : ι → ι → ℝ) (C : Finset ι) (ρ : ℝ) (U : ι → ℝ) : Prop :=
  0 < ρ ∧ (∀ i ∈ C, 1 ≤ U i) ∧ (∃ i ∈ C, U i = 1) ∧ ∀ i ∈ C, ∑ j ∈ C, M i j * U j = ρ * U i

/-- A path from a point of `S` to a point outside `S` contains an arc leaving `S`. -/
theorem exists_crossing {r : ι → ι → Prop} {S : Set ι} {i j : ι}
    (h : Relation.ReflTransGen r i j) (hi : i ∈ S) (hj : j ∉ S) :
    ∃ a b, Relation.ReflTransGen r i a ∧ r a b ∧ Relation.ReflTransGen r b j ∧ a ∈ S ∧ b ∉ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hi hj
  | head h' h ih =>
    rename_i a c
    by_cases hc : c ∈ S
    · obtain ⟨a', b', h1, h2, h3, h4, h5⟩ := ih hc
      exact ⟨a', b', Relation.ReflTransGen.head h' h1, h2, h3, h4, h5⟩
    · exact ⟨a, c, Relation.ReflTransGen.refl, h', h, hi, hc⟩

/-- A class is irreducible: every set meeting the class but not containing it has an arc, inside
the class, that leaves the set. -/
theorem IsClass.cut {M : ι → ι → ℝ} {C : Finset ι} (hC : IsClass M C) (S : Set ι)
    (h1 : ∃ i ∈ C, i ∈ S) (h2 : ∃ j ∈ C, j ∉ S) :
    ∃ i ∈ C, i ∈ S ∧ ∃ j ∈ C, j ∉ S ∧ 0 < M i j := by
  obtain ⟨i, hiC, hiS⟩ := h1
  obtain ⟨j, hjC, hjS⟩ := h2
  have hij := (hC.2 i hiC j).mp hjC
  obtain ⟨a, b, hia, hab, hbj, haS, hbS⟩ := exists_crossing hij.1 hiS hjS
  have haC : a ∈ C := (hC.2 i hiC a).mpr
    ⟨hia, (Relation.ReflTransGen.head (r := fun i j => 0 < M i j) hab hbj).trans hij.2⟩
  have hbC : b ∈ C := (hC.2 i hiC b).mpr
    ⟨hia.tail hab, hbj.trans hij.2⟩
  exact ⟨a, haC, haS, b, hbC, hbS, hab⟩

/-- In a nontrivial class every state has an arc into the class. -/
theorem IsNontrivialClass.row {M : ι → ι → ℝ} {C : Finset ι} (hC : IsNontrivialClass M C)
    {i : ι} (hi : i ∈ C) : ∃ j ∈ C, 0 < M i j := by
  obtain ⟨hcl, i0, hi0, j0, hj0, h0⟩ := hC
  by_cases h : i = i0
  · subst h; exact ⟨j0, hj0, h0⟩
  · obtain ⟨a, haC, haS, b, hbC, _, hab⟩ := hcl.cut {i} ⟨i, hi, rfl⟩ ⟨i0, hi0, fun h' => h h'.symm⟩
    rw [Set.mem_singleton_iff] at haS
    subst haS
    exact ⟨b, hbC, hab⟩

/-- **Perron–Frobenius for a nontrivial class** (paragraph "Classes" of Section 6): there are
`ρ_C > 0` and `U ∈ ℝ^C_{>0}` with `M_{CC} U = ρ_C U`, normalised by `min U = 1`. -/
theorem perron_frobenius {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j) {C : Finset ι}
    (hC : IsNontrivialClass M C) : ∃ ρ U, IsPerronPair M C ρ U := by
  classical
  obtain ⟨i0, hi0⟩ := hC.1.1
  haveI : Nonempty {j // j ∈ C} := ⟨⟨i0, hi0⟩⟩
  let A : {j // j ∈ C} → {j // j ∈ C} → ℝ := fun i j => M i.1 j.1
  have hrow : ∀ i : {j // j ∈ C}, ∃ j, 0 < A i j := by
    intro i
    obtain ⟨j, hj, hij⟩ := hC.row i.2
    exact ⟨⟨j, hj⟩, hij⟩
  have hcut : ∀ S : Finset {j // j ∈ C}, S.Nonempty → S ≠ Finset.univ →
      ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < A i j := by
    intro S hS hSu
    obtain ⟨s, hs⟩ := hS
    obtain ⟨t, ht⟩ : ∃ t, t ∉ S := by
      by_contra hcon
      push Not at hcon
      exact hSu (Finset.eq_univ_of_forall hcon)
    obtain ⟨a, haC, haS, b, hbC, hbS, hab⟩ :=
      hC.1.cut {x | ∃ h : x ∈ C, (⟨x, h⟩ : {j // j ∈ C}) ∈ S} ⟨s.1, s.2, s.2, hs⟩
        ⟨t.1, t.2, fun ⟨_, h'⟩ => ht h'⟩
    obtain ⟨_, haS'⟩ := haS
    exact ⟨⟨a, haC⟩, haS', ⟨b, hbC⟩, fun h' => hbS ⟨hbC, h'⟩, hab⟩
  obtain ⟨ρ, U', hρ, hU', hMU'⟩ := perron_frobenius_cut (A := A) (fun i j => hM _ _) hrow hcut
  obtain ⟨k0, hk0⟩ := Finite.exists_min U'
  refine ⟨ρ, fun j => if h : j ∈ C then U' ⟨j, h⟩ / U' k0 else 1, hρ, ?_, ?_, ?_⟩
  · intro i hi
    simp only [hi, dif_pos]
    rw [le_div_iff₀ (hU' k0), one_mul]
    exact hk0 ⟨i, hi⟩
  · exact ⟨k0.1, k0.2, by simp [div_self (hU' k0).ne']⟩
  · intro i hi
    simp only [hi, dif_pos]
    rw [← Finset.sum_coe_sort C, ← mul_div_assoc, ← hMU' ⟨i, hi⟩, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [j.2, dif_pos, A]
    ring

end EntropyGames
