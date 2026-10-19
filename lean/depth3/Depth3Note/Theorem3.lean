/-
Theorem 3(i) of the note: Hypothesis A implies the inequality
`s·p(n) + n·s + (n+2)·B + n³ + 1 ≥ n^{√n/400}` for every `ΣΠΣ` circuit computing `IMM_{n,n}`.
-/
import Depth3Note.Lemma1

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset

noncomputable section

/-! ### `IMM_{n,n}` is homogeneous of degree `n` -/

theorem list_prod_entry_isHomogeneous {K : Type*} [CommSemiring K] {σ : Type*} {n : ℕ}
    (L : List (Matrix (Fin n) (Fin n) (MvPolynomial σ K)))
    (hL : ∀ A ∈ L, ∀ i j, (A i j).IsHomogeneous 1) :
    ∀ i j, (L.prod i j).IsHomogeneous L.length := by
  induction L with
  | nil =>
    intro i j
    rw [List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact isHomogeneous_one σ K
    · exact isHomogeneous_zero σ K 0
  | cons A L ih =>
    intro i j
    rw [List.prod_cons, Matrix.mul_apply, List.length_cons, add_comm]
    refine IsHomogeneous.sum _ _ _ fun k _ => ?_
    exact (hL A (List.mem_cons_self) i k).mul
      (ih (fun A' hA' => hL A' (List.mem_cons_of_mem _ hA')) k j)

theorem imm_isHomogeneous (K : Type u) [CommSemiring K] (n : ℕ) : (imm K n).IsHomogeneous n := by
  unfold imm
  split_ifs with h
  · have := list_prod_entry_isHomogeneous
      (List.ofFn (fun t : Fin n => immLayer K n t)) (by
        intro A hA i j
        rw [List.mem_ofFn] at hA
        obtain ⟨t, rfl⟩ := hA
        exact isHomogeneous_X K _) ⟨0, h⟩ ⟨0, h⟩
    simpa using this
  · exact isHomogeneous_zero _ K n

/-! ### Setting the variables outside the image of `ι` to zero -/

namespace SPS

variable {K : Type u} [CommSemiring K] {σ τ : Type} [Fintype σ] [Fintype τ]

/-- substitute `0` for the variables outside the image of `ι`; `s` and `B` are unchanged -/
def restrict (S : SPS K τ) (ι : σ ↪ τ) : SPS K σ where
  s := S.s
  B := S.B
  c := S.c
  a := S.a
  l := fun j v => S.l j (ι v)
  m := S.m

theorem restrict_value (S : SPS K τ) (ι : σ ↪ τ) :
    (S.restrict ι).value = aeval (Function.extend ι X 0) S.value := by
  classical
  have hlin : ∀ j : Fin S.B, ∑ v, C (S.l j (ι v)) * (X v : MvPolynomial σ K) =
      ∑ t, C (S.l j t) * Function.extend ι (X : σ → MvPolynomial σ K) 0 t := by
    intro j
    rw [← Finset.sum_subset (Finset.subset_univ (univ.map ι)), Finset.sum_map]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [ι.injective.extend_apply]
    · intro t _ ht
      rw [Function.extend_apply', Pi.zero_apply, mul_zero]
      rintro ⟨v, rfl⟩
      exact ht (Finset.mem_map_of_mem _ (Finset.mem_univ v))
  simp only [value, form, lin, restrict, map_sum, map_mul, map_prod, map_pow, map_add, aeval_C,
    aeval_X, algebraMap_eq, hlin]
  rfl

theorem restrict_value_of_rename (S : SPS K τ) (ι : σ ↪ τ) (q : MvPolynomial σ K)
    (h : S.value = rename ι q) : (S.restrict ι).value = q := by
  rw [restrict_value, h, aeval_rename]
  have : (Function.extend ι (X : σ → MvPolynomial σ K) 0) ∘ ι = X := by
    funext v
    exact ι.injective.extend_apply _ _ v
  rw [this, aeval_X_left, AlgHom.id_apply]

end SPS

/-! ### Theorem 3(i) -/

/-- **Theorem 3(i)** of the note. Hypothesis A is the explicit hypothesis `HypothesisA n₀`. -/
theorem theorem3i : Theorem3iStatement.{u} := by
  intro n₀ hA K _ _ n hn τ _ ι S hS
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
    positivity
  have hS' : (S.restrict ι).value = imm K n := S.restrict_value_of_rename ι _ hS
  obtain ⟨c, hc, hsize⟩ := lemma1 K n (S.restrict ι) n hpos
  rw [hS', homogeneousComponent_eq_self (imm_isHomogeneous K n)] at hc
  have h1 := hA K n hn c hc
  have h2 : circuitSize c ≤ S.s * p n + n * S.s + (n + 2) * S.B + n ^ 3 + 1 := by
    have e : n ^ 3 + 2 * S.B + n * S.B + n * S.s + S.s * p n + 1 =
        S.s * p n + n * S.s + (n + 2) * S.B + n ^ 3 + 1 := by ring
    exact e ▸ hsize
  exact h1.trans (by exact_mod_cast h2)

end

end Depth3Note
