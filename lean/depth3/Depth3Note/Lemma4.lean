/-
Lemma 4 of the note, DETERMINANT HALF: for `n ≥ 2` there is a matrix of size `n² - n + 1` with
entries in `{0, 1} ∪ {variables}` whose determinant is `(-1)^{n-1} IMM_{n,n}`. (The permanent half
is not formalised.)

The matrix is the paper's: vertex `v₀` (index `Sum.inl ()`), and for each of the `n - 1` inner
layers `n` vertices (index `Sum.inr (l, i)`), with a loop of weight `1` at each inner vertex:
`A = [[0, u], [w, 1 + T]]`. The proof is NOT the paper's cycle-cover argument. It is linear
algebra: with `v(l, i) = (-1)^{n-2-l} (X^{(l+2)} ⋯ X^{(n)})_{i,1}` one has `(1 + T) v = w`, hence
`A · [[1, 0], [-v, 1]] = [[-u v, u], [0, 1 + T]]`, and `det (1 + T) = 1`, `u v = (-1)^{n-2} IMM`.
-/
import Depth3Note.Lemma2

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset Matrix

noncomputable section

variable (K : Type u) [CommRing K] (n : ℕ)

/-- inner vertices: (layer, position) -/
abbrev Mid (n : ℕ) : Type := Fin (n - 1) × Fin n

/-- the product of the layers `k, k+1, …, n-1` (0-indexed) -/
def suf (k : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (ImmVar n) K) :=
  ((List.ofFn (fun t : Fin n => immLayer K n t)).drop k).prod

theorem suf_n : suf K n n = 1 := by
  unfold suf
  rw [List.drop_eq_nil_of_le (by simp), List.prod_nil]

theorem suf_step (k : ℕ) (hk : k < n) :
    suf K n k = immLayer K n ⟨k, hk⟩ * suf K n (k + 1) := by
  unfold suf
  rw [List.drop_eq_getElem_cons (by simpa using hk), List.prod_cons, List.getElem_ofFn]

theorem imm_eq_suf (hn : 0 < n) : imm K n = suf K n 0 ⟨0, hn⟩ ⟨0, hn⟩ := by
  unfold imm suf
  rw [dif_pos hn]
  simp

/-- edges between consecutive inner layers -/
def Tmat : Matrix (Mid n) (Mid n) (MvPolynomial (ImmVar n) K) := fun a b =>
  if b.1.val = a.1.val + 1 then X (⟨a.1.val + 1, by have := a.1.isLt; omega⟩, a.2, b.2) else 0

/-- edges from `v₀` to the first inner layer -/
def umat (hn : 0 < n) : Matrix Unit (Mid n) (MvPolynomial (ImmVar n) K) := fun _ b =>
  if b.1.val = 0 then X (⟨0, hn⟩, ⟨0, hn⟩, b.2) else 0

/-- edges from the last inner layer to `v₀` -/
def wmat (hn : 0 < n) : Matrix (Mid n) Unit (MvPolynomial (ImmVar n) K) := fun a _ =>
  if a.1.val + 2 = n then X (⟨a.1.val + 1, by have := a.1.isLt; omega⟩, a.2, ⟨0, hn⟩) else 0

/-- the solution of `(1 + T) v = w` -/
def vmat (hn : 0 < n) : Matrix (Mid n) Unit (MvPolynomial (ImmVar n) K) := fun a _ =>
  (-1) ^ (n - 2 - a.1.val) * suf K n (a.1.val + 1) a.2 ⟨0, hn⟩

/-- the matrix of Lemma 4 -/
def Amat (hn : 0 < n) :
    Matrix (Unit ⊕ Mid n) (Unit ⊕ Mid n) (MvPolynomial (ImmVar n) K) :=
  fromBlocks 0 (umat K n hn) (wmat K n hn) (1 + Tmat K n)

theorem det_one_add_Tmat : (1 + Tmat K n : Matrix (Mid n) (Mid n) _).det = 1 := by
  have hT : (1 + Tmat K n : Matrix (Mid n) (Mid n) _).BlockTriangular Prod.fst := by
    intro a b hlt
    have h1 : a ≠ b := fun h => by
      rw [h] at hlt
      exact lt_irrefl _ hlt
    have h2 : ¬ b.1.val = a.1.val + 1 := by
      have := Fin.lt_def.1 hlt
      omega
    simp [Matrix.add_apply, Tmat, h1, h2]
  rw [hT.det_fintype]
  apply Finset.prod_eq_one
  intro k _
  have h1 : (1 + Tmat K n : Matrix (Mid n) (Mid n) _).toSquareBlock Prod.fst k = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    have h2 : ¬ b.1.val = a.1.val + 1 := by
      rw [ha, hb]
      omega
    simp [Matrix.toSquareBlock_def, Matrix.one_apply, Tmat, h2, Subtype.ext_iff]
  rw [h1, det_one]

theorem one_add_Tmat_mul_vmat (hn : 0 < n) :
    (1 + Tmat K n) * vmat K n hn = wmat K n hn := by
  ext a ⟨⟩
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  have ha := a.1.isLt
  by_cases h : a.1.val + 2 = n
  · have hz : ∑ l : Fin (n - 1), ∑ j : Fin n, Tmat K n a (l, j) * vmat K n hn (l, j) () = 0 := by
      refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => ?_
      have hl := l.isLt
      simp only [Tmat]
      rw [if_neg (by omega), zero_mul]
    rw [hz, add_zero]
    simp only [vmat, wmat]
    rw [if_pos h, suf_step K n (a.1.val + 1) (by omega)]
    have e : a.1.val + 1 + 1 = n := by omega
    have e0 : n - 2 - a.1.val = 0 := by omega
    rw [e, suf_n, mul_one, e0, pow_zero, one_mul]
    rfl
  · have hlt : a.1.val + 1 < n - 1 := by omega
    have hsum : ∑ l : Fin (n - 1), ∑ j : Fin n, Tmat K n a (l, j) * vmat K n hn (l, j) () =
        ∑ j : Fin n, Tmat K n a (⟨a.1.val + 1, hlt⟩, j) * vmat K n hn (⟨a.1.val + 1, hlt⟩, j) () := by
      refine Finset.sum_eq_single (⟨a.1.val + 1, hlt⟩ : Fin (n - 1)) ?_ ?_
      · intro l _ hl
        refine Finset.sum_eq_zero fun j _ => ?_
        have : ¬ l.val = a.1.val + 1 := fun h' => hl (Fin.ext h')
        simp only [Tmat]
        rw [if_neg this, zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    rw [hsum]
    have hS : suf K n (a.1.val + 1) a.2 ⟨0, hn⟩ =
        ∑ j : Fin n, X (⟨a.1.val + 1, by omega⟩, a.2, j) * suf K n (a.1.val + 2) j ⟨0, hn⟩ := by
      rw [suf_step K n (a.1.val + 1) (by omega), Matrix.mul_apply]
      rfl
    have e1 : n - 2 - a.1.val = (n - 3 - a.1.val) + 1 := by omega
    have e2 : n - 2 - (a.1.val + 1) = n - 3 - a.1.val := by omega
    have hTv : ∑ j : Fin n, Tmat K n a (⟨a.1.val + 1, hlt⟩, j) * vmat K n hn (⟨a.1.val + 1, hlt⟩, j) () =
        (-1) ^ (n - 3 - a.1.val) *
          ∑ j : Fin n, X (⟨a.1.val + 1, by omega⟩, a.2, j) * suf K n (a.1.val + 2) j ⟨0, hn⟩ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [vmat, Tmat, if_true, e2]
      ring
    rw [hTv]
    simp only [vmat, wmat]
    rw [if_neg h, hS, e1, pow_succ]
    ring_nf

theorem umat_mul_vmat (hn : 2 ≤ n) :
    (umat K n (by omega : 0 < n) * vmat K n (by omega : 0 < n)) () () = (-1) ^ (n - 2) * imm K n := by
  have hn0 : 0 < n := by omega
  have h0 : 0 < n - 1 := by omega
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (⟨0, h0⟩ : Fin (n - 1))]
  · rw [imm_eq_suf K n hn0, suf_step K n 0 hn0, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [umat, vmat, if_true, Nat.sub_zero, zero_add, immLayer]
    ring
  · intro l _ hl
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ l.val = 0 := fun h' => hl (Fin.ext h')
    simp only [umat]
    rw [if_neg this, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem det_Amat (hn : 2 ≤ n) :
    (Amat K n (by omega : 0 < n)).det = (-1) ^ (n - 1) * imm K n := by
  have hn0 : 0 < n := by omega
  have hmul : Amat K n hn0 * fromBlocks 1 0 (-vmat K n hn0) 1 =
      fromBlocks (-(umat K n hn0 * vmat K n hn0)) (umat K n hn0) 0 (1 + Tmat K n) := by
    rw [Amat, fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [Matrix.mul_one, Matrix.mul_neg, one_add_Tmat_mul_vmat]
      simp
    · simp
  have hdet := congrArg Matrix.det hmul
  simp only [det_mul, det_fromBlocks_zero₁₂, det_one, mul_one, det_fromBlocks_zero₂₁,
    det_one_add_Tmat] at hdet
  rw [det_unique (-(umat K n hn0 * vmat K n hn0)), Matrix.neg_apply] at hdet
  refine hdet.trans ?_
  have huv : (umat K n hn0 * vmat K n hn0) default default = (-1) ^ (n - 2) * imm K n :=
    umat_mul_vmat K n hn
  rw [huv]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show m + 2 - 1 = m + 1 by omega, pow_succ]
  ring

theorem Amat_entries (hn : 0 < n) (i j : Unit ⊕ Mid n) :
    Amat K n hn i j = 0 ∨ Amat K n hn i j = 1 ∨ ∃ v, Amat K n hn i j = X v := by
  rcases i with ⟨⟩ | a <;> rcases j with ⟨⟩ | b
  · left; rfl
  · simp only [Amat, fromBlocks_apply₁₂, umat]
    split_ifs
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inl rfl
  · simp only [Amat, fromBlocks_apply₂₁, wmat]
    split_ifs
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inl rfl
  · simp only [Amat, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Tmat]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_neg (by omega), add_zero]
      exact Or.inr (Or.inl rfl)
    · rw [if_neg hab, zero_add]
      split_ifs
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
      · exact Or.inl rfl

theorem card_Amat_index (hn : 2 ≤ n) : Fintype.card (Unit ⊕ Mid n) = n ^ 2 - n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin]
  have : (m + 2) ^ 2 = (m + 2 - 1) * (m + 2) + (m + 2) := by
    rw [show m + 2 - 1 = m + 1 by omega]; ring
  omega

/-- The matrix padded by an identity block to any size `M ≥ n² - n + 1` (the matrix `A'` in the
proof of Corollary 5). -/
theorem exists_matrix_det (hn : 2 ≤ n) (M : ℕ) (hM : n ^ 2 - n + 1 ≤ M) :
    ∃ A : Matrix (Fin M) (Fin M) (MvPolynomial (ImmVar n) K),
      (∀ i j, A i j = 0 ∨ A i j = 1 ∨ ∃ v, A i j = X v) ∧
      A.det = (-1) ^ (n - 1) * imm K n := by
  have hn0 : 0 < n := by omega
  have hcard : Fintype.card ((Unit ⊕ Mid n) ⊕ Fin (M - (n ^ 2 - n + 1))) = Fintype.card (Fin M) := by
    rw [Fintype.card_sum, card_Amat_index n hn, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin M ≃ (Unit ⊕ Mid n) ⊕ Fin (M - (n ^ 2 - n + 1)) :=
    (Fintype.equivOfCardEq hcard).symm
  refine ⟨(fromBlocks (Amat K n hn0) 0 0 1).submatrix e e, ?_, ?_⟩
  · intro i j
    rw [Matrix.submatrix_apply]
    rcases e i with a | a <;> rcases e j with b | b
    · exact Amat_entries K n hn0 a b
    · exact Or.inl rfl
    · exact Or.inl rfl
    · rw [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one, det_Amat K n hn]

/-- **Lemma 4, determinant half.** -/
theorem lemma4_det : Lemma4DetStatement.{u} := by
  intro K _ n hn
  exact exists_matrix_det K n hn _ le_rfl

end

end Depth3Note
