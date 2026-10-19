/-
Formal statements for the note
"A remark on depth-three circuits and a homogeneous depth-five lower bound for iterated matrix
multiplication".

This file contains DEFINITIONS ONLY (each statement of the paper is a `def ... : Prop`), so it is
`sorry`-free by construction. Proofs are in the other files of `Depth3Note`. Two of the statements
defined here, `Lemma4Statement` and `Corollary5Statement`, include the permanent and are NOT proved
anywhere in this library; only their determinant halves, `Lemma4DetStatement` and
`Corollary5DetStatement`, are.

What is and is not formalised: see README.md and the appendix "Formalisation" of the paper.
-/
import Depth3Note.ReleaseDefs

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial

noncomputable section

/-! ### Hypothesis A (Corollary 6.1 of the cited manuscript) -/

/-- **Hypothesis A with threshold `n₀`.** This is, word for word, the body of the second conjunct of
the release's theorem `OAI.Problem335.main` (equivalently of
`OAI.Problem335.characteristic_zero_depth_five_lower_bound`) after the quantifier
`∃ threshold : ℕ`: for every field `K` of characteristic zero (in universe `u`) and every
`n ≥ n₀`, every `Depth5Circuit K n` whose value is `imm K n` has `circuitSize ≥ n ^ (√n / 400)`.

The paper's Hypothesis A is `∃ n₀, HypothesisA n₀`; the paper's theorems are stated "with its
threshold `n₀`", which is why the threshold is a parameter here. It is a `Prop`-valued definition;
it is never asserted as an axiom. -/
def HypothesisA (n₀ : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K], ∀ n : ℕ, n₀ ≤ n →
    ∀ c : Depth5Circuit K n, circuitValue c = imm K n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ)

/-! ### Depth-three circuits, equation (1) of the paper -/

/-- A `ΣΠΣ` expression `f = ∑_{i<s} c_i ∏_{j<B} L_j ^ (m i j)` in the variables `σ`, with
`L_j = a_j + ∑_v l_j(v) x_v` affine. This is equation (1) of the paper with `J_i = {j | m i j ≠ 0}`.
The forms `L_j` are NOT required to be distinct (the paper takes them distinct; dropping the
requirement only enlarges the class of circuits, so lower bounds on `s + B` become stronger). -/
structure SPS (K : Type u) (σ : Type) where
  /-- number of product gates -/
  s : ℕ
  /-- number of bottom affine forms -/
  B : ℕ
  /-- coefficients of the top sum -/
  c : Fin s → K
  /-- constant terms of the affine forms -/
  a : Fin B → K
  /-- linear coefficients of the affine forms -/
  l : Fin B → σ → K
  /-- multiplicities (`0` means that `L_j` does not feed product gate `i`) -/
  m : Fin s → Fin B → ℕ

namespace SPS

variable {K : Type u} [CommSemiring K] {σ : Type} [Fintype σ]

/-- the homogeneous linear part `ℓ_j` of the `j`th form -/
def lin (C : SPS K σ) (j : Fin C.B) : MvPolynomial σ K := ∑ v, MvPolynomial.C (C.l j v) * X v

/-- the affine form `L_j = a_j + ℓ_j` -/
def form (C : SPS K σ) (j : Fin C.B) : MvPolynomial σ K := MvPolynomial.C (C.a j) + C.lin j

/-- the polynomial computed, equation (1) -/
def value (C : SPS K σ) : MvPolynomial σ K :=
  ∑ i, MvPolynomial.C (C.c i) * ∏ j, C.form j ^ C.m i j

end SPS

/-- The number of partitions of `n`. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- Variables of `IMM_{N,N}` in the release: `(layer, row, column)`. -/
abbrev ImmVar (N : ℕ) : Type := Fin N × Fin N × Fin N

/-! ### Lemma 1 -/

/-- **Lemma 1** (with `V = N³`: the release's circuit structure only exists over the variable set
`Fin N × Fin N × Fin N`; the degree `n` is independent of `N`). -/
def Lemma1Statement : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (N : ℕ) (C : SPS K (ImmVar N)) (n : ℕ), 1 ≤ n →
    ∃ c : Depth5Circuit K N,
      circuitValue c = homogeneousComponent n C.value ∧
      circuitSize c ≤ N ^ 3 + 2 * C.B + n * C.B + n * C.s + C.s * p n + 1

/-! ### Lemma 2 -/

/-- **Lemma 2.** `p(n) ≤ exp(π √(2n/3)) < e^{3√n}` for `n ≥ 1`. -/
def Lemma2Statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (p n : ℝ) ≤ Real.exp (Real.pi * Real.sqrt (2 * n / 3)) ∧
    Real.exp (Real.pi * Real.sqrt (2 * n / 3)) < Real.exp (3 * Real.sqrt n)

/-- The only consequence of Lemma 2 that Theorem 3(ii) uses. -/
def Lemma2WeakStatement : Prop := ∀ n : ℕ, (p n : ℝ) ≤ Real.exp (3 * Real.sqrt n)

/-! ### Theorem 3 -/

/-- **Theorem 3(i).** The `ΣΠΣ` circuit may use any finite set `τ` of variables containing the
`n³` variables of `IMM_{n,n}` (via the injection `ι`), as in the paper's proof ("substitute zero for
the variables of the circuit outside the `n³` matrix entries"). -/
def Theorem3iStatement : Prop :=
  ∀ n₀ : ℕ, HypothesisA.{u} n₀ →
    ∀ (K : Type u) [Field K] [CharZero K] (n : ℕ), n₀ ≤ n →
      ∀ (τ : Type) [Fintype τ] (ι : ImmVar n ↪ τ) (C : SPS K τ),
        C.value = rename ι (imm K n) →
          (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤
            (C.s * p n + n * C.s + (n + 2) * C.B + n ^ 3 + 1 : ℕ)

/-- **Theorem 3(ii)**, first form. "There is `n₁ ≥ 2`, depending only on `n₀`": the
quantifiers are `∀ n₀, ∃ n₁`, before the field and the circuit. -/
def Theorem3iiStatement : Prop :=
  ∀ n₀ : ℕ, ∃ n₁ : ℕ, 2 ≤ n₁ ∧ (HypothesisA.{u} n₀ →
    ∀ (K : Type u) [Field K] [CharZero K] (n : ℕ), n₁ ≤ n →
      ∀ (τ : Type) [Fintype τ] (ι : ImmVar n ↪ τ) (C : SPS K τ),
        C.value = rename ι (imm K n) →
          (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) * Real.exp (-4 * Real.sqrt n) ≤ (C.s + C.B : ℕ))

/-- The equality `n^{√n/400} e^{-4√n} = n^{√n/400 - 4√n/ln n}` printed in Theorem 3(ii); it needs
`n ≥ 2` (for `n = 1` the right-hand side divides by `ln 1 = 0`). -/
def Theorem3iiRewriteStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) * Real.exp (-4 * Real.sqrt n) =
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400 - 4 * Real.sqrt n / Real.log n)

/-! ### Lemma 4 -/

/-- **Lemma 4.** No hypothesis on the coefficient ring is used in the paper; we state it over every
commutative ring. -/
def Lemma4Statement : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ), 2 ≤ n →
    ∃ A : Matrix (Fin (n ^ 2 - n + 1)) (Fin (n ^ 2 - n + 1)) (MvPolynomial (ImmVar n) K),
      (∀ i j, A i j = 0 ∨ A i j = 1 ∨ ∃ v, A i j = X v) ∧
      A.permanent = imm K n ∧
      A.det = (-1) ^ (n - 1) * imm K n

/-- **Lemma 4, determinant half** (the part that is formalised; the permanent half of
`Lemma4Statement` is not). -/
def Lemma4DetStatement : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ), 2 ≤ n →
    ∃ A : Matrix (Fin (n ^ 2 - n + 1)) (Fin (n ^ 2 - n + 1)) (MvPolynomial (ImmVar n) K),
      (∀ i j, A i j = 0 ∨ A i j = 1 ∨ ∃ v, A i j = X v) ∧
      A.det = (-1) ^ (n - 1) * imm K n

/-! ### Corollary 5 -/

/-- the generic `M × M` matrix -/
def genericMatrix (K : Type u) [CommSemiring K] (M : ℕ) :
    Matrix (Fin M) (Fin M) (MvPolynomial (Fin M × Fin M) K) := fun i j => X (i, j)

/-- **Corollary 5.** "There are an absolute constant `c > 0` and `M₀`, depending only on `n₀`":
the quantifiers are `∃ c > 0, ∀ n₀, ∃ M₀`. -/
def Corollary5Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ M₀ : ℕ, HypothesisA.{u} n₀ →
    ∀ (K : Type u) [Field K] [CharZero K] (M : ℕ), M₀ ≤ M →
      ∀ (τ : Type) [Fintype τ] (ι : Fin M × Fin M ↪ τ) (C : SPS K τ),
        (C.value = rename ι (genericMatrix K M).det ∨
          C.value = rename ι (genericMatrix K M).permanent) →
          (M : ℝ) ^ (c * (M : ℝ) ^ (1 / 4 : ℝ)) ≤ (C.s + C.B : ℕ)

/-- **Corollary 5, determinant half** (the part that is formalised). -/
def Corollary5DetStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ M₀ : ℕ, HypothesisA.{u} n₀ →
    ∀ (K : Type u) [Field K] [CharZero K] (M : ℕ), M₀ ≤ M →
      ∀ (τ : Type) [Fintype τ] (ι : Fin M × Fin M ↪ τ) (C : SPS K τ),
        C.value = rename ι (genericMatrix K M).det →
          (M : ℝ) ^ (c * (M : ℝ) ^ (1 / 4 : ℝ)) ≤ (C.s + C.B : ℕ)

end

end Depth3Note
