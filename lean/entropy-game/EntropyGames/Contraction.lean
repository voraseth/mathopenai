/-
Section 4 of the paper, first part: Lemma 4.1 (contraction, unique fixed point, comparison
with sub- and supersolutions), the remark after it (one-sided translation inequality), and
Lemma 4.2 (integer comparison vectors).
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace EntropyGames

variable {ι : Type*} [Fintype ι]

/-- Equation (4.1) of the paper (the same as Equation (3.1) of the release, without the
side condition on `γ`): `G` is monotone and `G (t + c𝟙) = G t + γ c 𝟙`. -/
structure IsDiscounted (γ : ℝ) (G : (ι → ℝ) → ι → ℝ) : Prop where
  mono : Monotone G
  shift : ∀ (t : ι → ℝ) (c : ℝ), G (fun i => t i + c) = fun i => G t i + γ * c

/-- The weaker hypothesis of the remark after Lemma 4.1: monotone, and
`Ψ (t + c𝟙) ≤ Ψ t + γ c 𝟙` for `c ≥ 0`. -/
structure IsSubDiscounted (γ : ℝ) (Ψ : (ι → ℝ) → ι → ℝ) : Prop where
  mono : Monotone Ψ
  subshift : ∀ (t : ι → ℝ) (c : ℝ), 0 ≤ c → ∀ i, Ψ (fun j => t j + c) i ≤ Ψ t i + γ * c

theorem IsDiscounted.isSubDiscounted {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G) :
    IsSubDiscounted γ G :=
  ⟨h.mono, fun t c _ i => by rw [h.shift]⟩

/-- Remark after Lemma 4.1, subsolutions: if `w ≤ Ψ w` then `w` is below any fixed point. -/
theorem IsSubDiscounted.le_fixed {γ : ℝ} {Ψ : (ι → ℝ) → ι → ℝ} (h : IsSubDiscounted γ Ψ)
    (hγ : γ < 1) {x w : ι → ℝ} (hx : Ψ x = x) (hw : w ≤ Ψ w) : w ≤ x := by
  intro i
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => w j - x j)
  by_contra hcon
  have hc : 0 < w i0 - x i0 := by
    have : w i - x i ≤ w i0 - x i0 := hi0 i
    linarith [not_le.mp hcon]
  set c := w i0 - x i0 with hcdef
  have h1 : w ≤ fun j => x j + c := fun j => by
    have : w j - x j ≤ w i0 - x i0 := hi0 j
    linarith
  have h2 := h.mono h1 i0
  have h3 := h.subshift x c hc.le i0
  have h4 := hw i0
  rw [hx] at h3
  nlinarith

/-- Remark after Lemma 4.1, supersolutions: if `Ψ w ≤ w` then `w` is above any fixed point. -/
theorem IsSubDiscounted.fixed_le {γ : ℝ} {Ψ : (ι → ℝ) → ι → ℝ} (h : IsSubDiscounted γ Ψ)
    (hγ : γ < 1) {x w : ι → ℝ} (hx : Ψ x = x) (hw : Ψ w ≤ w) : x ≤ w := by
  intro i
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => x j - w j)
  by_contra hcon
  have hc : 0 < x i0 - w i0 := by
    have : x i - w i ≤ x i0 - w i0 := hi0 i
    linarith [not_le.mp hcon]
  set c := x i0 - w i0 with hcdef
  have h1 : x ≤ fun j => w j + c := fun j => by
    have : x j - w j ≤ x i0 - w i0 := hi0 j
    linarith
  have h2 := h.mono h1 i0
  have h3 := h.subshift w c hc.le i0
  have h4 := hw i0
  rw [hx] at h2
  nlinarith

/-- Lemma 4.1, first claim: a map satisfying (4.1) with `0 ≤ γ` is `γ`-Lipschitz for the sup
norm (the distance on `ι → ℝ` is the sup distance). -/
theorem IsDiscounted.dist_le {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G) (hγ0 : 0 ≤ γ)
    (t t' : ι → ℝ) : dist (G t) (G t') ≤ γ * dist t t' := by
  have key : ∀ s s' : ι → ℝ, ∀ i, G s i - G s' i ≤ γ * dist s s' := by
    intro s s' i
    have h1 : s ≤ fun j => s' j + dist s s' := fun j => by
      have := dist_le_pi_dist s s' j
      rw [Real.dist_eq] at this
      linarith [le_abs_self (s j - s' j)]
    have h2 := h.mono h1 i
    rw [h.shift] at h2
    linarith
  rw [dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)]
  intro i
  rw [Real.dist_eq, abs_le]
  have a := key t t' i
  have b := key t' t i
  rw [dist_comm t' t] at b
  constructor <;> linarith

/-- Lemma 4.1: existence and uniqueness of the fixed point. -/
theorem IsDiscounted.existsUnique_fixed {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) : ∃! x, G x = x := by
  have hc : ContractingWith ⟨γ, hγ0⟩ G :=
    ⟨by exact_mod_cast hγ, LipschitzWith.of_dist_le_mul fun t t' => h.dist_le hγ0 t t'⟩
  refine ⟨ContractingWith.fixedPoint G hc, hc.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact le_antisymm (h.isSubDiscounted.le_fixed hγ hc.fixedPoint_isFixedPt hy.ge)
    (h.isSubDiscounted.fixed_le hγ hc.fixedPoint_isFixedPt hy.le)

/-- The fixed point of a map satisfying (4.1), `0 ≤ γ < 1`. -/
noncomputable def fixedPt {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) : ι → ℝ :=
  (h.existsUnique_fixed hγ0 hγ).choose

theorem fixedPt_spec {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) : G (fixedPt h hγ0 hγ) = fixedPt h hγ0 hγ :=
  (h.existsUnique_fixed hγ0 hγ).choose_spec.1

theorem fixedPt_unique {γ : ℝ} {G : (ι → ℝ) → ι → ℝ} (h : IsDiscounted γ G)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) {y : ι → ℝ} (hy : G y = y) : y = fixedPt h hγ0 hγ :=
  (h.existsUnique_fixed hγ0 hγ).choose_spec.2 y hy

/-- Lemma 4.2 (comparison vectors).  `Y = ⌊x⌋ - N 𝟙`, `Z = ⌈x⌉ + N 𝟙`. -/
theorem comparison_vectors {N : ℕ} (hN : 2 ≤ N) {G : (ι → ℝ) → ι → ℝ}
    (h : IsDiscounted (1 - 1 / (N : ℝ)) G) {x : ι → ℝ} (hx : G x = x) :
    let Y : ι → ℤ := fun i => ⌊x i⌋ - N
    let Z : ι → ℤ := fun i => ⌈x i⌉ + N
    (∀ i, (Y i : ℝ) ≤ G (fun j => (Y j : ℝ)) i) ∧ (∀ i, G (fun j => (Z j : ℝ)) i ≤ Z i) ∧
      (∀ i, (Y i : ℝ) ≤ x i) ∧ (∀ i, x i ≤ Z i) ∧ ∀ i, Z i - Y i ≤ 2 * (N + 1) := by
  intro Y Z
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hid : (1 - 1 / (N : ℝ)) * (N + 1) = N - 1 / N := by field_simp; ring
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h1 : (fun j => x j + (-(N + 1 : ℝ))) ≤ fun j => (Y j : ℝ) := fun j => by
      have := Int.lt_floor_add_one (x j)
      simp only [Y, Int.cast_sub, Int.cast_natCast]; linarith
    have h2 := h.mono h1 i
    rw [h.shift, hx] at h2
    have h3 := Int.floor_le (x i)
    simp only [Y, Int.cast_sub, Int.cast_natCast] at h2 ⊢
    nlinarith
  · intro i
    have h1 : (fun j => (Z j : ℝ)) ≤ fun j => x j + (N + 1 : ℝ) := fun j => by
      have := Int.ceil_lt_add_one (x j)
      simp only [Z, Int.cast_add, Int.cast_natCast]; linarith
    have h2 := h.mono h1 i
    rw [h.shift, hx] at h2
    have h3 := Int.le_ceil (x i)
    simp only [Z, Int.cast_add, Int.cast_natCast] at h2 ⊢
    nlinarith
  · intro i
    have h3 := Int.floor_le (x i)
    simp only [Y, Int.cast_sub, Int.cast_natCast]; linarith
  · intro i
    have h3 := Int.le_ceil (x i)
    simp only [Z, Int.cast_add, Int.cast_natCast]; linarith
  · intro i
    have := Int.ceil_le_floor_add_one (x i)
    simp only [Y, Z]; linarith

end EntropyGames
