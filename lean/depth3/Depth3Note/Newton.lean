/-
Algebraic core of Lemma 1: over a field of characteristic zero, elementary symmetric polynomials are
linear combinations of products of power sums indexed by partitions (Girard-Newton), and the
homogeneous components of `H * ∏_j (1 + y_j)^{m_j}`.

The paper writes the closed form `e_k = ∑_{λ ⊢ k} (-1)^{k - len λ} / z_λ ∏_r P_r^{μ_r}`. Lemma 1 only
needs that SOME coefficients indexed by the partitions of `k` exist; we derive their existence from
Mathlib's Newton recurrence `MvPolynomial.mul_esymm_eq_sum` by induction on `k`. The closed form of
the coefficients is not formalised (it is not part of the statement of Lemma 1).
-/
import Depth3Note.Statements

namespace Depth3Note

open MvPolynomial Finset

noncomputable section

section Span

variable (K : Type*) [Field K] [CharZero K]

/-- add the part `j` to a partition of `i` -/
def consPart {i : ℕ} (μ : Nat.Partition i) (j : ℕ) (hj : 0 < j) : Nat.Partition (i + j) where
  parts := j ::ₘ μ.parts
  parts_pos := by
    intro x hx
    rcases Multiset.mem_cons.1 hx with rfl | h
    · exact hj
    · exact μ.parts_pos h
  parts_sum := by simp [μ.parts_sum, add_comm]

/-- Girard-Newton, existence form: `e_k` lies in the span of the products of power sums `p_μ`,
`μ ⊢ k`. -/
theorem esymm_mem_span_psumPart (τ : Type) [Fintype τ] (k : ℕ) :
    esymm τ K k ∈ Submodule.span K (Set.range (fun μ : Nat.Partition k => psumPart τ K μ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · apply Submodule.subset_span
      exact ⟨default, by simp [psumPart, esymm_zero]⟩
    · have hN := mul_esymm_eq_sum τ K k
      have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have h0 : esymm τ K k = C ((k : K)⁻¹) * ((k : MvPolynomial τ K) * esymm τ K k) := by
        rw [← mul_assoc, ← map_natCast (C : K →+* MvPolynomial τ K) k, ← C_mul,
          inv_mul_cancel₀ hk', C_1, one_mul]
      rw [h0, hN, ← smul_eq_C_mul]
      apply Submodule.smul_mem
      have h1 : ((-1 : MvPolynomial τ K)) ^ (k + 1) = C ((-1 : K) ^ (k + 1)) := by simp
      rw [h1, ← smul_eq_C_mul]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      rintro ⟨i, j⟩ hij
      simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at hij
      obtain ⟨rfl, hlt⟩ := hij
      dsimp only
      have hj : 0 < j := by omega
      have h2 : ((-1 : MvPolynomial τ K)) ^ i = C ((-1 : K) ^ i) := by simp
      rw [h2, mul_assoc, ← smul_eq_C_mul]
      apply Submodule.smul_mem
      have hle : Submodule.span K (Set.range (fun μ : Nat.Partition i => psumPart τ K μ)) ≤
          (Submodule.span K (Set.range (fun μ : Nat.Partition (i + j) => psumPart τ K μ))).comap
            (LinearMap.mulRight K (psum τ K j)) := by
        rw [Submodule.span_le]
        rintro _ ⟨μ, rfl⟩
        apply Submodule.subset_span
        refine ⟨consPart μ j hj, ?_⟩
        simp [psumPart, consPart, mul_comm]
      exact hle (ih i hlt)

end Span

section Weighted

variable {K : Type*} [Field K] [CharZero K] {A : Type*} [CommRing A] [Algebra K A]

/-- `e_k` of the multiset containing `y j` with multiplicity `m j`. -/
def esymmW {B : ℕ} (m : Fin B → ℕ) (y : Fin B → A) (k : ℕ) : A :=
  ∑ t ∈ powersetCard k (univ : Finset (Σ j : Fin B, Fin (m j))), ∏ x ∈ t, y x.1

/-- `∏_j (1 + y_j)^{m_j} = ∑_k e_k`. -/
theorem prod_one_add_pow_eq_sum_esymmW {B : ℕ} (m : Fin B → ℕ) (y : Fin B → A) (M : ℕ)
    (hM : ∑ j, m j ≤ M) :
    ∏ j, (1 + y j) ^ m j = ∑ k ∈ range (M + 1), esymmW m y k := by
  classical
  have h1 : ∏ j, (1 + y j) ^ m j = ∏ x : (Σ j : Fin B, Fin (m j)), (1 + y x.1) := by
    rw [Fintype.prod_sigma]
    simp
  rw [h1, Finset.prod_one_add]
  have hcard : Fintype.card (Σ j : Fin B, Fin (m j)) = ∑ j, m j := by simp
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (Σ j : Fin B, Fin (m j))).powerset)
    (t := range (M + 1)) (g := Finset.card)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [esymmW, Finset.powersetCard_eq_filter]
  · intro t _
    have : t.card ≤ Fintype.card (Σ j : Fin B, Fin (m j)) := Finset.card_le_univ t
    simp only [mem_range]
    omega

/-- Girard-Newton for `esymmW`: a linear combination, over the partitions of `k`, of products of the
weighted power sums `P_r = ∑_j m_j y_j^r`. -/
theorem exists_esymmW_eq {B : ℕ} (m : Fin B → ℕ) (y : Fin B → A) (k : ℕ) :
    ∃ c : Nat.Partition k → K,
      esymmW m y k = ∑ μ, c μ • (μ.parts.map (fun r => ∑ j, m j • y j ^ r)).prod := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (esymm_mem_span_psumPart K (Σ j : Fin B, Fin (m j)) k)
  refine ⟨c, ?_⟩
  have h := congrArg (aeval (R := K) (fun x : (Σ j : Fin B, Fin (m j)) => y x.1)) hc
  rw [aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val] at h
  rw [esymmW, ← h, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, psumPart, map_multiset_prod, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun r _ => ?_
  simp [psum, Fintype.sum_sigma]

end Weighted

section Component

variable {K : Type*} [Field K] {σ : Type*}

theorem esymmW_isHomogeneous {B : ℕ} (m : Fin B → ℕ) (y : Fin B → MvPolynomial σ K)
    (hy : ∀ j, (y j).IsHomogeneous 1) (k : ℕ) : (esymmW m y k).IsHomogeneous k := by
  apply IsHomogeneous.sum
  intro t ht
  have h := IsHomogeneous.prod t (fun x : (Σ j : Fin B, Fin (m j)) => y x.1) (fun _ => 1)
    (fun x _ => hy x.1)
  simpa [(mem_powersetCard.1 ht).2] using h

/-- The degree-`n` component of `H * ∏_j (1 + y_j)^{m_j}` for `H` homogeneous of degree `D` and
`y_j` homogeneous of degree `1`. -/
theorem homogeneousComponent_mul_prod_one_add {B : ℕ} (m : Fin B → ℕ)
    (y : Fin B → MvPolynomial σ K) (hy : ∀ j, (y j).IsHomogeneous 1)
    (H : MvPolynomial σ K) (D : ℕ) (hH : H.IsHomogeneous D) (n : ℕ) :
    homogeneousComponent n (H * ∏ j, (1 + y j) ^ m j) =
      if D ≤ n then H * esymmW m y (n - D) else 0 := by
  rw [prod_one_add_pow_eq_sum_esymmW m y (∑ j, m j + n) (Nat.le_add_right _ _), Finset.mul_sum,
    map_sum]
  have hterm : ∀ k, homogeneousComponent n (H * esymmW m y k) =
      if n = D + k then H * esymmW m y k else 0 := fun k =>
    homogeneousComponent_of_mem (hH.mul (esymmW_isHomogeneous m y hy k))
  simp only [hterm]
  split_ifs with hD
  · rw [Finset.sum_eq_single (n - D)]
    · rw [if_pos (by omega)]
    · intro k _ hk
      rw [if_neg (by omega)]
    · intro hk
      exact absurd (mem_range.2 (by omega)) hk
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]

end Component

end

end Depth3Note
