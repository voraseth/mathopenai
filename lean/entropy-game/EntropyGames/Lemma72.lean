/-
Section 7 of the paper: Lemma 7.2 (separation at threshold 1).

The statement is the paper's, with the paper's constant `H = n (q + 2 n a_max)^n`.  The proof
follows the paper up to the polynomial `ψ` (characteristic polynomial of the integer matrix
`A = q M_CC` with the factor `(z - q)^ν` removed; `ψ(q)` is a nonzero integer; the complex
roots of `ψ` are eigenvalues of `A`, of modulus at most the maximal row sum).  In the last
step the value `ψ(q)` is written as the product of `q - r` over the complex roots `r` of `ψ`, one
of which is `α = q ρ_C`.  This gives `1 ≤ |q - α| (q + n a_max)^{n-1}`.
-/
import EntropyGames.Lemma71a

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical Polynomial

section core

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The complex roots of the characteristic polynomial of an integer matrix are its
eigenvalues. -/
theorem charpoly_root_iff (A : Matrix κ κ ℤ) (μ : ℂ) :
    (A.charpoly.map (Int.castRingHom ℂ)).eval μ = 0 ↔
      ∃ w : κ → ℂ, w ≠ 0 ∧ ∀ i, ∑ j, (A i j : ℂ) * w j = μ * w i := by
  rw [← Matrix.charpoly_map, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun w => and_congr Iff.rfl ?_
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Pi.zero_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal,
    sub_eq_zero]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom]
  exact eq_comm

/-- An eigenvalue has modulus at most the maximal row sum. -/
theorem eigen_norm_le (A : Matrix κ κ ℤ) {amax : ℕ} (hA : ∀ i j, |A i j| ≤ (amax : ℤ))
    {μ : ℂ} {w : κ → ℂ} (hw : w ≠ 0) (h : ∀ i, ∑ j, (A i j : ℂ) * w j = μ * w i) :
    ‖μ‖ ≤ Fintype.card κ * amax := by
  haveI : Nonempty κ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hw (Subsingleton.elim _ _)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖w i‖) Finset.univ_nonempty
  have hwi : 0 < ‖w i‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hw
    funext j
    have := hi j (Finset.mem_univ j)
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have h1 : ‖μ‖ * ‖w i‖ ≤ (Fintype.card κ * amax) * ‖w i‖ := by
    rw [← norm_mul, ← h i]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(A i j : ℂ) * w j‖ ≤ ∑ _j : κ, (amax : ℝ) * ‖w i‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul ?_ (hi j (Finset.mem_univ j)) (norm_nonneg _) (by positivity)
          rw [Complex.norm_intCast]
          exact_mod_cast hA i j
      _ = Fintype.card κ * amax * ‖w i‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  exact le_of_mul_le_mul_right h1 hwi

theorem norm_multiset_prod_sub_le {B : ℝ} (hB : 0 ≤ B) (c : ℂ) (s : Multiset ℂ)
    (h : ∀ r ∈ s, ‖c - r‖ ≤ B) :
    ‖(s.map (fun r => c - r)).prod‖ ≤ B ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih fun r hr => h r (Multiset.mem_cons_of_mem hr)) (norm_nonneg _) hB

/-- The core of Lemma 7.2: a real eigenvalue `α ≠ q` of an integer matrix with entries of
modulus at most `a_max` is at distance at least `(q + k a_max)^{-(k-1)}` from the integer `q`. -/
theorem int_eigen_sep (A : Matrix κ κ ℤ) {amax q : ℕ} (hq : 1 ≤ q)
    (hA : ∀ i j, |A i j| ≤ (amax : ℤ)) {α : ℝ} {v : κ → ℝ} (hv : v ≠ 0)
    (hAv : ∀ i, ∑ j, (A i j : ℝ) * v j = α * v i) (hαq : α ≠ q) :
    1 ≤ |α - q| * ((q : ℝ) + Fintype.card κ * amax) ^ (Fintype.card κ - 1) := by
  have hφm : A.charpoly.Monic := A.charpoly_monic
  obtain ⟨ψ, hφ, hnd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd A.charpoly hφm.ne_zero (q : ℤ)
  obtain ⟨ν, hν⟩ : ∃ ν, ν = rootMultiplicity (q : ℤ) A.charpoly := ⟨_, rfl⟩
  rw [← hν] at hφ
  have hpm : ((X - C (q : ℤ)) ^ ν).Monic := (monic_X_sub_C _).pow _
  have hψm : ψ.Monic := hpm.of_mul_monic_left (hφ ▸ hφm)
  have hψq : ψ.eval (q : ℤ) ≠ 0 := fun h => hnd (dvd_iff_isRoot.mpr h)
  have hφc : A.charpoly.map (Int.castRingHom ℂ)
      = (X - C (q : ℂ)) ^ ν * ψ.map (Int.castRingHom ℂ) := by
    conv_lhs => rw [hφ]
    simp [Polynomial.map_mul, Polynomial.map_pow]
  have hroot : ∀ μ : ℂ, (ψ.map (Int.castRingHom ℂ)).eval μ = 0 →
      ‖μ‖ ≤ Fintype.card κ * amax := by
    intro μ hμ
    have : (A.charpoly.map (Int.castRingHom ℂ)).eval μ = 0 := by
      rw [hφc, eval_mul, hμ, mul_zero]
    obtain ⟨w, hw, hw'⟩ := (charpoly_root_iff A μ).mp this
    exact eigen_norm_le A hA hw hw'
  have hα : (ψ.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0 := by
    have h1 : (A.charpoly.map (Int.castRingHom ℂ)).eval (α : ℂ) = 0 := by
      rw [charpoly_root_iff]
      refine ⟨fun i => (v i : ℂ), ?_, fun i => ?_⟩
      · intro h0
        apply hv
        funext i
        have := congrFun h0 i
        simpa using this
      · have := congrArg (Complex.ofReal) (hAv i)
        push_cast at this
        exact this
    rw [hφc, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exfalso
      have h3 : (α : ℂ) - q = 0 := eq_zero_of_pow_eq_zero h
      apply hαq
      have h4 : (α : ℂ) = ((q : ℝ) : ℂ) := by rw [sub_eq_zero] at h3; simpa using h3
      exact_mod_cast h4
    · exact h
  have hmc : (ψ.map (Int.castRingHom ℂ)).Monic := hψm.map _
  have hev := (IsAlgClosed.splits (ψ.map (Int.castRingHom ℂ))).eval_eq_prod_roots_of_monic hmc
    (q : ℂ)
  have hαmem : (α : ℂ) ∈ (ψ.map (Int.castRingHom ℂ)).roots := (mem_roots hmc.ne_zero).mpr hα
  have hint : (ψ.map (Int.castRingHom ℂ)).eval (q : ℂ) = ((ψ.eval (q : ℤ) : ℤ) : ℂ) := by
    rw [eval_natCast_map]; rfl
  have hone : (1 : ℝ) ≤ ‖(ψ.map (Int.castRingHom ℂ)).eval (q : ℂ)‖ := by
    rw [hint, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hψq
  have hk0 : (0 : ℝ) ≤ Fintype.card κ * amax := by positivity
  have hB1 : (1 : ℝ) ≤ (q : ℝ) + Fintype.card κ * amax := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [← Multiset.cons_erase hαmem, Multiset.map_cons, Multiset.prod_cons] at hev
  have hrest := norm_multiset_prod_sub_le (B := (q : ℝ) + Fintype.card κ * amax) (by linarith)
    (q : ℂ) ((ψ.map (Int.castRingHom ℂ)).roots.erase (α : ℂ)) (fun r hr => by
      have hr' := Multiset.mem_of_mem_erase hr
      have h1 := hroot r ((mem_roots hmc.ne_zero).mp hr')
      calc ‖(q : ℂ) - r‖ ≤ ‖(q : ℂ)‖ + ‖r‖ := norm_sub_le _ _
        _ ≤ (q : ℝ) + Fintype.card κ * amax := by
          rw [Complex.norm_natCast]; linarith)
  have hcard : Multiset.card ((ψ.map (Int.castRingHom ℂ)).roots.erase (α : ℂ))
      ≤ Fintype.card κ - 1 := by
    rw [Multiset.card_erase_of_mem hαmem]
    have h1 := card_roots' (ψ.map (Int.castRingHom ℂ))
    have h2 : (ψ.map (Int.castRingHom ℂ)).natDegree = ψ.natDegree := hψm.natDegree_map _
    have h3 := hpm.natDegree_mul hψm
    rw [← hφ, Matrix.charpoly_natDegree_eq_dim] at h3
    have : Multiset.card (ψ.map (Int.castRingHom ℂ)).roots ≤ Fintype.card κ := by omega
    exact Nat.pred_le_pred this
  have hnorm : ‖(q : ℂ) - (α : ℂ)‖ = |α - q| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm]
  rw [hev, norm_mul, hnorm] at hone
  refine hone.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  exact hrest.trans (pow_le_pow_right₀ hB1 hcard)

end core

/-- Lemma 7.2 for one class: if `M = a/q` entrywise with integers `0 ≤ a_{ij} ≤ a_max`, then
`ln ρ_C` is `0` or at least `1/H` in absolute value, `H = n (q + 2 n a_max)^n`. -/
theorem perron_sep {ι : Type*} [Fintype ι] {M : ι → ι → ℝ} {q amax : ℕ} (hq : 1 ≤ q)
    (a : ι → ι → ℕ) (ha : ∀ i j, a i j ≤ amax) (hMa : ∀ i j, M i j = (a i j : ℝ) / q)
    {C : Finset ι} {ρ : ℝ} {U : ι → ℝ} (hU : IsPerronPair M C ρ U) :
    Real.log ρ = 0 ∨
      1 / ((Fintype.card ι * (q + 2 * Fintype.card ι * amax) ^ Fintype.card ι : ℕ) : ℝ)
        ≤ |Real.log ρ| := by
  obtain ⟨hρ, hU1, ⟨k0, hk0C, hk0⟩, hMU⟩ := hU
  by_cases hρ1 : ρ = 1
  · left; rw [hρ1, Real.log_one]
  right
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  let A : Matrix {j // j ∈ C} {j // j ∈ C} ℤ := fun i j => (a i.1 j.1 : ℤ)
  have hA : ∀ i j, |A i j| ≤ (amax : ℤ) := by
    intro i j
    simp only [A]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast ha i.1 j.1
  have hv : (fun i : {j // j ∈ C} => U i.1) ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨k0, hk0C⟩
    simp only [Pi.zero_apply] at this
    rw [hk0] at this
    exact one_ne_zero this
  have hAv : ∀ i : {j // j ∈ C}, ∑ j, (A i j : ℝ) * U j.1 = (q * ρ) * U i.1 := by
    intro i
    rw [Finset.sum_coe_sort C (fun j => ((a i.1 j : ℤ) : ℝ) * U j), mul_assoc, ← hMU i.1 i.2,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hMa]
    push_cast
    field_simp
  have hαq : (q : ℝ) * ρ ≠ q := by
    intro h
    apply hρ1
    have : (q : ℝ) * ρ = q * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hq0.ne' this
  have hcore := int_eigen_sep A hq hA hv hAv hαq
  -- `α = q ρ ≤ k a_max`
  have hαle : (q : ℝ) * ρ ≤ Fintype.card {j // j ∈ C} * amax := by
    have h := eigen_norm_le A hA (μ := ((q * ρ : ℝ) : ℂ)) (w := fun i => (U i.1 : ℂ))
      (by
        intro h0
        apply hv
        funext i
        have := congrFun h0 i
        simpa using this)
      (fun i => by
        have := congrArg (Complex.ofReal) (hAv i)
        push_cast at this
        push_cast
        exact this)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hq0 hρ)] at h
    exact h
  have hcardC : Fintype.card {j // j ∈ C} ≤ Fintype.card ι := by
    rw [Fintype.card_coe]; exact Finset.card_le_univ C
  have hcardC' : (Fintype.card {j // j ∈ C} : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcardC
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨k0⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = Fintype.card {j // j ∈ C} := ⟨_, rfl⟩
  rw [← hn] at hcardC hcardC' hn1 ⊢
  rw [← hk] at hcardC hcardC' hcore hαle
  have ham0 : (0 : ℝ) ≤ amax := by positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = q + n * amax := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by
    rw [hB]
    have : (0 : ℝ) ≤ n * amax := by positivity
    linarith
  have hBk : (q : ℝ) + k * amax ≤ B := by
    rw [hB]
    have := mul_le_mul_of_nonneg_right hcardC' ham0
    linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = B ^ (n - 1) := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hX]; exact one_le_pow₀ hB1
  have hpow : ((q : ℝ) + k * amax) ^ (k - 1) ≤ X := by
    rw [hX]
    have hk0' : (0 : ℝ) ≤ (q : ℝ) + k * amax := by positivity
    exact (pow_le_pow_left₀ hk0' hBk _).trans (pow_le_pow_right₀ hB1 (by omega))
  have hcore' : 1 ≤ |(q : ℝ) * ρ - q| * X :=
    hcore.trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
  -- `q |ρ - 1| ≤ |ln ρ| B`
  have hkey : |(q : ℝ) * ρ - q| ≤ |Real.log ρ| * B := by
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have h1 := Real.log_le_sub_one_of_pos hρ
      have hneg : Real.log ρ < 0 := Real.log_neg hρ hlt
      rw [abs_of_neg hneg, abs_of_neg (by nlinarith)]
      have hBq : (q : ℝ) ≤ B := by
        rw [hB]
        have : (0 : ℝ) ≤ n * amax := by positivity
        linarith
      have h2 : 0 ≤ 1 - ρ := by linarith
      nlinarith
    · have h1 := Real.one_sub_inv_le_log_of_pos hρ
      have hpos : 0 < Real.log ρ := Real.log_pos hgt
      rw [abs_of_pos hpos, abs_of_pos (by nlinarith)]
      have hαB : (q : ℝ) * ρ ≤ B := by
        have : (0 : ℝ) ≤ q := hq0.le
        have : (k : ℝ) * amax ≤ (q : ℝ) + k * amax := by linarith
        linarith
      have h2 : (ρ - 1) / ρ ≤ Real.log ρ := by
        have : (ρ - 1) / ρ = 1 - ρ⁻¹ := by field_simp
        rw [this]; exact h1
      have h3 : (q : ℝ) * ρ - q = (ρ - 1) / ρ * (q * ρ) := by field_simp
      rw [h3]
      have h4 : 0 ≤ (ρ - 1) / ρ := div_nonneg (by linarith) hρ.le
      calc (ρ - 1) / ρ * (q * ρ) ≤ (ρ - 1) / ρ * B := mul_le_mul_of_nonneg_left hαB h4
        _ ≤ Real.log ρ * B := mul_le_mul_of_nonneg_right h2 (by linarith)
  have hfin : 1 ≤ |Real.log ρ| * (B * X) := by
    have := mul_le_mul_of_nonneg_right hkey (by linarith : (0 : ℝ) ≤ X)
    linarith
  have hBX : B * X ≤ ((n * (q + 2 * n * amax) ^ n : ℕ) : ℝ) := by
    have e : B * X = B ^ n := by
      rw [hX, ← pow_succ']
      congr 1
      omega
    rw [e]
    push_cast
    have h1 : B ≤ (q : ℝ) + 2 * n * amax := by
      rw [hB]
      have : (0 : ℝ) ≤ n * amax := by positivity
      linarith
    have h2 : B ^ n ≤ ((q : ℝ) + 2 * n * amax) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h4 : (0 : ℝ) ≤ ((q : ℝ) + 2 * n * amax) ^ n := by positivity
    nlinarith
  have hBXpos : 0 < B * X := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hBXpos hBX)]
  have habs := abs_nonneg (Real.log ρ)
  calc (1 : ℝ) ≤ |Real.log ρ| * (B * X) := hfin
    _ ≤ |Real.log ρ| * ((n * (q + 2 * n * amax) ^ n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hBX habs

section game

variable {D T P : Type*} [Fintype D] (Γ : EntropyGame D T P)

/-- **Lemma 7.2 (separation at threshold 1), first sentence**: for all policies `σ`, `τ` and
all `d`, either `λ^{στ}_d = 0` or `|λ^{στ}_d| ≥ 1/H`, `H = n (q + 2 n a_max)^n`. -/
theorem lemma_7_2_policies {q amax : ℕ} (hnorm : IsNormalised Γ q amax)
    (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) (d : D) :
    lam (polMatrix Γ σ τ) d = 0 ∨
      1 / ((Fintype.card D * (q + 2 * Fintype.card D * amax) ^ Fintype.card D : ℕ) : ℝ)
        ≤ |lam (polMatrix Γ σ τ) d| := by
  have hM := polMatrix_matHyp hnorm σ τ
  obtain ⟨hq, hw⟩ := hnorm
  have hex : ∀ d d' : D, ∃ a : ℕ, a ≤ amax ∧ polMatrix Γ σ τ d d' = (a : ℝ) / q := by
    intro d d'
    by_cases h : d' ∈ Γ.outP (τ.move (σ.move d))
    · obtain ⟨a, _, ha2, hm⟩ := hw _ _ h
      exact ⟨a, ha2, by unfold polMatrix; rw [if_pos h, hm]⟩
    · exact ⟨0, Nat.zero_le _, by unfold polMatrix; rw [if_neg h]; simp⟩
  choose a ha hMa using hex
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 1 / ((Fintype.card D * (q + 2 * Fintype.card D * amax)
      ^ Fintype.card D : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hH]
  have hclosed : IsClosed {x : ℝ | x = 0 ∨ H ≤ |x|} :=
    (isClosed_eq continuous_id continuous_const).union
      (isClosed_le continuous_const continuous_abs)
  have hsub : lamSet (polMatrix Γ σ τ) d ⊆ {x : ℝ | x = 0 ∨ H ≤ |x|} := by
    rintro _ ⟨C, ρ, U, _, _, hU, rfl⟩
    have := perron_sep hq a ha hMa hU
    rw [← hH] at this
    exact this
  have hmem := csSup_mem_closure (lamSet_nonempty hM d) (lamSet_bddAbove hM d)
  rw [← lam_eq_sSup] at hmem
  exact closure_minimal hsub hclosed hmem

/-- "χ_d is one of the λ^{στ}_d" (proof of Lemma 7.2; from Lemma 7.1(a)). -/
theorem chi_eq_lam {V : D → ℝ} (hV : IsValueWithPolicies Γ V) (d : D) :
    ∃ (σ : DespotPolicy Γ) (τ : TribunePolicy Γ), Real.log (V d) = lam (polMatrix Γ σ τ) d :=
  chi_eq_lam_of_a (χ := fun d => Real.log (V d)) d
    (lemma_7_1_a Γ hV d).2.1 (lemma_7_1_a Γ hV d).2.2

/-- **Lemma 7.2 (separation at threshold 1), second sentence**: for every `d`, either
`χ_d = 0` or `|χ_d| ≥ 1/H`. -/
theorem lemma_7_2 {V : D → ℝ} (hV : IsValueWithPolicies Γ V) {q amax : ℕ}
    (hnorm : IsNormalised Γ q amax) (d : D) :
    Real.log (V d) = 0 ∨
      1 / ((Fintype.card D * (q + 2 * Fintype.card D * amax) ^ Fintype.card D : ℕ) : ℝ)
        ≤ |Real.log (V d)| := by
  obtain ⟨σ, τ, h⟩ := chi_eq_lam Γ hV d
  rw [h]
  exact lemma_7_2_policies Γ hnorm σ τ d

end game

end EntropyGames
