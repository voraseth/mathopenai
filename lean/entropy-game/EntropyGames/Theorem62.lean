/-
Section 6 of the paper: Theorem 6.2 (the quantitative discount bound), reducible matrices
included, with the constant `R = 3n(2 ln N + 4nΩ + 2)` of the paper.

Organisation of the proof (the estimates are those of the paper):
* lower bound: sub-solution `c + ln U` on a nontrivial class, then propagation along a path;
  the path-length bound `≤ n - 1` is obtained by a counting argument (`reach_induction`);
* upper bound: the paper's induction on the height of a class is replaced by an induction on
  the number of states accessible from `i` (a state below a class has strictly fewer accessible
  states); the recurrence `R_{h+1} = (1+2θ)(R_h + Ω + ln N + 1) + Ω + O_n` is the paper's,
  started at `0` one step earlier, which makes the closed classes a special case of the step.
The comparison map `PsiC` is the map `Ψ` of the paper's proof, extended by `v` outside `C`, so
that no restriction to a subtype is needed.
-/
import EntropyGames.Lam

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

variable {ι : Type*} [Fintype ι]

/-- Counting form of "a path can be taken with at most `n - 1` arcs": if `Q 0` holds on `S`,
`Q k` is monotone in `k`, and `Q k b` gives `Q (k+1) a` along every arc `a → b`, then
`Q (n-1)` holds at every state from which `S` is accessible. -/
theorem reach_induction {r : ι → ι → Prop} (Q : ℕ → ι → Prop) (S : Set ι)
    (h0 : ∀ j ∈ S, Q 0 j) (hmono : ∀ k i, Q k i → Q (k + 1) i)
    (hstep : ∀ k a b, r a b → Q k b → Q (k + 1) a) (i : ι)
    (hi : ∃ j ∈ S, Relation.ReflTransGen r i j) : Q (Fintype.card ι - 1) i := by
  have hmono0 : ∀ k j, Q 0 j → Q k j := by
    intro k j hj
    induction k with
    | zero => exact hj
    | succ k ih => exact hmono k j ih
  let B : Finset ι := Finset.univ.filter fun x => ∃ j ∈ S, Relation.ReflTransGen r x j
  let T : ℕ → Finset ι := fun k => B.filter (Q k)
  have hTmono : ∀ k, T k ⊆ T (k + 1) := by
    intro k x hx
    simp only [T, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hmono k x hx.2⟩
  have hTB : ∀ k, T k ⊆ B := fun k => Finset.filter_subset _ _
  have hiB : i ∈ B := by simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
  have hclaim : ∀ k, T k = B ∨ k + 1 ≤ (T k).card := by
    intro k
    induction k with
    | zero =>
      right
      obtain ⟨j, hjS, _⟩ := hi
      have : j ∈ T 0 := by
        simp only [T, B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨j, hjS, Relation.ReflTransGen.refl⟩, h0 j hjS⟩
      exact Finset.card_pos.mpr ⟨j, this⟩
    | succ k ih =>
      by_cases hk : T k = B
      · left
        exact Finset.Subset.antisymm (hTB _) (hk ▸ hTmono k)
      · right
        have hcard : k + 1 ≤ (T k).card := ih.resolve_left hk
        obtain ⟨x, hxB, hxT⟩ : ∃ x ∈ B, x ∉ T k := by
          by_contra hcon
          push Not at hcon
          exact hk (Finset.Subset.antisymm (hTB k) hcon)
        have hxQ : ¬ Q k x := fun hq => hxT (by simp only [T, Finset.mem_filter]; exact ⟨hxB, hq⟩)
        obtain ⟨j, hjS, hxj⟩ : ∃ j ∈ S, Relation.ReflTransGen r x j := by
          simpa [B] using hxB
        obtain ⟨a, b, _, hab, hbj, haS, hbS⟩ :=
          exists_crossing (S := {y | ¬ Q k y}) hxj hxQ (fun h => h (hmono0 k j (h0 j hjS)))
        have hbQ : Q k b := by
          by_contra hb; exact hbS hb
        have haB : a ∈ B := by
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hjS, Relation.ReflTransGen.head hab hbj⟩
        have haT : a ∈ T (k + 1) := by
          simp only [T, Finset.mem_filter]; exact ⟨haB, hstep k a b hab hbQ⟩
        have haT' : a ∉ T k := fun h => haS (by simp only [T, Finset.mem_filter] at h; exact h.2)
        have hss : T k ⊂ T (k + 1) := ⟨hTmono k, fun hsub => haT' (hsub haT)⟩
        have := Finset.card_lt_card hss
        omega
  have hiT : i ∈ T (Fintype.card ι - 1) := by
    rcases hclaim (Fintype.card ι - 1) with h | h
    · rw [h]; exact hiB
    · have h1 := Finset.card_le_univ (T (Fintype.card ι - 1))
      have h2 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
      have : T (Fintype.card ι - 1) = Finset.univ := Finset.eq_univ_of_card _ (by omega)
      rw [this]; exact Finset.mem_univ i
  simp only [T, Finset.mem_filter] at hiT
  exact hiT.2

/-- The comparison map of the proof of Theorem 6.2: on `C` it is
`Ψ(t)_a = γ ln(∑_{j∈C} M_{aj} e^{t_j} + ∑_{j∉C} M_{aj} e^{v_j})`; outside `C` it is the
constant `v_a`. -/
noncomputable def PsiC (γ : ℝ) (M : ι → ι → ℝ) (C : Finset ι) (v t : ι → ℝ) (a : ι) : ℝ :=
  if a ∈ C then
    γ * Real.log (∑ j ∈ C, M a j * Real.exp (t j) + ∑ j ∈ Cᶜ, M a j * Real.exp (v j))
  else v a

section PsiC

variable {γ : ℝ} {M : ι → ι → ℝ} {C : Finset ι}

theorem PsiC_inner_pos (hM : ∀ i j, 0 ≤ M i j) (hrowC : ∀ a ∈ C, ∃ j ∈ C, 0 < M a j)
    (t : ι → ℝ) {a : ι} (ha : a ∈ C) : 0 < ∑ j ∈ C, M a j * Real.exp (t j) := by
  obtain ⟨j, hj, hpos⟩ := hrowC a ha
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hM a j) (Real.exp_pos _).le)
    ⟨j, hj, mul_pos hpos (Real.exp_pos _)⟩

theorem PsiC_outer_nonneg (hM : ∀ i j, 0 ≤ M i j) (v : ι → ℝ) (a : ι) :
    0 ≤ ∑ j ∈ Cᶜ, M a j * Real.exp (v j) :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hM a j) (Real.exp_pos _).le

/-- `PsiC` is monotone and satisfies `Ψ(t + c𝟙) ≤ Ψ(t) + γc𝟙` for `c ≥ 0`. -/
theorem PsiC_isSub (hγ : 0 ≤ γ) (hM : ∀ i j, 0 ≤ M i j)
    (hrowC : ∀ a ∈ C, ∃ j ∈ C, 0 < M a j) (v : ι → ℝ) :
    IsSubDiscounted γ (PsiC γ M C v) := by
  constructor
  · intro t t' htt a
    unfold PsiC
    split_ifs with ha
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hγ
      · linarith [PsiC_inner_pos hM hrowC t ha, PsiC_outer_nonneg (C := C) hM v a]
      · have : ∑ j ∈ C, M a j * Real.exp (t j) ≤ ∑ j ∈ C, M a j * Real.exp (t' j) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (htt j)) (hM a j)
        linarith
    · exact le_rfl
  · intro t c hc a
    unfold PsiC
    split_ifs with ha
    · have hS := PsiC_inner_pos hM hrowC t ha
      have hE := PsiC_outer_nonneg (C := C) hM v a
      have h1 : ∑ j ∈ C, M a j * Real.exp (t j + c)
          = Real.exp c * ∑ j ∈ C, M a j * Real.exp (t j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Real.exp_add]; ring
      have hec : 1 ≤ Real.exp c := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hc
      have h2 : ∑ j ∈ C, M a j * Real.exp (t j + c) + ∑ j ∈ Cᶜ, M a j * Real.exp (v j)
          ≤ Real.exp c * (∑ j ∈ C, M a j * Real.exp (t j) + ∑ j ∈ Cᶜ, M a j * Real.exp (v j)) := by
        rw [h1, mul_add]
        have := mul_le_mul_of_nonneg_right hec hE
        linarith
      have hpos : 0 < ∑ j ∈ C, M a j * Real.exp (t j) + ∑ j ∈ Cᶜ, M a j * Real.exp (v j) := by
        linarith
      have hpos' : 0 < ∑ j ∈ C, M a j * Real.exp (t j + c) + ∑ j ∈ Cᶜ, M a j * Real.exp (v j) := by
        have := PsiC_inner_pos hM hrowC (fun j => t j + c) ha
        linarith
      have h3 := Real.log_le_log hpos' h2
      rw [Real.log_mul (Real.exp_pos c).ne' hpos.ne', Real.log_exp] at h3
      have := mul_le_mul_of_nonneg_left h3 hγ
      linarith
    · have := mul_nonneg hγ hc
      linarith

/-- The fixed point `v` of `Ψ_M` is a fixed point of `PsiC`. -/
theorem PsiC_fixed {v : ι → ℝ} (hv : Psi γ M v = v) : PsiC γ M C v v = v := by
  funext a
  unfold PsiC
  split_ifs with ha
  · rw [Finset.sum_add_sum_compl]
    exact congrFun hv a
  · rfl

/-- The inner sum of `PsiC` at `c + ln U`. -/
theorem PsiC_eigen_sum {U : ι → ℝ} {ρ : ℝ} (hU : ∀ i ∈ C, 0 < U i)
    (hMU : ∀ i ∈ C, ∑ j ∈ C, M i j * U j = ρ * U i) {w : ι → ℝ} {c : ℝ}
    (hw : ∀ j ∈ C, w j = c + Real.log (U j)) {a : ι} (ha : a ∈ C) :
    ∑ j ∈ C, M a j * Real.exp (w j) = Real.exp c * (ρ * U a) := by
  rw [← hMU a ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hw j hj, Real.exp_add, Real.exp_log (hU j hj)]
  ring

end PsiC

section lower

variable {M : ι → ι → ℝ} {mmin mmax Ω : ℝ} {N : ℕ} {v : ι → ℝ}

/-- `-Ω ≤ ln m` for a positive entry `m`. -/
theorem MatHyp.neg_le_log_entry [Nonempty ι] (hM : MatHyp M mmin mmax Ω) {a b : ι}
    (hab : 0 < M a b) : -Ω ≤ Real.log (M a b) := by
  obtain ⟨_, hA2, _, _⟩ := hM.exp_bounds
  rw [Real.le_log_iff_exp_le hab, Real.exp_neg]
  refine le_trans ?_ (hM.lo a b hab)
  rw [inv_le_comm₀ (Real.exp_pos _) hM.mmin_pos, ← one_div]
  exact hA2

/-- Lower bound of Theorem 6.2 on the class itself: `θ v_j ≥ γ ln ρ_C - θ O_n` for `j ∈ C`. -/
theorem lower_on_class [Nonempty ι] (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) {C : Finset ι} (hC : IsNontrivialClass M C)
    {ρ : ℝ} {U : ι → ℝ} (hU : IsPerronPair M C ρ U) {a : ι} (ha : a ∈ C) :
    (1 - 1 / (N : ℝ)) * Real.log ρ - 1 / (N : ℝ) * (2 * (Fintype.card ι - 1) * Ω)
      ≤ 1 / (N : ℝ) * v a := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hO := lemma_6_1_b hM hC hU
  obtain ⟨hρ, hU1, _, hMU⟩ := hU
  have hUpos : ∀ i ∈ C, 0 < U i := fun i hi => lt_of_lt_of_le one_pos (hU1 i hi)
  set θ : ℝ := 1 / (N : ℝ) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  set O : ℝ := 2 * (Fintype.card ι - 1) * Ω with hOdef
  set lamC : ℝ := Real.log ρ with hlamC
  set c : ℝ := ((1 - θ) * lamC - θ * O) / θ with hc
  have hθc : θ * c = (1 - θ) * lamC - θ * O := by rw [hc]; field_simp
  let w : ι → ℝ := fun x => if x ∈ C then c + Real.log (U x) else v x
  have hwC : ∀ j ∈ C, w j = c + Real.log (U j) := fun j hj => if_pos hj
  have hsub := PsiC_isSub (γ := 1 - θ) (C := C) (by linarith) hM.nonneg (fun a ha => hC.row ha) v
  have hw : w ≤ PsiC (1 - θ) M C v w := by
    intro x
    by_cases hx : x ∈ C
    · have hS := PsiC_eigen_sum hUpos hMU hwC hx
      have hE := PsiC_outer_nonneg (C := C) hM.nonneg v x
      have hpos : 0 < Real.exp c * (ρ * U x) :=
        mul_pos (Real.exp_pos c) (mul_pos hρ (hUpos x hx))
      have hlog : Real.log (Real.exp c * (ρ * U x)) = c + lamC + Real.log (U x) := by
        rw [Real.log_mul (Real.exp_pos c).ne' (mul_pos hρ (hUpos x hx)).ne', Real.log_exp,
          Real.log_mul hρ.ne' (hUpos x hx).ne']
        ring
      have h1 : c + lamC + Real.log (U x)
          ≤ Real.log (∑ j ∈ C, M x j * Real.exp (w j) + ∑ j ∈ Cᶜ, M x j * Real.exp (v j)) := by
        rw [hS, ← hlog]
        exact Real.log_le_log hpos (by linarith)
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 - θ by linarith)
      have h3 : θ * Real.log (U x) ≤ θ * O := mul_le_mul_of_nonneg_left (hO x hx).2 hθpos.le
      have hgoal : c + Real.log (U x) ≤ (1 - θ) *
          Real.log (∑ j ∈ C, M x j * Real.exp (w j) + ∑ j ∈ Cᶜ, M x j * Real.exp (v j)) := by
        linarith
      simpa only [PsiC, if_pos hx, hwC x hx] using hgoal
    · simp [PsiC, w, hx]
  have hle := hsub.le_fixed (by linarith) (PsiC_fixed hv) hw a
  rw [hwC a ha] at hle
  have h2 := mul_le_mul_of_nonneg_left hle hθpos.le
  have h3 := mul_nonneg hθpos.le (hO a ha).1
  linarith

/-- One arc: `v_a ≥ γ v_b - Ω` if `a → b`. -/
theorem arc_step [Nonempty ι] (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) {a b : ι} (hab : 0 < M a b) :
    (1 - 1 / (N : ℝ)) * v b - Ω ≤ v a := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨_, _, hΩ0, _⟩ := hM.exp_bounds
  have hθpos : 0 < 1 / (N : ℝ) := by positivity
  have hθ1 : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h1 : (1 - 1 / (N : ℝ)) * Real.log (∑ j, M a j * Real.exp (v j)) = v a := congrFun hv a
  have h2 : M a b * Real.exp (v b) ≤ ∑ j, M a j * Real.exp (v j) :=
    Finset.single_le_sum (f := fun j => M a j * Real.exp (v j))
      (fun j _ => mul_nonneg (hM.nonneg a j) (Real.exp_pos _).le) (Finset.mem_univ b)
  have h3 : Real.log (M a b) + v b ≤ Real.log (∑ j, M a j * Real.exp (v j)) := by
    have := Real.log_le_log (mul_pos hab (Real.exp_pos (v b))) h2
    rwa [Real.log_mul hab.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have h4 := hM.neg_le_log_entry hab
  have h5 := mul_le_mul_of_nonneg_left (show -Ω + v b ≤ Real.log (∑ j, M a j * Real.exp (v j)) by
    linarith) (show (0 : ℝ) ≤ 1 - 1 / (N : ℝ) by linarith)
  have h6 : 1 / (N : ℝ) * Ω ≥ 0 := mul_nonneg hθpos.le hΩ0
  linarith

/-- **Lower bound of Theorem 6.2**: `θ v_i ≥ ln ρ_C - 5 n² Ω θ` for every nontrivial class `C`
accessible from `i`. -/
theorem lower_bound [Nonempty ι] (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) {C : Finset ι} (hC : IsNontrivialClass M C)
    {ρ : ℝ} {U : ι → ℝ} (hU : IsPerronPair M C ρ U) {i : ι} (hacc : ∃ j ∈ C, Acc M i j) :
    Real.log ρ - 1 / (N : ℝ) * (5 * (Fintype.card ι : ℝ) ^ 2 * Ω) ≤ 1 / (N : ℝ) * v i := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨_, _, hΩ0, _⟩ := hM.exp_bounds
  have hlamC := (lemma_6_1_a_class hM hC hU).2
  set θ : ℝ := 1 / (N : ℝ) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hNθ : (N : ℝ) * θ = 1 := by rw [hθ]; field_simp
  set γ : ℝ := 1 - θ with hγ
  have hγ0 : 0 ≤ γ := by linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set nn : ℝ := (Fintype.card ι : ℝ) with hnn
  set O : ℝ := 2 * (nn - 1) * Ω with hOdef
  have hO0 : 0 ≤ O := by rw [hOdef]; exact mul_nonneg (by linarith) hΩ0
  set lamC : ℝ := Real.log ρ with hlamCdef
  set z0 : ℝ := γ * lamC - θ * O with hz0
  set a0 : ℝ := N * z0 with ha0
  have hθa0 : θ * a0 = z0 := by rw [ha0, ← mul_assoc, mul_comm θ, hNθ, one_mul]
  -- propagation along a path
  have hQ := reach_induction (r := fun i j => 0 < M i j)
    (fun k x => ∃ l : ℕ, l ≤ k ∧ γ ^ l * a0 - l * Ω ≤ v x) (↑C : Set ι)
    (by
      intro j hj
      refine ⟨0, le_rfl, ?_⟩
      have h : z0 ≤ θ * v j := lower_on_class hM hN hv hC hU (Finset.mem_coe.mp hj)
      have h2 : (N : ℝ) * z0 ≤ N * (θ * v j) := mul_le_mul_of_nonneg_left h hNpos.le
      rw [← mul_assoc, hNθ, one_mul] at h2
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, sub_zero]
      exact h2)
    (fun k x ⟨l, hl, h⟩ => ⟨l, Nat.le_succ_of_le hl, h⟩)
    (by
      rintro k a b hab ⟨l, hl, h⟩
      refine ⟨l + 1, by omega, ?_⟩
      have h1 := arc_step hM hN hv hab
      have h2 := mul_le_mul_of_nonneg_left h hγ0
      have hlΩ : 0 ≤ (l : ℝ) * Ω := mul_nonneg (Nat.cast_nonneg l) hΩ0
      have h3 : γ * ((l : ℝ) * Ω) ≤ (l : ℝ) * Ω := mul_le_of_le_one_left hlΩ hγ1
      rw [pow_succ]
      push_cast
      linarith)
    i (by obtain ⟨j, hj, hij⟩ := hacc; exact ⟨j, Finset.mem_coe.mpr hj, hij⟩)
  obtain ⟨l, hl, hb⟩ := hQ
  have hln : (l : ℝ) ≤ nn := by
    have : l ≤ Fintype.card ι := by omega
    rw [hnn]
    exact_mod_cast this
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  -- γ^l ∈ [1 - lθ, 1]
  set g : ℝ := γ ^ l with hg
  have hg1 : g ≤ 1 := pow_le_one₀ hγ0 hγ1
  have hg2 : 1 - l * θ ≤ g := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -θ by linarith) l
    have hγ' : (1 : ℝ) + -θ = γ := by rw [hγ]; ring
    rw [hγ'] at this
    linarith
  -- |z0| ≤ Z
  set Z : ℝ := Ω + O with hZ
  have hZ0 : 0 ≤ Z := by linarith
  have hlam := abs_le.mp hlamC
  have hθlam1 : θ * lamC ≤ θ * Ω := mul_le_mul_of_nonneg_left hlam.2 hθpos.le
  have hθlam2 : θ * (-Ω) ≤ θ * lamC := mul_le_mul_of_nonneg_left hlam.1 hθpos.le
  have hθO : θ * O ≤ O := mul_le_of_le_one_left hO0 (by linarith)
  have hθO0 : 0 ≤ θ * O := mul_nonneg hθpos.le hO0
  have hθΩ : 0 ≤ θ * Ω := mul_nonneg hθpos.le hΩ0
  have hγlam : γ * lamC ≤ γ * Ω := mul_le_mul_of_nonneg_left hlam.2 hγ0
  have hγΩ : γ * Ω ≤ Ω := mul_le_of_le_one_left hΩ0 hγ1
  have hz0up : z0 ≤ Z := by rw [hz0, hZ]; linarith
  have hz0lo : lamC - θ * Ω - θ * O ≤ z0 := by rw [hz0, hγ]; linarith
  -- g z0 ≥ z0 - l θ Z
  have hgz : z0 - l * θ * Z ≤ g * z0 := by
    have h1 : (1 - g) * z0 ≤ (1 - g) * Z := mul_le_mul_of_nonneg_left hz0up (by linarith)
    have h2 : (1 - g) * Z ≤ l * θ * Z := mul_le_mul_of_nonneg_right (by linarith) hZ0
    linarith
  have h7 := mul_le_mul_of_nonneg_left hb hθpos.le
  have h8 : θ * (g * a0 - l * Ω) = g * z0 - l * (θ * Ω) := by rw [← hθa0]; ring
  rw [h8] at h7
  have h9 : (l : ℝ) * (θ * Z) ≤ nn * (θ * Z) :=
    mul_le_mul_of_nonneg_right hln (mul_nonneg hθpos.le hZ0)
  have h10 : (l : ℝ) * (θ * Ω) ≤ nn * (θ * Ω) := mul_le_mul_of_nonneg_right hln hθΩ
  -- constants: Ω + O + n (Ω + O) + n Ω ≤ 5 n² Ω
  have hconst : Ω + O + nn * Z + nn * Ω ≤ 5 * nn ^ 2 * Ω := by
    rw [hZ, hOdef]
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ nn by linarith)
      (show (0 : ℝ) ≤ nn - 1 by linarith)) hΩ0, mul_nonneg (show (0 : ℝ) ≤ nn by linarith) hΩ0]
  have h11 := mul_le_mul_of_nonneg_left hconst hθpos.le
  linarith

end lower

section upper

variable {M : ι → ι → ℝ} {mmin mmax Ω : ℝ} {N : ℕ} {v : ι → ℝ}

/-- The induction step of the upper bound of Theorem 6.2 (cases "trivial class" and
"nontrivial class" of the paper; a class with no outgoing arc is the case where `hbelow` is
vacuous).  If `θ v_j ≤ λ_j + θ R'` at every state `j` outside the class of `i₀` that is the
head of an arc from the class, then on the class
`θ v ≤ λ_{i₀} + θ ((1 + 2θ)(R' + Ω + ln N + 1) + Ω + O_n)`. -/
theorem upper_step [Nonempty ι] (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) (i0 : ι) {R' : ℝ} (hR' : 0 ≤ R')
    (hbelow : ∀ a ∈ cls M i0, ∀ j, j ∉ cls M i0 → 0 < M a j →
      1 / (N : ℝ) * v j ≤ lam M j + 1 / (N : ℝ) * R')
    {a : ι} (ha : a ∈ cls M i0) :
    1 / (N : ℝ) * v a ≤ lam M i0 + 1 / (N : ℝ) *
      ((1 + 2 * (1 / (N : ℝ))) * (R' + Ω + Real.log N + 1) + Ω
        + 2 * (Fintype.card ι - 1) * Ω) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hA1, _, hΩ0, _⟩ := hM.exp_bounds
  set θ : ℝ := 1 / (N : ℝ) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hNθ : (N : ℝ) * θ = 1 := by rw [hθ]; field_simp
  set γ : ℝ := 1 - θ with hγ
  have hγ0 : 0 < γ := by linarith
  have hγ1 : γ ≤ 1 := by linarith
  set C : Finset ι := cls M i0 with hCdef
  set lamv : ℝ := lam M i0 with hlamv
  have hlamb := abs_le.mp (lemma_6_1_a_lam hM i0)
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set O : ℝ := 2 * ((Fintype.card ι : ℝ) - 1) * Ω with hOdef
  have hO0 : 0 ≤ O := by rw [hOdef]; exact mul_nonneg (by linarith) hΩ0
  set X : ℝ := R' + Ω + L + 1 with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef]; linarith
  set b : ℝ := N * lamv + R' with hbdef
  have hθb : θ * b = lamv + θ * R' := by
    have h : θ * ((N : ℝ) * lamv + R') = lamv + θ * R' := by linear_combination lamv * hNθ
    exact h
  -- states below the class
  have hb : ∀ x ∈ C, ∀ j, j ∉ C → 0 < M x j → v j ≤ b := by
    intro x hx j hj hxj
    have h1 := hbelow x hx j hj hxj
    have h2 : lam M j ≤ lam M x := lemma_6_1_c hM hxj
    have h3 : lam M x = lamv := lam_eq_of_mem_cls hM hx
    have h4 : θ * v j ≤ θ * b := by rw [hθb]; linarith
    exact le_of_mul_le_mul_left h4 hθpos
  have hrowsum : ∀ (x : ι) (s : Finset ι), ∑ j ∈ s, M x j ≤ Real.exp Ω := by
    intro x s
    calc ∑ j ∈ s, M x j ≤ ∑ j, M x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun j _ _ => hM.nonneg x j
      _ ≤ ∑ _j : ι, mmax := Finset.sum_le_sum fun j _ => hM.hi x j
      _ = Fintype.card ι * mmax := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Real.exp Ω := hA1
  -- a sum over a set none of whose arcs stays in `C`
  have hsumb : ∀ (x : ι), x ∈ C → ∀ s : Finset ι, (∀ j ∈ s, 0 < M x j → j ∉ C) →
      ∑ j ∈ s, M x j * Real.exp (v j) ≤ Real.exp (Ω + b) := by
    intro x hx s hs
    calc ∑ j ∈ s, M x j * Real.exp (v j) ≤ ∑ j ∈ s, M x j * Real.exp b := by
          refine Finset.sum_le_sum fun j hj => ?_
          by_cases hpos : 0 < M x j
          · exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (hb x hx j (hs j hj hpos) hpos)) hpos.le
          · rw [le_antisymm (not_lt.mp hpos) (hM.nonneg x j), zero_mul, zero_mul]
      _ = (∑ j ∈ s, M x j) * Real.exp b := by rw [Finset.sum_mul]
      _ ≤ Real.exp Ω * Real.exp b :=
          mul_le_mul_of_nonneg_right (hrowsum x s) (Real.exp_pos _).le
      _ = Real.exp (Ω + b) := (Real.exp_add _ _).symm
  have h2θX : 0 ≤ 2 * θ * X := by positivity
  have hθlam : θ * (-Ω) ≤ θ * lamv := mul_le_mul_of_nonneg_left hlamb.1 hθpos.le
  by_cases hnt : ∃ x ∈ C, ∃ j ∈ C, 0 < M x j
  · -- nontrivial class
    have hC : IsNontrivialClass M C := ⟨isClass_cls M i0, hnt⟩
    obtain ⟨ρ, U, hU⟩ := perron_frobenius hM.nonneg hC
    have hρle : Real.log ρ ≤ lamv :=
      log_le_lam hM hC ⟨i0, self_mem_cls M i0, Relation.ReflTransGen.refl⟩ hU
    have hO := lemma_6_1_b hM hC hU
    obtain ⟨hρ, hU1, _, hMU⟩ := hU
    have hUpos : ∀ i ∈ C, 0 < U i := fun i hi => lt_of_lt_of_le one_pos (hU1 i hi)
    set η : ℝ := θ / γ * X with hη
    have hγη : γ * η = θ * X := by rw [hη]; field_simp
    set c : ℝ := N * (γ * (lamv + η)) with hc
    have hθc : θ * c = γ * lamv + θ * X := by
      rw [hc, ← mul_assoc, mul_comm θ, hNθ, one_mul, mul_add, hγη]
    have hkey : Ω + b = (lamv + c) + (-L - 1) := by
      have h : Ω + ((N : ℝ) * lamv + R') = (lamv + N * (γ * (lamv + η))) + (-L - 1) := by
        linear_combination (lamv - X) * hNθ - (N : ℝ) * hγη - (N : ℝ) * lamv * hγ - hXdef
      exact h
    obtain ⟨xx, hxx⟩ : ∃ xx : ℝ, xx = Real.exp (-L - 1) := ⟨_, rfl⟩
    have hxxpos : 0 < xx := by rw [hxx]; exact Real.exp_pos _
    have hxxθ : xx ≤ θ := by
      have h1 : Real.exp (-L) = θ := by
        rw [Real.exp_neg, hL, Real.exp_log hNpos, hθ, one_div]
      calc xx = Real.exp (-L) * Real.exp (-1) := by rw [hxx, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-L) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
        _ = θ := by rw [mul_one, h1]
    let w : ι → ℝ := fun x => if x ∈ C then c + Real.log (U x) else v x
    have hwC : ∀ j ∈ C, w j = c + Real.log (U j) := fun j hj => if_pos hj
    have hsub := PsiC_isSub (γ := γ) (C := C) hγ0.le hM.nonneg (fun a ha => hC.row ha) v
    have hw : PsiC γ M C v w ≤ w := by
      intro x
      by_cases hx : x ∈ C
      · have hS := PsiC_eigen_sum hUpos hMU hwC hx
        have hE : ∑ j ∈ Cᶜ, M x j * Real.exp (v j) ≤ Real.exp (Ω + b) :=
          hsumb x hx Cᶜ fun j hj _ => Finset.mem_compl.mp hj
        have hE0 := PsiC_outer_nonneg (C := C) hM.nonneg v x
        have hUx := hUpos x hx
        have hρexp : ρ ≤ Real.exp lamv := (Real.log_le_iff_le_exp hρ).mp hρle
        obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Real.exp (lamv + c) := ⟨_, rfl⟩
        have hBpos : 0 < B := by rw [hB]; exact Real.exp_pos _
        have hlogB : Real.log B = lamv + c := by rw [hB, Real.log_exp]
        have hS1 : Real.exp c * (ρ * U x) ≤ B * U x := by
          rw [hB, Real.exp_add]
          calc Real.exp c * (ρ * U x) = ρ * (Real.exp c * U x) := by ring
            _ ≤ Real.exp lamv * (Real.exp c * U x) :=
                mul_le_mul_of_nonneg_right hρexp (mul_nonneg (Real.exp_pos c).le hUx.le)
            _ = Real.exp lamv * Real.exp c * U x := by ring
        have hE1 : Real.exp (Ω + b) ≤ B * U x * xx := by
          have e : Real.exp (Ω + b) = B * xx := by rw [hkey, Real.exp_add, hB, hxx]
          rw [e]
          have := mul_le_mul_of_nonneg_left (hU1 x hx) (mul_nonneg hBpos.le hxxpos.le)
          linarith only [this]
        have htot : ∑ j ∈ C, M x j * Real.exp (w j) + ∑ j ∈ Cᶜ, M x j * Real.exp (v j)
            ≤ B * U x * (1 + xx) := by
          rw [hS]; linarith only [hS1, hE, hE1]
        have hpos : 0 < ∑ j ∈ C, M x j * Real.exp (w j) + ∑ j ∈ Cᶜ, M x j * Real.exp (v j) := by
          have := PsiC_inner_pos hM.nonneg (fun a ha => hC.row ha) w hx
          linarith only [this, hE0]
        have hlog := Real.log_le_log hpos htot
        have hlog2 : Real.log (B * U x * (1 + xx)) ≤ lamv + c + Real.log (U x) + θ := by
          rw [Real.log_mul (mul_pos hBpos hUx).ne' (by linarith only [hxxpos]),
            Real.log_mul hBpos.ne' hUx.ne', hlogB]
          have := Real.log_le_sub_one_of_pos (show 0 < 1 + xx by linarith only [hxxpos])
          linarith only [this, hxxθ]
        have h3 := mul_le_mul_of_nonneg_left (hlog.trans hlog2) hγ0.le
        have h4 : 0 ≤ θ * Real.log (U x) := mul_nonneg hθpos.le (hO x hx).1
        have h5 : θ * 1 ≤ θ * X := mul_le_mul_of_nonneg_left hX1 hθpos.le
        have h6 : γ * θ ≤ θ := mul_le_of_le_one_left hθpos.le hγ1
        have hgoal : γ * Real.log (∑ j ∈ C, M x j * Real.exp (w j)
            + ∑ j ∈ Cᶜ, M x j * Real.exp (v j)) ≤ c + Real.log (U x) := by
          have e1 : γ * (lamv + c + Real.log (U x) + θ)
              = γ * lamv + (c + Real.log (U x)) - (θ * c + θ * Real.log (U x)) + γ * θ := by
            rw [hγ]; ring
          linarith only [h3, e1, hθc, h4, h5, h6]
        simpa only [PsiC, if_pos hx, hwC x hx] using hgoal
      · simp [PsiC, w, hx]
    have hle := hsub.fixed_le (by linarith) (PsiC_fixed hv) hw a
    rw [hwC a ha] at hle
    have h1 := mul_le_mul_of_nonneg_left hle hθpos.le
    have h2 : θ * Real.log (U a) ≤ θ * O := mul_le_mul_of_nonneg_left (hO a ha).2 hθpos.le
    have h3 : θ * ((1 + 2 * θ) * X + Ω + O) = θ * X + θ * (2 * θ * X) + θ * Ω + θ * O := by ring
    have h4 : 0 ≤ θ * (2 * θ * X) := mul_nonneg hθpos.le h2θX
    have h5 : γ * lamv = lamv - θ * lamv := by rw [hγ]; ring
    rw [h3]
    linarith only [h1, h2, h4, h5, hθc, hθlam]
  · -- trivial class: every arc from `a` leaves the class
    push Not at hnt
    have hS : ∑ j, M a j * Real.exp (v j) ≤ Real.exp (Ω + b) :=
      hsumb a ha Finset.univ fun j _ hpos hjC => absurd hpos (not_lt.mpr (hnt a ha j hjC))
    have hSpos := Psi_sum_pos hM.nonneg hM.row v a
    have hlog : Real.log (∑ j, M a j * Real.exp (v j)) ≤ Ω + b :=
      (Real.log_le_iff_le_exp hSpos).mpr hS
    have hva : γ * Real.log (∑ j, M a j * Real.exp (v j)) = v a := congrFun hv a
    have h1 : v a ≤ γ * (Ω + b) := by
      rw [← hva]; exact mul_le_mul_of_nonneg_left hlog hγ0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hθpos.le
    have e : θ * (γ * (Ω + b)) = γ * (θ * Ω) + γ * (lamv + θ * R') := by rw [← hθb]; ring
    have h3 : γ * (θ * Ω) ≤ θ * Ω := mul_le_of_le_one_left (mul_nonneg hθpos.le hΩ0) hγ1
    have h4 : γ * (lamv + θ * R') = lamv + θ * R' - θ * lamv - θ * (θ * R') := by rw [hγ]; ring
    have h5 : 0 ≤ θ * (θ * R') := mul_nonneg hθpos.le (mul_nonneg hθpos.le hR')
    have h6 : θ * ((1 + 2 * θ) * X + Ω + O)
        = θ * R' + 2 * (θ * Ω) + θ * L + θ + θ * (2 * θ * X) + θ * O := by rw [hXdef]; ring
    have h7 : 0 ≤ θ * (2 * θ * X) := mul_nonneg hθpos.le h2θX
    have h8 : 0 ≤ θ * L := mul_nonneg hθpos.le hL0
    have h9 : 0 ≤ θ * O := mul_nonneg hθpos.le hO0
    rw [h6]
    linarith only [h2, e, h3, h4, h5, h7, h8, h9, hθlam, hθpos]

/-- The recurrence of the upper bound: `R_{k+1} = (1 + 2θ)(R_k + Ω + ln N + 1) + Ω + O_n`. -/
noncomputable def Rs (θ Ω L O : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + 2 * θ) * (Rs θ Ω L O k + Ω + L + 1) + Ω + O

theorem Rs_nonneg {θ Ω L O : ℝ} (hθ : 0 ≤ θ) (hΩ : 0 ≤ Ω) (hL : 0 ≤ L) (hO : 0 ≤ O) :
    ∀ k, 0 ≤ Rs θ Ω L O k
  | 0 => le_rfl
  | k + 1 => by
    have := Rs_nonneg hθ hΩ hL hO k
    simp only [Rs]
    positivity

/-- Solving the recurrence: `R_k ≤ k (1 + 2θ)^k Q` with `Q = 2(Ω + ln N + 1) + Ω + O_n`. -/
theorem Rs_le {θ Ω L O : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (hΩ : 0 ≤ Ω) (hL : 0 ≤ L)
    (hO : 0 ≤ O) : ∀ k : ℕ,
    Rs θ Ω L O k ≤ k * (1 + 2 * θ) ^ k * (2 * (Ω + L + 1) + Ω + O)
  | 0 => by simp [Rs]
  | k + 1 => by
    have ih := Rs_le hθ hθ1 hΩ hL hO k
    simp only [Rs]
    set a : ℝ := 1 + 2 * θ with ha
    set Q : ℝ := 2 * (Ω + L + 1) + Ω + O with hQ
    have ha1 : 1 ≤ a := by linarith
    have ha2 : a ≤ 2 := by linarith
    have hQ0 : 0 ≤ Q := by rw [hQ]; linarith
    have hpow : 1 ≤ a ^ (k + 1) := one_le_pow₀ ha1
    have h1 : a * Rs θ Ω L O k ≤ a * (k * a ^ k * Q) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : a * (Ω + L + 1) + Ω + O ≤ Q := by
      rw [hQ]; nlinarith
    have h3 : Q ≤ a ^ (k + 1) * Q := le_mul_of_one_le_left hQ0 hpow
    have e : a * (k * a ^ k * Q) = k * a ^ (k + 1) * Q := by rw [pow_succ]; ring
    push_cast
    nlinarith

/-- The upper bound of Theorem 6.2, by induction on the number of accessible states. -/
theorem upper_all [Nonempty ι] (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) : ∀ (k : ℕ) (i : ι), (reach M i).card ≤ k →
    1 / (N : ℝ) * v i ≤ lam M i + 1 / (N : ℝ) *
      Rs (1 / (N : ℝ)) Ω (Real.log N) (2 * (Fintype.card ι - 1) * Ω) k := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨_, _, hΩ0, _⟩ := hM.exp_bounds
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hO0 : (0 : ℝ) ≤ 2 * (Fintype.card ι - 1) * Ω := mul_nonneg (by linarith) hΩ0
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hθ0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  intro k
  induction k with
  | zero =>
    intro i hi
    have : 0 < (reach M i).card := Finset.card_pos.mpr ⟨i, self_mem_reach M i⟩
    omega
  | succ k ih =>
    intro i hi
    have hstep := upper_step hM hN hv i (Rs_nonneg hθ0 hΩ0 hL0 hO0 k)
      (fun a ha j hj haj => by
        rw [mem_cls] at ha
        have hij : Acc M i j := ha.1.trans (Acc.of_arc haj)
        have hss : reach M j ⊂ reach M i := by
          refine ⟨reach_subset hij, fun hsub => hj ?_⟩
          have : i ∈ reach M j := hsub (self_mem_reach M i)
          exact mem_cls.mpr ⟨hij, mem_reach.mp this⟩
        have := Finset.card_lt_card hss
        exact ih j (by omega)) (self_mem_cls M i)
    simpa only [Rs] using hstep

/-- **Theorem 6.2 (discount bound).**  Let `M` be a nonnegative `n × n` matrix every row of
which has a positive entry, with positive entries in `[m_min, m_max]`, let `Ω` satisfy
Equation (6.1), let `v` be the fixed point of `Ψ_M(t) = γ ln(M e^t)`, `γ = 1 - θ`, `θ = 1/N`.
If `N ≥ 2n` then, for every `i`, `|θ v_i - λ_i| ≤ θ R` with `R = 3n(2 ln N + 4nΩ + 2)`. -/
theorem theorem_6_2 (hM : MatHyp M mmin mmax Ω) (hN : 2 ≤ N) (hNn : 2 * Fintype.card ι ≤ N)
    (hv : Psi (1 - 1 / (N : ℝ)) M v = v) (i : ι) :
    |1 / (N : ℝ) * v i - lam M i|
      ≤ 1 / (N : ℝ) * (3 * Fintype.card ι * (2 * Real.log N + 4 * Fintype.card ι * Ω + 2)) := by
  haveI : Nonempty ι := ⟨i⟩
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨_, _, hΩ0, _⟩ := hM.exp_bounds
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set nn : ℝ := (Fintype.card ι : ℝ) with hnn
  set θ : ℝ := 1 / (N : ℝ) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set O : ℝ := 2 * (nn - 1) * Ω with hOdef
  have hO0 : 0 ≤ O := by rw [hOdef]; exact mul_nonneg (by linarith) hΩ0
  have hnnΩ : 0 ≤ nn * Ω := mul_nonneg (by linarith) hΩ0
  have hnn2Ω : 0 ≤ nn * (nn * Ω) := mul_nonneg (by linarith) hnnΩ
  have hnnL : 0 ≤ nn * L := mul_nonneg (by linarith) hL0
  rw [abs_le]
  constructor
  · -- lower bound
    have h1 : lam M i ≤ θ * v i + θ * (5 * nn ^ 2 * Ω) :=
      lam_le hM fun C ρ U hC hacc hU => by
        have : Real.log ρ - θ * (5 * nn ^ 2 * Ω) ≤ θ * v i := lower_bound hM hN hv hC hU hacc
        linarith
    have h2 : 5 * nn ^ 2 * Ω ≤ 3 * nn * (2 * L + 4 * nn * Ω + 2) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hθpos.le
    linarith
  · -- upper bound
    have h1 : θ * v i ≤ lam M i + θ * Rs θ Ω L O (Fintype.card ι) :=
      upper_all hM hN hv (Fintype.card ι) i (Finset.card_le_univ _)
    have h2 : Rs θ Ω L O (Fintype.card ι)
        ≤ nn * (1 + 2 * θ) ^ (Fintype.card ι) * (2 * (Ω + L + 1) + Ω + O) :=
      Rs_le hθpos.le hθ1 hΩ0 hL0 hO0 (Fintype.card ι)
    -- (1 + 2θ)^n ≤ e ≤ 3
    have hpow : (1 + 2 * θ) ^ (Fintype.card ι) ≤ 3 := by
      have ha : 1 + 2 * θ ≤ Real.exp (2 * θ) := by linarith [Real.add_one_le_exp (2 * θ)]
      have h3 : (1 + 2 * θ) ^ (Fintype.card ι) ≤ Real.exp (2 * θ) ^ (Fintype.card ι) :=
        pow_le_pow_left₀ (by linarith) ha _
      rw [← Real.exp_nat_mul] at h3
      have h4 : (Fintype.card ι : ℝ) * (2 * θ) ≤ 1 := by
        have : (2 : ℝ) * Fintype.card ι ≤ N := by exact_mod_cast hNn
        have e : (Fintype.card ι : ℝ) * (2 * θ) = (2 * Fintype.card ι) / N := by rw [hθ]; ring
        rw [e, div_le_one hNpos]
        exact this
      have h5 := Real.exp_le_exp.mpr h4
      have := Real.exp_one_lt_d9
      linarith
    set Q : ℝ := 2 * (Ω + L + 1) + Ω + O with hQ
    have hQ0 : 0 ≤ Q := by rw [hQ]; linarith
    have h3 : nn * (1 + 2 * θ) ^ (Fintype.card ι) * Q ≤ nn * 3 * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) hQ0
    have h4 : nn * 3 * Q ≤ 3 * nn * (2 * L + 4 * nn * Ω + 2) := by
      rw [hQ, hOdef]; nlinarith
    have h5 := mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4)) hθpos.le
    linarith

end upper

end EntropyGames
