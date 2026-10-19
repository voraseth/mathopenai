/-
Section 6 of the paper: Lemma 6.1(d), `lim_k (1/k) ln (M^k 𝟙)_i = λ_i`.

Lower bound as in the paper (a path into a class, then the eigenvector of the class).
Upper bound: the paper builds one vector `u` with `M u ≤ e^{λ+ε} u`, class by class.  Here the
same estimate is run as an induction on the number of states accessible from `i` (as in the
proof of Theorem 6.2): `(M^k 𝟙)_a ≤ κ U_a e^{k(λ_i+ε)}` on the class of `i`, the constant `κ`
being chosen as in the paper from the bounds for the states below the class.
-/
import EntropyGames.Lam

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Classical

variable {ι : Type*} [Fintype ι]

/-- `(M^k 𝟙)_i`, by recursion on `k`. -/
noncomputable def pw (M : ι → ι → ℝ) : ℕ → ι → ℝ
  | 0, _ => 1
  | k + 1, i => ∑ j, M i j * pw M k j

theorem pw_eq [DecidableEq ι] (M : ι → ι → ℝ) (k : ℕ) (i : ι) :
    pw M k i = ((Matrix.of M) ^ k).mulVec (fun _ => 1) i := by
  induction k generalizing i with
  | zero => simp [pw, Matrix.mulVec, dotProduct, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [pw, ih]
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.of_apply]

section

variable {M : ι → ι → ℝ}

theorem pw_pos (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j) :
    ∀ (k : ℕ) (i : ι), 0 < pw M k i
  | 0, _ => one_pos
  | k + 1, i => by
    obtain ⟨j, hj⟩ := hrow i
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j) (pw_pos hM hrow k j).le)
      ⟨j, Finset.mem_univ _, mul_pos hj (pw_pos hM hrow k j)⟩

/-- Lower bound on a class: `(M^k 𝟙)_j ≥ ρ^k U_j / B` if `U ≤ B` on `C`. -/
theorem pw_ge_class (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j) {C : Finset ι}
    {ρ : ℝ} {U : ι → ℝ} (hU : IsPerronPair M C ρ U) {B : ℝ} (hB : ∀ j ∈ C, U j ≤ B) :
    ∀ (k : ℕ), ∀ j ∈ C, ρ ^ k * U j / B ≤ pw M k j := by
  obtain ⟨hρ, hU1, ⟨k0, hk0C, hk0⟩, hMU⟩ := hU
  have hBpos : 0 < B := lt_of_lt_of_le one_pos ((hU1 k0 hk0C).trans (hB k0 hk0C))
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [pow_zero, one_mul, pw]
    rw [div_le_one hBpos]
    exact hB j hj
  | succ k ih =>
    intro j hj
    have h1 : ∑ j' ∈ C, M j j' * (ρ ^ k * U j' / B) ≤ pw M (k + 1) j := by
      simp only [pw]
      refine le_trans (Finset.sum_le_sum fun j' hj' =>
        mul_le_mul_of_nonneg_left (ih j' hj') (hM j j')) ?_
      exact Finset.sum_le_univ_sum_of_nonneg
        (fun j' => mul_nonneg (hM j j') (pw_pos hM hrow k j').le)
    refine le_trans (le_of_eq ?_) h1
    have h2 : ∑ j' ∈ C, M j j' * (ρ ^ k * U j' / B) = ρ ^ k / B * ∑ j' ∈ C, M j j' * U j' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [h2, hMU j hj]
    ring

/-- Along a path the payments are comparable up to a shift of the horizon. -/
theorem pw_acc (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j) {i j : ι}
    (h : Acc M i j) : ∃ (l : ℕ) (c : ℝ), 0 < c ∧ ∀ k, c * pw M k j ≤ pw M (k + l) i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, 1, one_pos, fun k => by simp⟩
  | @head a b hab _ ih =>
    obtain ⟨l, c, hc, hl⟩ := ih
    refine ⟨l + 1, M a b * c, mul_pos hab hc, fun k => ?_⟩
    have h1 : M a b * pw M (k + l) b ≤ pw M (k + (l + 1)) a := by
      rw [← add_assoc]
      simp only [pw]
      exact Finset.single_le_sum (f := fun x => M a x * pw M (k + l) x)
        (fun x _ => mul_nonneg (hM a x) (pw_pos hM hrow _ x).le) (Finset.mem_univ b)
    refine le_trans ?_ h1
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hl k) (hM a b)

/-- Lemma 6.1(d), lower bound, for one class accessible from `i`. -/
theorem pw_lower (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j) {C : Finset ι}
    {ρ : ℝ} {U : ι → ℝ} (hU : IsPerronPair M C ρ U) {i : ι} (hacc : ∃ j ∈ C, Acc M i j) :
    ∃ (l : ℕ) (c : ℝ), 0 < c ∧ ∀ k, c * ρ ^ k ≤ pw M (k + l) i := by
  obtain ⟨j, hjC, hij⟩ := hacc
  obtain ⟨l, c, hc, hl⟩ := pw_acc hM hrow hij
  have hne : C.Nonempty := ⟨j, hjC⟩
  obtain ⟨b, hbC, hb⟩ := Finset.exists_max_image C U hne
  have hU1 := hU.2.1
  have hρ := hU.1
  have hBpos : 0 < U b := lt_of_lt_of_le one_pos (hU1 b hbC)
  refine ⟨l, c / U b, div_pos hc hBpos, fun k => ?_⟩
  refine le_trans ?_ (hl k)
  have h1 := pw_ge_class hM hrow hU hb k j hjC
  have h2 : ρ ^ k / U b ≤ ρ ^ k * U j / U b := by
    apply div_le_div_of_nonneg_right _ hBpos.le
    exact le_mul_of_one_le_right (pow_pos hρ k).le (hU1 j hjC)
  calc c / U b * ρ ^ k = c * (ρ ^ k / U b) := by ring
    _ ≤ c * pw M k j := mul_le_mul_of_nonneg_left (h2.trans h1) hc.le

end

section upper

variable {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}

/-- A state below the class of `i` has fewer accessible states. -/
theorem reach_card_lt {i a j : ι} (ha : a ∈ cls M i) (hj : j ∉ cls M i) (haj : 0 < M a j) :
    (reach M j).card < (reach M i).card := by
  rw [mem_cls] at ha
  have hij : Acc M i j := ha.1.trans (Acc.of_arc haj)
  refine Finset.card_lt_card ⟨reach_subset hij, fun hsub => ?_⟩
  have : i ∈ reach M j := hsub (self_mem_reach M i)
  exact hj (mem_cls.mpr ⟨hij, mem_reach.mp this⟩)

/-- Lemma 6.1(d), upper bound: `(M^k 𝟙)_i ≤ K e^{k(λ_i+ε)}`. -/
theorem pw_upper (hM : MatHyp M mmin mmax Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ (n : ℕ) (i : ι), (reach M i).card ≤ n →
      ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, pw M k i ≤ K * Real.exp (lam M i + ε) ^ k := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have : 0 < (reach M i).card := Finset.card_pos.mpr ⟨i, self_mem_reach M i⟩
    omega
  | succ n ih =>
    intro i hi
    have hpos := pw_pos hM.nonneg hM.row
    obtain ⟨lmb, hlmb⟩ : ∃ x, x = lam M i := ⟨_, rfl⟩
    obtain ⟨E, hE⟩ : ∃ x, x = Real.exp (lmb + ε) := ⟨_, rfl⟩
    have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
    -- bounds for the states below the class
    let Kf : ι → ℝ := fun j =>
      if h : (reach M j).card ≤ n then Classical.choose (ih j h) else 1
    have hKf0 : ∀ j, 0 < Kf j := by
      intro j
      simp only [Kf]
      split_ifs with h
      · exact (Classical.choose_spec (ih j h)).1
      · exact one_pos
    have hbelow : ∀ a ∈ cls M i, ∀ j, j ∉ cls M i → ∀ k : ℕ,
        M a j * pw M k j ≤ M a j * Kf j * E ^ k := by
      intro a ha j hj k
      rcases (hM.nonneg a j).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · have hcard : (reach M j).card ≤ n := by
          have := reach_card_lt ha hj h0
          omega
        have h1 := (Classical.choose_spec (ih j hcard)).2 k
        have h2 : Kf j = Classical.choose (ih j hcard) := by
          simp only [Kf, dif_pos hcard]
        have hlam : lam M j ≤ lmb := by
          rw [hlmb]
          exact lam_mono_acc hM ((mem_cls.mp ha).1.trans (Acc.of_arc h0))
        have h3 : Real.exp (lam M j + ε) ^ k ≤ E ^ k := by
          rw [hE]
          exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) k
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ h0.le
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_left h3 (Classical.choose_spec (ih j hcard)).1.le)
    obtain ⟨S, hS⟩ : ∃ x, x = ∑ a, ∑ j, M a j * Kf j := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hM.nonneg a j) (hKf0 j).le
    have hout : ∀ a ∈ cls M i, ∀ k : ℕ,
        ∑ j ∈ (cls M i)ᶜ, M a j * pw M k j ≤ S * E ^ k := by
      intro a ha k
      have h1 : ∑ j ∈ (cls M i)ᶜ, M a j * pw M k j
          ≤ ∑ j ∈ (cls M i)ᶜ, M a j * Kf j * E ^ k :=
        Finset.sum_le_sum fun j hj => hbelow a ha j (Finset.mem_compl.mp hj) k
      have h2 : ∑ j ∈ (cls M i)ᶜ, M a j * Kf j ≤ S := by
        rw [hS]
        refine le_trans (Finset.sum_le_univ_sum_of_nonneg
          (fun j => mul_nonneg (hM.nonneg a j) (hKf0 j).le)) ?_
        exact Finset.single_le_sum (f := fun a => ∑ j, M a j * Kf j)
          (fun a _ => Finset.sum_nonneg fun j _ => mul_nonneg (hM.nonneg a j) (hKf0 j).le)
          (Finset.mem_univ a)
      rw [← Finset.sum_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (pow_pos hEpos k).le)
    -- the eigenvector of the class, or `ρ = 0`, `U = 𝟙` for a trivial class
    obtain ⟨ρ, U, hρ0, hρle, hU1, hMU⟩ : ∃ (ρ : ℝ) (U : ι → ℝ), 0 ≤ ρ ∧ ρ ≤ Real.exp lmb ∧
        (∀ a ∈ cls M i, 1 ≤ U a) ∧ ∀ a ∈ cls M i, ∑ j ∈ cls M i, M a j * U j = ρ * U a := by
      by_cases hC : IsNontrivialClass M (cls M i)
      · obtain ⟨ρ, U, hU⟩ := perron_frobenius hM.nonneg hC
        refine ⟨ρ, U, hU.1.le, ?_, hU.2.1, hU.2.2.2⟩
        have := log_le_lam hM hC ⟨i, self_mem_cls M i, Relation.ReflTransGen.refl⟩ hU
        rw [← hlmb] at this
        exact (Real.log_le_iff_le_exp hU.1).mp this
      · refine ⟨0, fun _ => 1, le_rfl, (Real.exp_pos _).le, fun _ _ => le_rfl, fun a ha => ?_⟩
        rw [zero_mul]
        refine Finset.sum_eq_zero fun j hj => ?_
        have : ¬ 0 < M a j := fun h => hC ⟨isClass_cls M i, a, ha, j, hj, h⟩
        rw [le_antisymm (not_lt.mp this) (hM.nonneg a j), zero_mul]
    obtain ⟨dl, hdl⟩ : ∃ x, x = Real.exp lmb * (Real.exp ε - 1) := ⟨_, rfl⟩
    have hdlpos : 0 < dl := by
      rw [hdl]
      have : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
      exact mul_pos (Real.exp_pos _) (by linarith)
    have hEeq : E = Real.exp lmb + dl := by
      rw [hE, hdl, Real.exp_add]; ring
    obtain ⟨κ, hκ⟩ : ∃ x, x = 1 + S / dl := ⟨_, rfl⟩
    have hκ1 : 1 ≤ κ := by
      rw [hκ]
      have : 0 ≤ S / dl := div_nonneg hS0 hdlpos.le
      linarith
    have hκS : S ≤ κ * dl := by
      rw [hκ, add_mul, div_mul_cancel₀ _ hdlpos.ne']
      linarith
    have key : ∀ (k : ℕ), ∀ a ∈ cls M i, pw M k a ≤ κ * U a * E ^ k := by
      intro k
      induction k with
      | zero =>
        intro a ha
        simp only [pw, pow_zero, mul_one]
        have := hU1 a ha
        nlinarith
      | succ k ihk =>
        intro a ha
        have hP : 0 < E ^ k := pow_pos hEpos k
        have hUa := hU1 a ha
        have h1 : pw M (k + 1) a
            = ∑ j ∈ cls M i, M a j * pw M k j + ∑ j ∈ (cls M i)ᶜ, M a j * pw M k j := by
          simp only [pw]
          rw [Finset.sum_add_sum_compl]
        have h2 : ∑ j ∈ cls M i, M a j * pw M k j ≤ κ * E ^ k * (ρ * U a) := by
          rw [← hMU a ha, Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have := mul_le_mul_of_nonneg_left (ihk j hj) (hM.nonneg a j)
          linarith only [this]
        have h3 := hout a ha k
        have h4 : κ * E ^ k * (ρ * U a) ≤ κ * E ^ k * (Real.exp lmb * U a) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hρle (by linarith)
        have h5 : S * E ^ k ≤ κ * dl * U a * E ^ k := by
          apply mul_le_mul_of_nonneg_right _ hP.le
          have : κ * dl ≤ κ * dl * U a := le_mul_of_one_le_right (by positivity) hUa
          linarith
        rw [h1, pow_succ, hEeq]
        rw [hEeq] at h2 h3 h4 h5
        linarith only [h2, h3, h4, h5]
    have hUi := hU1 i (self_mem_cls M i)
    refine ⟨κ * U i, by positivity, fun k => ?_⟩
    have := key k i (self_mem_cls M i)
    rw [← hlmb, ← hE]
    exact this

end upper

/-- **Lemma 6.1(d)**: `lim_{k→∞} (1/k) ln (M^k 𝟙)_i = λ_i` for every `i`. -/
theorem lemma_6_1_d [DecidableEq ι] {M : ι → ι → ℝ} {mmin mmax Ω : ℝ}
    (hM : MatHyp M mmin mmax Ω) (i : ι) :
    Filter.Tendsto
      (fun k : ℕ => 1 / (k : ℝ) * Real.log (((Matrix.of M) ^ k).mulVec (fun _ => 1) i))
      Filter.atTop (nhds (lam M i)) := by
  simp only [← pw_eq]
  have hpos := pw_pos hM.nonneg hM.row
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- upper bound
  obtain ⟨K, hK, hup⟩ := pw_upper hM (half_pos hε) _ i le_rfl
  -- lower bound
  obtain ⟨x, ⟨C, ρ, U, hC, hacc, hU, rfl⟩, hx⟩ :=
    exists_lt_of_lt_csSup (lamSet_nonempty hM i)
      (show lam M i - ε / 2 < sSup (lamSet M i) by rw [← lam_eq_sSup]; linarith)
  obtain ⟨l, c, hc, hlow⟩ := pw_lower hM.nonneg hM.row hU hacc
  have hρ := hU.1
  obtain ⟨lmb, hlmb⟩ : ∃ x, x = lam M i := ⟨_, rfl⟩
  obtain ⟨lr, hlr⟩ : ∃ x, x = Real.log ρ := ⟨_, rfl⟩
  obtain ⟨lK, hlK⟩ : ∃ x, x = Real.log K := ⟨_, rfl⟩
  obtain ⟨lc, hlc⟩ : ∃ x, x = Real.log c := ⟨_, rfl⟩
  rw [← hlmb] at hup hx ⊢
  rw [← hlr] at hx
  obtain ⟨N1, hN1⟩ := exists_nat_gt (2 * (|lK| + |lc - l * lr|) / ε)
  refine ⟨max (l + 1) N1, fun m hm => ?_⟩
  have hml : l + 1 ≤ m := (le_max_left _ _).trans hm
  have hmN : (N1 : ℝ) ≤ m := by exact_mod_cast (le_max_right _ _).trans hm
  have hm0 : (0 : ℝ) < m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have hbig : 2 * (|lK| + |lc - l * lr|) < m * ε := by
    have := lt_of_lt_of_le hN1 hmN
    rwa [div_lt_iff₀ hε] at this
  -- upper estimate of the logarithm
  have h1 : Real.log (pw M m i) ≤ lK + m * (lmb + ε / 2) := by
    have := Real.log_le_log (hpos m i) (hup m)
    rw [Real.log_mul hK.ne' (pow_pos (Real.exp_pos _) m).ne', Real.log_pow, Real.log_exp,
      ← hlK] at this
    exact this
  -- lower estimate
  have h2 : lc + (m - l) * lr ≤ Real.log (pw M m i) := by
    have h := hlow (m - l)
    rw [Nat.sub_add_cancel (by omega)] at h
    have := Real.log_le_log (mul_pos hc (pow_pos hρ _)) h
    rw [Real.log_mul hc.ne' (pow_pos hρ _).ne', Real.log_pow, ← hlc, ← hlr,
      Nat.cast_sub (by omega)] at this
    exact this
  have ha1 := le_abs_self lK
  have ha2 := neg_abs_le (lc - l * lr)
  have ha3 := abs_nonneg lK
  have ha4 := abs_nonneg (lc - l * lr)
  rw [Real.dist_eq, abs_lt]
  have e : 1 / (m : ℝ) * Real.log (pw M m i) - lmb
      = (Real.log (pw M m i) - m * lmb) / m := by
    field_simp
  rw [e, lt_div_iff₀ hm0, div_lt_iff₀ hm0]
  constructor
  · nlinarith only [h2, ha2, ha3, hbig, hx, hm0]
  · linarith only [h1, ha1, ha4, hbig]

end EntropyGames
