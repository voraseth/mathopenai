/-
Section 6 of the paper, irreducible part: the map `Ψ_M(t) = γ ln(M e^t)`, Lemma 6.1(a),(b) for
a matrix with a positive eigenvector, and the discount bound in the case of a single class
(the "height 0" case of Theorem 6.2 together with the first step of its lower bound).

The Perron–Frobenius theorem (existence of the positive eigenvector of an irreducible
nonnegative matrix) is not in Mathlib; here the eigenvector is a hypothesis.
-/
import EntropyGames.Contraction

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

variable {ι : Type*} [Fintype ι]

/-- `Ψ_M(t) = γ ln(M e^t)`. -/
noncomputable def Psi (γ : ℝ) (M : ι → ι → ℝ) (t : ι → ℝ) (i : ι) : ℝ :=
  γ * Real.log (∑ j, M i j * Real.exp (t j))

theorem Psi_sum_pos {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j)
    (t : ι → ℝ) (i : ι) : 0 < ∑ j, M i j * Real.exp (t j) := by
  obtain ⟨j0, hj0⟩ := hrow i
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j) (Real.exp_pos _).le)
    ⟨j0, Finset.mem_univ _, mul_pos hj0 (Real.exp_pos _)⟩

/-- `Ψ_M` satisfies Equation (4.1) (stated in the paper before Theorem 6.2). -/
theorem Psi_isDiscounted {γ : ℝ} (hγ : 0 ≤ γ) {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∃ j, 0 < M i j) : IsDiscounted γ (Psi γ M) := by
  constructor
  · intro t t' htt i
    unfold Psi
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (Psi_sum_pos hM hrow t i) ?_) hγ
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (htt j)) (hM i j)
  · intro t c
    funext i
    unfold Psi
    have h1 : ∑ j, M i j * Real.exp (t j + c) = Real.exp c * ∑ j, M i j * Real.exp (t j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Real.exp_add]; ring
    rw [h1, Real.log_mul (Real.exp_pos c).ne' (Psi_sum_pos hM hrow t i).ne', Real.log_exp]
    ring

/-- The value of `Ψ_M` at `c + ln U` for an eigenvector `U`. -/
theorem Psi_eigen {γ : ℝ} {M : ι → ι → ℝ} {U : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : ∀ i, 0 < U i) (hMU : ∀ i, ∑ j, M i j * U j = ρ * U i) (c : ℝ) (i : ι) :
    Psi γ M (fun j => c + Real.log (U j)) i = γ * (Real.log ρ + c + Real.log (U i)) := by
  unfold Psi
  have h1 : ∑ j, M i j * Real.exp (c + Real.log (U j)) = Real.exp c * (ρ * U i) := by
    rw [← hMU i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.exp_add, Real.exp_log (hU j)]; ring
  rw [h1, Real.log_mul (Real.exp_pos c).ne' (mul_pos hρ (hU i)).ne', Real.log_exp,
    Real.log_mul hρ.ne' (hU i).ne']
  ring

/-- Rows are nonzero when there is a positive eigenvector with positive eigenvalue. -/
theorem row_pos_of_eigen {M : ι → ι → ℝ} {U : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : ∀ i, 0 < U i) (hM : ∀ i j, 0 ≤ M i j) (hMU : ∀ i, ∑ j, M i j * U j = ρ * U i)
    (i : ι) : ∃ j, 0 < M i j := by
  by_contra hcon
  push Not at hcon
  have : ∑ j, M i j * U j = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [le_antisymm (hcon j) (hM i j), zero_mul]
  have := hMU i
  have := mul_pos hρ (hU i)
  linarith

/-- **Discount bound, one class** (the height-0 case of Theorem 6.2 and the first display of
its lower bound).  `M ≥ 0` has an eigenvector `U ≥ 1` with eigenvalue `ρ > 0` and
`ln U ≤ O`; `v` is the fixed point of `Ψ_M` for `γ = 1 - 1/N`.  Then
`γ ln ρ - θ O ≤ θ v_i ≤ γ ln ρ + θ O`, `θ = 1/N`. -/
theorem discount_one_class {N : ℕ} (hN : 2 ≤ N) {M : ι → ι → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {U : ι → ℝ} {ρ O : ℝ} (hρ : 0 < ρ) (hU : ∀ i, 1 ≤ U i)
    (hMU : ∀ i, ∑ j, M i j * U j = ρ * U i) (hO : ∀ i, Real.log (U i) ≤ O)
    {v : ι → ℝ} (hv : Psi (1 - 1 / (N : ℝ)) M v = v) (i : ι) :
    (1 - 1 / (N : ℝ)) * Real.log ρ - 1 / (N : ℝ) * O ≤ 1 / (N : ℝ) * v i ∧
      1 / (N : ℝ) * v i ≤ (1 - 1 / (N : ℝ)) * Real.log ρ + 1 / (N : ℝ) * O := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set θ : ℝ := 1 / (N : ℝ) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hUpos : ∀ i, 0 < U i := fun i => lt_of_lt_of_le one_pos (hU i)
  have hlogU : ∀ i, 0 ≤ Real.log (U i) := fun i => Real.log_nonneg (hU i)
  have hrow := row_pos_of_eigen hρ hUpos hM hMU
  have hdisc : IsDiscounted (1 - θ) (Psi (1 - θ) M) := Psi_isDiscounted (by linarith) hM hrow
  have hsub := hdisc.isSubDiscounted
  set lam := Real.log ρ with hlam
  constructor
  · -- subsolution w = c + ln U with θ c = γ λ - θ O
    set c := ((1 - θ) * lam - θ * O) / θ with hc
    have hθc : θ * c = (1 - θ) * lam - θ * O := by rw [hc]; field_simp
    have hw : (fun j => c + Real.log (U j)) ≤ Psi (1 - θ) M (fun j => c + Real.log (U j)) := by
      intro j
      rw [Psi_eigen hρ hUpos hMU]
      have h1 : θ * Real.log (U j) ≤ θ * O := mul_le_mul_of_nonneg_left (hO j) hθpos.le
      simp only
      nlinarith
    have := hsub.le_fixed (by linarith) hv hw i
    simp only at this
    have h2 : θ * (c + Real.log (U i)) ≤ θ * v i := mul_le_mul_of_nonneg_left this hθpos.le
    have h3 : 0 ≤ θ * Real.log (U i) := mul_nonneg hθpos.le (hlogU i)
    nlinarith
  · -- supersolution w = c + ln U with θ c = γ λ
    set c := ((1 - θ) * lam) / θ with hc
    have hθc : θ * c = (1 - θ) * lam := by rw [hc]; field_simp
    have hw : Psi (1 - θ) M (fun j => c + Real.log (U j)) ≤ (fun j => c + Real.log (U j)) := by
      intro j
      rw [Psi_eigen hρ hUpos hMU]
      have h1 : 0 ≤ θ * Real.log (U j) := mul_nonneg hθpos.le (hlogU j)
      simp only
      nlinarith
    have := hsub.fixed_le (by linarith) hv hw i
    simp only at this
    have h2 : θ * v i ≤ θ * (c + Real.log (U i)) := mul_le_mul_of_nonneg_left this hθpos.le
    have h3 : θ * Real.log (U i) ≤ θ * O := mul_le_mul_of_nonneg_left (hO i) hθpos.le
    nlinarith

/-- Lemma 6.1(a) for a matrix with a positive eigenvector: `m_min ≤ ρ ≤ n m_max`. -/
theorem perron_root_bounds [Nonempty ι] {M : ι → ι → ℝ} {U : ι → ℝ} {ρ mmin mmax : ℝ}
    (hU : ∀ i, 0 < U i) (hMU : ∀ i, ∑ j, M i j * U j = ρ * U i)
    (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j)
    (hmin : ∀ i j, 0 < M i j → mmin ≤ M i j) (hmax : ∀ i j, M i j ≤ mmax) :
    mmin ≤ ρ ∧ ρ ≤ Fintype.card ι * mmax := by
  constructor
  · obtain ⟨i0, hi0⟩ := Finite.exists_min U
    obtain ⟨j0, hj0⟩ := hrow i0
    have h1 : mmin * U i0 ≤ ρ * U i0 := by
      rw [← hMU i0]
      calc mmin * U i0 ≤ M i0 j0 * U j0 :=
            mul_le_mul (hmin i0 j0 hj0) (hi0 j0) (hU i0).le hj0.le
        _ ≤ ∑ j, M i0 j * U j := Finset.single_le_sum (f := fun j => M i0 j * U j)
            (fun j _ => mul_nonneg (hM i0 j) (hU j).le) (Finset.mem_univ j0)
    exact le_of_mul_le_mul_right h1 (hU i0)
  · obtain ⟨i0, hi0⟩ := Finite.exists_max U
    have hmax0 : 0 ≤ mmax := (hM i0 i0).trans (hmax i0 i0)
    have h1 : ρ * U i0 ≤ (Fintype.card ι * mmax) * U i0 := by
      rw [← hMU i0]
      calc ∑ j, M i0 j * U j ≤ ∑ _j : ι, mmax * U i0 :=
            Finset.sum_le_sum fun j _ => mul_le_mul (hmax i0 j) (hi0 j) (hU j).le hmax0
        _ = (Fintype.card ι * mmax) * U i0 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    exact le_of_mul_le_mul_right h1 (hU i0)

/-- The combinatorial core of Lemma 6.1(b): if every proper nonempty set of states has an
outgoing arc (irreducibility) and `U_j ≤ c U_i` along every arc `i → j`, then
`max U ≤ c^{n-1} min U`. -/
theorem le_pow_mul_of_arcs {M : ι → ι → ℝ} {U : ι → ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < M i j)
    (harc : ∀ i j, 0 < M i j → U j ≤ c * U i) {i0 : ι} (hi0pos : 0 ≤ U i0) (j : ι) :
    U j ≤ c ^ (Fintype.card ι - 1) * U i0 := by
  classical
  have hc0 : 0 ≤ c := by linarith
  let S : ℕ → Finset ι := fun k => Finset.univ.filter fun j => U j ≤ c ^ k * U i0
  have hmono : ∀ k, S k ⊆ S (k + 1) := by
    intro k x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have : c ^ k * U i0 ≤ c ^ (k + 1) * U i0 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (Nat.le_succ k)) hi0pos
    linarith
  have hclaim : ∀ k, S k = Finset.univ ∨ k + 1 ≤ (S k).card := by
    intro k
    induction k with
    | zero =>
      right
      have : i0 ∈ S 0 := by simp [S]
      exact Finset.card_pos.mpr ⟨i0, this⟩
    | succ k ih =>
      rcases ih with ih | ih
      · left
        exact Finset.eq_univ_of_forall fun x => hmono k (ih ▸ Finset.mem_univ x)
      · by_cases huniv : S k = Finset.univ
        · left
          exact Finset.eq_univ_of_forall fun x => hmono k (huniv ▸ Finset.mem_univ x)
        · right
          obtain ⟨i, hi, j', hj', hpos⟩ := hcut (S k) (Finset.card_pos.mp (by omega)) huniv
          have hj1 : j' ∈ S (k + 1) := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            calc U j' ≤ c * U i := harc i j' hpos
              _ ≤ c * (c ^ k * U i0) := mul_le_mul_of_nonneg_left hi hc0
              _ = c ^ (k + 1) * U i0 := by ring
          have hss : S k ⊂ S (k + 1) :=
            ⟨hmono k, fun hsub => hj' (hsub hj1)⟩
          have := Finset.card_lt_card hss
          omega
  have hall : S (Fintype.card ι - 1) = Finset.univ := by
    rcases hclaim (Fintype.card ι - 1) with h | h
    · exact h
    · apply Finset.eq_univ_of_card
      have h1 := Finset.card_le_univ (S (Fintype.card ι - 1))
      have h2 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
      omega
  have : j ∈ S (Fintype.card ι - 1) := hall ▸ Finset.mem_univ j
  simpa [S] using this

/-- **Discount bound for irreducible matrices** (Theorem 6.2 for a matrix with a single class).
`M ≥ 0` is irreducible in the sense that every proper nonempty set of states has an outgoing
arc, its positive entries lie in `[m_min, m_max]`, `Ω` satisfies Equation (6.1), and `U` is a
positive eigenvector with eigenvalue `ρ > 0` (it exists by the Perron–Frobenius theorem, which
is a hypothesis here).  Then `|θ v_i - ln ρ| ≤ θ (2n - 1) Ω` for the fixed point `v` of
`Ψ_M`, `γ = 1 - 1/N`, `θ = 1/N`, `N ≥ 2`.  Since `(2n-1) Ω = Ω + O_n = R_0 ≤ R`, this is the
bound of Theorem 6.2 for such `M`. -/
theorem discount_irreducible [Nonempty ι] {N : ℕ} (hN : 2 ≤ N) {M : ι → ι → ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {mmin mmax Ω : ℝ} (hmin0 : 0 < mmin)
    (hmin : ∀ i j, 0 < M i j → mmin ≤ M i j) (hmax : ∀ i j, M i j ≤ mmax)
    (hΩ : Real.log (Fintype.card ι * max mmax (max (1 / mmin) 1)) ≤ Ω)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < M i j)
    {U : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : ∀ i, 0 < U i)
    (hMU : ∀ i, ∑ j, M i j * U j = ρ * U i)
    {v : ι → ℝ} (hv : Psi (1 - 1 / (N : ℝ)) M v = v) (i : ι) :
    |1 / (N : ℝ) * v i - Real.log ρ| ≤ 1 / (N : ℝ) * ((2 * Fintype.card ι - 1) * Ω) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hrow := row_pos_of_eigen hρ hU hM hMU
  obtain ⟨hρlo, hρhi⟩ := perron_root_bounds hU hMU hM hrow hmin hmax
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmaxpos : 0 < mmax := by
    obtain ⟨j, hj⟩ := hrow i
    exact hj.trans_le (hmax i j)
  -- consequences of (6.1)
  have hexpΩ : Fintype.card ι * max mmax (max (1 / mmin) 1) ≤ Real.exp Ω :=
    (Real.log_le_iff_le_exp (by positivity)).mp hΩ
  have hA1 : Fintype.card ι * mmax ≤ Real.exp Ω := by
    refine le_trans ?_ hexpΩ
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  have hA2 : 1 / mmin ≤ Real.exp Ω := by
    refine le_trans ?_ hexpΩ
    calc 1 / mmin ≤ max mmax (max (1 / mmin) 1) := (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ Fintype.card ι * max mmax (max (1 / mmin) 1) :=
        le_mul_of_one_le_left (by positivity) hn
  have hA3 : (1 : ℝ) ≤ Real.exp Ω := by
    refine le_trans ?_ hexpΩ
    calc (1 : ℝ) ≤ max mmax (max (1 / mmin) 1) := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ Fintype.card ι * max mmax (max (1 / mmin) 1) :=
        le_mul_of_one_le_left (by positivity) hn
  have hΩ0 : 0 ≤ Ω := by
    rw [← Real.exp_le_exp, Real.exp_zero]; exact hA3
  -- |ln ρ| ≤ Ω
  have hlog_hi : Real.log ρ ≤ Ω := (Real.log_le_iff_le_exp hρ).mpr (hρhi.trans hA1)
  have hlog_lo : -Ω ≤ Real.log ρ := by
    rw [Real.le_log_iff_exp_le hρ, Real.exp_neg]
    refine le_trans ?_ hρlo
    rw [inv_le_comm₀ (Real.exp_pos _) hmin0, ← one_div]
    exact hA2
  -- arcs: U_j ≤ (ρ / mmin) U_i, and ρ / mmin ≤ e^{2Ω}
  set c := Real.exp (2 * Ω) with hc
  have hρm : ρ / mmin ≤ c := by
    rw [hc, two_mul, Real.exp_add, div_eq_mul_one_div]
    exact mul_le_mul (hρhi.trans hA1) hA2 (by positivity) (Real.exp_pos _).le
  have hc1 : 1 ≤ c := by
    rw [hc, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have harc : ∀ i j, 0 < M i j → U j ≤ c * U i := by
    intro i j hij
    have h1 : M i j * U j ≤ ρ * U i := by
      rw [← hMU i]
      exact Finset.single_le_sum (f := fun j => M i j * U j)
        (fun j _ => mul_nonneg (hM i j) (hU j).le) (Finset.mem_univ j)
    have h2 : mmin * U j ≤ ρ * U i :=
      (mul_le_mul_of_nonneg_right (hmin i j hij) (hU j).le).trans h1
    have h3 : U j ≤ ρ / mmin * U i := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hmin0]; linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hρm (hU i).le)
  -- normalise the eigenvector: U' = U / min U
  obtain ⟨i0, hi0⟩ := Finite.exists_min U
  set U' : ι → ℝ := fun j => U j / U i0 with hU'
  have hU'1 : ∀ j, 1 ≤ U' j := fun j => by
    rw [hU', le_div_iff₀ (hU i0)]; linarith [hi0 j]
  have hMU' : ∀ i, ∑ j, M i j * U' j = ρ * U' i := by
    intro i
    simp only [hU']
    rw [← mul_div_assoc, ← hMU i, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hO : ∀ j, Real.log (U' j) ≤ (Fintype.card ι - 1 : ℕ) * (2 * Ω) := by
    intro j
    have h1 := le_pow_mul_of_arcs hc1 hcut harc (hU i0).le j
    have h2 : U' j ≤ c ^ (Fintype.card ι - 1) := by
      rw [hU', div_le_iff₀ (hU i0)]; exact h1
    have h3 : 0 < U' j := lt_of_lt_of_le one_pos (hU'1 j)
    calc Real.log (U' j) ≤ Real.log (c ^ (Fintype.card ι - 1)) := Real.log_le_log h3 h2
      _ = (Fintype.card ι - 1 : ℕ) * (2 * Ω) := by rw [Real.log_pow, hc, Real.log_exp]
  obtain ⟨hlo, hhi⟩ := discount_one_class hN hM hρ hU'1 hMU' hO hv i
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub (Fintype.card_pos)]; simp
  rw [hcast] at hlo hhi
  have hθpos : 0 < 1 / (N : ℝ) := by positivity
  have h1 : 1 / (N : ℝ) * Real.log ρ ≤ 1 / (N : ℝ) * Ω :=
    mul_le_mul_of_nonneg_left hlog_hi hθpos.le
  have h2 : 1 / (N : ℝ) * (-Ω) ≤ 1 / (N : ℝ) * Real.log ρ :=
    mul_le_mul_of_nonneg_left hlog_lo hθpos.le
  rw [abs_le]
  constructor <;> nlinarith

end EntropyGames
