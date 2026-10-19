/-
The Perron–Frobenius theorem for irreducible nonnegative matrices (existence of a positive
eigenvector with positive eigenvalue), which the paper uses in Section 6, paragraph "Classes".
It is not in Mathlib.  The proof here is the vanishing-discount argument: the fixed points of
`Ψ_M` for `γ = 1 - 1/N` give vectors `W_N ∈ [0,1]^n` with `M W_N = c_N W_N^{1/γ}`; a limit
point as `N → ∞` is an eigenvector, and irreducibility makes it positive.

Irreducibility is the cut condition: every proper nonempty set of states has an outgoing arc.
-/
import EntropyGames.Discount

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The normalised exponential of the discounted fixed point is an approximate eigenvector. -/
theorem exists_approx_eigen [Nonempty ι] {A : ι → ι → ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) {N : ℕ} (hN : 2 ≤ N) :
    ∃ (W : ι → ℝ) (c : ℝ), (∀ i, 0 ≤ W i ∧ W i ≤ 1) ∧ 1 ≤ ∑ i, W i ∧ 0 ≤ c ∧
      c ≤ ∑ i, ∑ j, A i j ∧
      ∀ i, ∑ j, A i j * W j = c * W i ^ (1 / (1 - 1 / (N : ℝ))) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set γ : ℝ := 1 - 1 / (N : ℝ) with hγ
  have hθ : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hθpos : 0 < 1 / (N : ℝ) := by positivity
  have hγ0 : 0 < γ := by linarith
  have hγ1 : γ < 1 := by linarith
  obtain ⟨v, hv, _⟩ := (Psi_isDiscounted hγ0.le hA hrow).existsUnique_fixed hγ0.le hγ1
  set X : ι → ℝ := fun i => Real.exp (v i) with hXdef
  have hXpos : ∀ i, 0 < X i := fun i => Real.exp_pos _
  have hX : ∀ i, ∑ j, A i j * X j = X i ^ (1 / γ) := by
    intro i
    have h1 : γ * Real.log (∑ j, A i j * Real.exp (v j)) = v i := congrFun hv i
    have hS := Psi_sum_pos hA hrow v i
    have h2 : Real.log (∑ j, A i j * Real.exp (v j)) = v i * (1 / γ) := by
      rw [← h1]; field_simp
    simp only [hXdef]
    rw [← Real.exp_mul, ← h2, Real.exp_log hS]
  obtain ⟨i0, hi0⟩ := Finite.exists_max X
  set a : ℝ := 1 / γ with ha
  refine ⟨fun i => X i / X i0, ∑ j, A i0 j * (X j / X i0), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(div_pos (hXpos i) (hXpos i0)).le, (div_le_one (hXpos i0)).mpr (hi0 i)⟩
  · calc (1 : ℝ) = X i0 / X i0 := (div_self (hXpos i0).ne').symm
      _ ≤ ∑ i, X i / X i0 := Finset.single_le_sum (f := fun i => X i / X i0)
          (fun i _ => (div_pos (hXpos i) (hXpos i0)).le) (Finset.mem_univ i0)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i0 j) (div_pos (hXpos j) (hXpos i0)).le
  · calc ∑ j, A i0 j * (X j / X i0) ≤ ∑ j, A i0 j :=
          Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hA i0 j)
            ((div_le_one (hXpos i0)).mpr (hi0 j))
      _ ≤ ∑ i, ∑ j, A i j := Finset.single_le_sum (f := fun i => ∑ j, A i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hA i j) (Finset.mem_univ i0)
  · intro i
    have hsum : ∀ k, ∑ j, A k j * (X j / X i0) = X k ^ a / X i0 := by
      intro k
      rw [← hX k, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum i, hsum i0, Real.div_rpow (hXpos i).le (hXpos i0).le]
    have h0 : 0 < X i0 ^ a := Real.rpow_pos_of_pos (hXpos i0) a
    field_simp

/-- **Perron–Frobenius, existence.**  A nonnegative matrix with nonzero rows in which every
proper nonempty set of states has an outgoing arc has a positive eigenvector with a positive
eigenvalue. -/
theorem perron_frobenius_cut [Nonempty ι] {A : ι → ι → ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < A i j) :
    ∃ (ρ : ℝ) (U : ι → ℝ), 0 < ρ ∧ (∀ i, 0 < U i) ∧ ∀ i, ∑ j, A i j * U j = ρ * U i := by
  classical
  choose W c hW01 hWsum hc0 hcR hEq using
    fun n : ℕ => exists_approx_eigen hA hrow (N := n + 2) (by omega)
  set R : ℝ := ∑ i, ∑ j, A i j with hR
  -- compactness
  let K : Set ((ι → ℝ) × ℝ) := (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) ×ˢ Set.Icc (0 : ℝ) R
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_Icc
  have hmem : ∀ n, (W n, c n) ∈ K := fun n =>
    ⟨fun i _ => ⟨(hW01 n i).1, (hW01 n i).2⟩, ⟨hc0 n, hcR n⟩⟩
  obtain ⟨⟨Winf, cinf⟩, hlimK, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hWlim : Tendsto (fun n => W (φ n)) atTop (𝓝 Winf) :=
    (continuous_fst.tendsto _).comp hlim
  have hclim : Tendsto (fun n => c (φ n)) atTop (𝓝 cinf) :=
    (continuous_snd.tendsto _).comp hlim
  have hWi : ∀ i, Tendsto (fun n => W (φ n) i) atTop (𝓝 (Winf i)) :=
    fun i => tendsto_pi_nhds.mp hWlim i
  -- the exponents tend to 1
  have hexp : Tendsto (fun n : ℕ => 1 / (1 - 1 / (((φ n + 2 : ℕ)) : ℝ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => φ n + 2) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφ.tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => 1 / (((φ n + 2 : ℕ)) : ℝ)) atTop (𝓝 0) := h0.comp h1
    have h3 : Tendsto (fun n : ℕ => 1 - 1 / (((φ n + 2 : ℕ)) : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h2
    have h4 := (tendsto_const_nhds (x := (1 : ℝ))).div h3 (by norm_num)
    simp only [sub_zero, div_one] at h4
    exact h4.congr fun n => rfl
  -- pass to the limit in the approximate eigen-equation
  have hEqlim : ∀ i, ∑ j, A i j * Winf j = cinf * Winf i := by
    intro i
    have hL : Tendsto (fun n => ∑ j, A i j * W (φ n) j) atTop (𝓝 (∑ j, A i j * Winf j)) :=
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hWi j)
    have hRt : Tendsto (fun n => c (φ n) * W (φ n) i ^ (1 / (1 - 1 / (((φ n + 2 : ℕ)) : ℝ))))
        atTop (𝓝 (cinf * Winf i ^ (1 : ℝ))) :=
      hclim.mul ((hWi i).rpow hexp (Or.inr one_pos))
    have hfun : (fun n => ∑ j, A i j * W (φ n) j)
        = fun n => c (φ n) * W (φ n) i ^ (1 / (1 - 1 / (((φ n + 2 : ℕ)) : ℝ))) :=
      funext fun n => hEq (φ n) i
    rw [hfun] at hL
    have := tendsto_nhds_unique hL hRt
    rwa [Real.rpow_one] at this
  have hW0 : ∀ i, 0 ≤ Winf i := fun i => (hlimK.1 i (Set.mem_univ i)).1
  have hc0' : 0 ≤ cinf := hlimK.2.1
  have hsum1 : 1 ≤ ∑ i, Winf i :=
    ge_of_tendsto' (tendsto_finsetSum _ fun i _ => hWi i) fun n => hWsum (φ n)
  -- positivity from irreducibility
  have hWpos : ∀ i, 0 < Winf i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i1, hi1⟩ := hcon
    let Z : Finset ι := Finset.univ.filter fun i => Winf i = 0
    have hZne : Z.Nonempty := ⟨i1, by simp [Z, le_antisymm hi1 (hW0 i1)]⟩
    have hZuniv : Z ≠ Finset.univ := by
      intro hZ
      have : ∑ i, Winf i = 0 := Finset.sum_eq_zero fun i _ => by
        have : i ∈ Z := hZ ▸ Finset.mem_univ i
        simpa [Z] using this
      linarith
    obtain ⟨i, hi, j, hj, hij⟩ := hcut Z hZne hZuniv
    have hWi0 : Winf i = 0 := by simpa [Z] using hi
    have hWj : 0 < Winf j := by
      have : Winf j ≠ 0 := by simpa [Z] using hj
      exact lt_of_le_of_ne (hW0 j) (Ne.symm this)
    have h1 := hEqlim i
    rw [hWi0, mul_zero] at h1
    have h2 : A i j * Winf j ≤ ∑ j, A i j * Winf j :=
      Finset.single_le_sum (f := fun j => A i j * Winf j)
        (fun j _ => mul_nonneg (hA i j) (hW0 j)) (Finset.mem_univ j)
    have := mul_pos hij hWj
    linarith
  refine ⟨cinf, Winf, ?_, hWpos, hEqlim⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨j, hj⟩ := hrow i
  have h1 := hEqlim i
  have h2 : A i j * Winf j ≤ ∑ j, A i j * Winf j :=
    Finset.single_le_sum (f := fun j => A i j * Winf j)
      (fun j _ => mul_nonneg (hA i j) (hW0 j)) (Finset.mem_univ j)
  have h3 := mul_pos hj (hWpos j)
  have h4 : 0 < cinf * Winf i := by linarith
  by_contra hneg
  have : cinf * Winf i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (hW0 i)
  linarith

/-- **Discount bound for irreducible matrices, with no eigenvector hypothesis** (Theorem 6.2
for a matrix with a single class).  There is `ρ > 0`, the Perron root, with
`|θ v_i - ln ρ| ≤ θ (2n - 1) Ω` for every `N ≥ 2` and every `i`. -/
theorem discount_irreducible' [Nonempty ι] {M : ι → ι → ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∃ j, 0 < M i j) {mmin mmax Ω : ℝ} (hmin0 : 0 < mmin)
    (hmin : ∀ i j, 0 < M i j → mmin ≤ M i j) (hmax : ∀ i j, M i j ≤ mmax)
    (hΩ : Real.log (Fintype.card ι * max mmax (max (1 / mmin) 1)) ≤ Ω)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j, j ∉ S ∧ 0 < M i j) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∃ U : ι → ℝ, (∀ i, 0 < U i) ∧ ∀ i, ∑ j, M i j * U j = ρ * U i) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ v : ι → ℝ, Psi (1 - 1 / (N : ℝ)) M v = v → ∀ i,
        |1 / (N : ℝ) * v i - Real.log ρ| ≤ 1 / (N : ℝ) * ((2 * Fintype.card ι - 1) * Ω) := by
  obtain ⟨ρ, U, hρ, hU, hMU⟩ := perron_frobenius_cut hM hrow hcut
  exact ⟨ρ, hρ, ⟨U, hU, hMU⟩, fun N hN v hv i =>
    discount_irreducible hN hM hmin0 hmin hmax hΩ hcut hρ hU hMU hv i⟩

end EntropyGames
