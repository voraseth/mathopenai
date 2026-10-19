/-
Lemma 1 of the note: the degree-`n` component of a `ΣΠΣ` expression is computed by a syntactically
homogeneous `ΣΠΣΠΣ` circuit, in the release's structure `Depth5Circuit`, with at most
`N³ + 2B + nB + ns + s·p(n) + 1` vertices.

Differences from the proof in the paper (the STATEMENT is the paper's, with `V = N³`):
* no normalisation step is needed. In the release's structure, formal degrees are declared and the
  homogeneity conditions are purely syntactic, so a bottom sum all of whose coefficients vanish
  still has formal degree `1`; forms with `ℓ_j = 0` need no special treatment. Constant forms
  `L_j = a_j ≠ 0` are handled by the general formula (`y_j = 0`).
* the middle sum `P_t(y_i)` reads `ℓ_j^t` for EVERY `j` (coefficient `0` when `a_j = 0` or
  `j ∉ J_i`), so it is non-empty as soon as `B ≥ 1`; the cases `B = 0` and `N = 0` (where
  `f_n = 0`) use the circuit with an empty output sum.
* the coefficients of the output sum are those given by `exists_esymmW_eq`, not the closed form.
-/
import Depth3Note.Newton
import Depth3Note.Typed

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset

noncomputable section

/-! ### Monotonicity of the partition function -/

/-- add `d` parts equal to `1` -/
def addOnes {k : ℕ} (d : ℕ) (μ : Nat.Partition k) : Nat.Partition (k + d) where
  parts := μ.parts + Multiset.replicate d 1
  parts_pos := by
    intro x hx
    rcases Multiset.mem_add.1 hx with h | h
    · exact μ.parts_pos h
    · rw [Multiset.eq_of_mem_replicate h]
      exact Nat.one_pos
  parts_sum := by simp [μ.parts_sum]

theorem p_mono {k n : ℕ} (h : k ≤ n) : p k ≤ p n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine Fintype.card_le_of_injective (addOnes d) ?_
  intro μ ν hμν
  have := congrArg Nat.Partition.parts hμν
  simp only [addOnes, add_left_inj] at this
  exact Nat.Partition.ext this

/-! ### The trivial circuit -/

/-- the circuit with no leaves, no inner gates and an empty output sum -/
def zeroCircuit (K : Type u) [CommSemiring K] (N : ℕ) : Depth5Circuit K N where
  leafCount := 0
  leaves := fun i => i.elim0
  bottomCount := 0
  bottomInputs := fun i => i.elim0
  bottomDegree := fun _ => 0
  bottomHomogeneous := fun i => i.elim0
  bottomEmpty := fun i => i.elim0
  lowerCount := 0
  lowerInputs := fun i => i.elim0
  middleCount := 0
  middleInputs := fun i => i.elim0
  middleDegree := fun _ => 0
  middleHomogeneous := fun i => i.elim0
  middleEmpty := fun i => i.elim0
  upperCount := 0
  upperInputs := fun i => i.elim0
  outputInputs := []
  outputDegree := 0
  outputHomogeneous := by
    intro e h
    simp at h
  outputEmpty := fun _ => rfl

theorem circuitValue_zeroCircuit (K : Type u) [CommSemiring K] (N : ℕ) :
    circuitValue (zeroCircuit K N) = 0 := by
  simp [circuitValue, zeroCircuit]

theorem circuitSize_zeroCircuit (K : Type u) [CommSemiring K] (N : ℕ) :
    circuitSize (zeroCircuit K N) = 1 := by
  simp [circuitSize, zeroCircuit]

theorem homogeneousComponent_C_eq_zero {K : Type*} [CommSemiring K] {σ : Type*} (r : K) {n : ℕ}
    (hn : n ≠ 0) : homogeneousComponent n (C r : MvPolynomial σ K) = 0 := by
  rw [← mul_one (C r), homogeneousComponent_C_mul,
    homogeneousComponent_of_mem (isHomogeneous_one σ K), if_neg hn, mul_zero]

/-! ### Decomposition of a `ΣΠΣ` expression -/

namespace SPS

variable {K : Type u} [Field K] {σ : Type} [Fintype σ] (S : SPS K σ)

open Classical in
/-- multiplicity of `L_j` in term `i` if `a_j = 0` (that is, `j ∈ J_i⁰`), else `0` -/
def m0 (i : Fin S.s) (j : Fin S.B) : ℕ := if S.a j = 0 then S.m i j else 0

open Classical in
/-- multiplicity of `L_j` in term `i` if `a_j ≠ 0` (that is, `j ∈ J_i¹`), else `0` -/
def m1 (i : Fin S.s) (j : Fin S.B) : ℕ := if S.a j = 0 then 0 else S.m i j

/-- `D₀(i)` -/
def D0 (i : Fin S.s) : ℕ := ∑ j, S.m0 i j

/-- `ℓ_j / a_j` -/
def y (j : Fin S.B) : MvPolynomial σ K := C ((S.a j)⁻¹) * S.lin j

/-- `c_i ∏_{j ∈ J_i¹} a_j^{m_ij}` -/
def alpha (i : Fin S.s) : K := S.c i * ∏ j, S.a j ^ S.m1 i j

/-- `∏_{j ∈ J_i⁰} ℓ_j^{m_ij}` -/
def Hprod (i : Fin S.s) : MvPolynomial σ K := ∏ j, S.lin j ^ S.m0 i j

/-- the scalar `m_ij a_j^{-r}` -/
def w (i : Fin S.s) (r : ℕ) (j : Fin S.B) : K := (S.m1 i j : K) * ((S.a j)⁻¹) ^ r

/-- the power sum `P_r(y_i) = ∑_j m_ij a_j^{-r} ℓ_j^r` -/
def Pform (i : Fin S.s) (r : ℕ) : MvPolynomial σ K := ∑ j, C (S.w i r j) * S.lin j ^ r

theorem lin_isHomogeneous (j : Fin S.B) : (S.lin j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem y_isHomogeneous (j : Fin S.B) : (S.y j).IsHomogeneous 1 :=
  (S.lin_isHomogeneous j).C_mul _

theorem Hprod_isHomogeneous (i : Fin S.s) : (S.Hprod i).IsHomogeneous (S.D0 i) := by
  have h := IsHomogeneous.prod univ (fun j => S.lin j ^ S.m0 i j) (fun j => S.m0 i j)
    (fun j _ => by simpa using (S.lin_isHomogeneous j).pow (S.m0 i j))
  exact h

theorem term_eq (i : Fin S.s) :
    C (S.c i) * ∏ j, S.form j ^ S.m i j =
      C (S.alpha i) * (S.Hprod i * ∏ j, (1 + S.y j) ^ S.m1 i j) := by
  have hj : ∀ j, S.form j ^ S.m i j =
      C (S.a j ^ S.m1 i j) * (S.lin j ^ S.m0 i j * (1 + S.y j) ^ S.m1 i j) := by
    intro j
    by_cases h : S.a j = 0
    · simp [m0, m1, h, form]
    · simp only [m0, m1, h, if_false, pow_zero, one_mul, form, y]
      rw [C_pow, ← mul_pow]
      congr 1
      rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h, C_1, one_mul]
  simp only [hj, alpha, Hprod, Finset.prod_mul_distrib, C_mul, map_prod]
  ring

theorem homogeneousComponent_value (n : ℕ) :
    homogeneousComponent n S.value =
      ∑ i, if S.D0 i ≤ n then C (S.alpha i) * (S.Hprod i * esymmW (S.m1 i) S.y (n - S.D0 i))
        else 0 := by
  rw [value, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term_eq, homogeneousComponent_C_mul,
    homogeneousComponent_mul_prod_one_add (S.m1 i) S.y S.y_isHomogeneous (S.Hprod i) (S.D0 i)
      (S.Hprod_isHomogeneous i) n]
  split_ifs <;> simp

theorem sum_m1_smul_y_pow (i : Fin S.s) (r : ℕ) :
    ∑ j, S.m1 i j • S.y j ^ r = S.Pform i r := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul, y, mul_pow, ← C_pow, ← mul_assoc, ← map_natCast (C : K →+* MvPolynomial σ K),
    ← C_mul]
  rfl

/-- The degree-`n` component as a combination of products of the gates of the circuit. -/
theorem exists_normal_form [CharZero K] (n : ℕ) :
    ∃ coef : ∀ i, Nat.Partition (n - S.D0 i) → K,
      homogeneousComponent n S.value =
        ∑ i, if S.D0 i ≤ n then
          ∑ μ, C (S.alpha i * coef i μ) * (S.Hprod i * (μ.parts.map (S.Pform i)).prod)
        else 0 := by
  choose coef hcoef using fun i => exists_esymmW_eq (K := K) (S.m1 i) S.y (n - S.D0 i)
  refine ⟨coef, ?_⟩
  rw [homogeneousComponent_value]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [hcoef, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hP : (fun r => ∑ j, S.m1 i j • S.y j ^ r) = S.Pform i :=
      funext (S.sum_m1_smul_y_pow i)
    rw [hP, smul_eq_C_mul, C_mul]
    ring
  · rfl

end SPS

/-! ### The circuit -/

theorem map_sum_nsmul_singleton_prod {ι α M : Type*} [CommMonoid M] (s : Finset ι) (m : ι → ℕ)
    (f : ι → α) (g : α → M) :
    ((∑ j ∈ s, m j • ({f j} : Multiset α)).map g).prod = ∏ j ∈ s, g (f j) ^ m j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.map_add, Multiset.prod_add, ih, Finset.prod_insert ha,
      Multiset.map_nsmul, Multiset.prod_nsmul]
    simp

theorem map_sum_nsmul_singleton_sum {ι α : Type*} (s : Finset ι) (m : ι → ℕ)
    (f : ι → α) (g : α → ℕ) :
    ((∑ j ∈ s, m j • ({f j} : Multiset α)).map g).sum = ∑ j ∈ s, m j * g (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih, Finset.sum_insert ha,
      Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

/-- the gate index of the power `r`, for `1 ≤ r ≤ n` -/
def toFin (n : ℕ) (hn : 0 < n) (r : ℕ) : Fin n := ⟨(r - 1) % n, Nat.mod_lt _ hn⟩

theorem toFin_add_one {n : ℕ} (hn : 0 < n) {r : ℕ} (h1 : 0 < r) (h2 : r ≤ n) :
    (toFin n hn r : ℕ) + 1 = r := by
  have : (r - 1) % n = r - 1 := Nat.mod_eq_of_lt (by omega)
  simp only [toFin, this]
  omega

variable {K : Type u} [Field K] {N : ℕ}

/-- **The circuit of Lemma 1**, with typed gates:
* bottom sums `ℓ_j`, `j < B`;
* lower products `ℓ_j^{t+1}`, `j < B`, `t < n`;
* middle sums: the unary gates `U_j` (`Sum.inl j`) and the power sums `P_{t+1}(y_i)`
  (`Sum.inr (i, t)`), `i < s`, `t < n`;
* upper products: for each `i` and each partition `μ` of `n - D₀(i)`;
* output: the upper products with `D₀(i) ≤ n`. -/
def lemma1TC (S : SPS K (ImmVar N)) (n : ℕ) (hn : 0 < n) (hB : 0 < S.B)
    (coef : ∀ i, Nat.Partition (n - S.D0 i) → K) :
    TC K N (Fin S.B) (Fin S.B × Fin n) (Fin S.B ⊕ (Fin S.s × Fin n))
      (Σ i : Fin S.s, Nat.Partition (n - S.D0 i)) where
  botCoef := S.l
  low := fun e => Multiset.replicate (e.2 + 1) e.1
  mid := Sum.elim (fun j => {(j, ⟨0, hn⟩)}) (fun it => univ ×ˢ {it.2})
  midCoef := Sum.elim (fun _ _ => 1) (fun it e => S.w it.1 (it.2 + 1) e.1)
  up := fun u => (∑ j, S.m0 u.1 j • ({Sum.inl j} : Multiset (Fin S.B ⊕ (Fin S.s × Fin n)))) +
    u.2.parts.map (fun r => Sum.inr (u.1, toFin n hn r))
  out := univ.filter (fun u => S.D0 u.1 ≤ n)
  outCoef := fun u => S.alpha u.1 * coef u.1 u.2
  midDeg := Sum.elim (fun _ => 1) (fun it => it.2 + 1)
  outDeg := n
  mid_ne := by
    haveI : Nonempty (Fin S.B) := ⟨⟨0, hB⟩⟩
    rintro (j | it)
    · exact singleton_nonempty _
    · exact univ_nonempty.product (singleton_nonempty _)
  mid_hom := by
    rintro (j | it) e he
    · simp only [Sum.elim_inl, mem_singleton] at he
      simp [he]
    · simp only [Sum.elim_inr, mem_product, mem_univ, mem_singleton, true_and] at he
      simp [he]
  out_hom := by
    rintro ⟨i, μ⟩ hu
    have hD : S.D0 i ≤ n := (mem_filter.1 hu).2
    rw [Multiset.map_add, Multiset.sum_add, map_sum_nsmul_singleton_sum, Multiset.map_map]
    have h2 : (μ.parts.map
        ((Sum.elim (fun _ => 1) (fun it : Fin S.s × Fin n => (it.2 : ℕ) + 1)) ∘
          fun r => (Sum.inr (i, toFin n hn r) : Fin S.B ⊕ (Fin S.s × Fin n)))) =
        μ.parts.map id := by
      refine Multiset.map_congr rfl fun r hr => ?_
      have := Nat.Partition.le_of_mem_parts hr
      simpa using toFin_add_one hn (μ.parts_pos hr) (by omega)
    rw [h2, Multiset.map_id, μ.parts_sum]
    simp only [Sum.elim_inl, mul_one]
    have : ∑ j, S.m0 i j = S.D0 i := rfl
    omega

section Values

variable (S : SPS K (ImmVar N)) (n : ℕ) (hn : 0 < n) (hB : 0 < S.B)
  (coef : ∀ i, Nat.Partition (n - S.D0 i) → K)

theorem lemma1TC_lowVal (e : Fin S.B × Fin n) :
    (lemma1TC S n hn hB coef).lowVal e = S.lin e.1 ^ ((e.2 : ℕ) + 1) := by
  simp [TC.lowVal, lemma1TC, TC.botVal, SPS.lin, pow_succ']

theorem lemma1TC_midVal_inl (j : Fin S.B) :
    (lemma1TC S n hn hB coef).midVal (Sum.inl j) = S.lin j := by
  rw [TC.midVal]
  simp only [lemma1TC_lowVal]
  simp [lemma1TC]

theorem lemma1TC_midVal_inr (i : Fin S.s) (t : Fin n) :
    (lemma1TC S n hn hB coef).midVal (Sum.inr (i, t)) = S.Pform i ((t : ℕ) + 1) := by
  rw [TC.midVal]
  simp only [lemma1TC_lowVal]
  simp [lemma1TC, SPS.Pform]

theorem lemma1TC_upVal (i : Fin S.s) (μ : Nat.Partition (n - S.D0 i)) :
    (lemma1TC S n hn hB coef).upVal ⟨i, μ⟩ = S.Hprod i * (μ.parts.map (S.Pform i)).prod := by
  rw [TC.upVal]
  have hup : (lemma1TC S n hn hB coef).up ⟨i, μ⟩ =
      (∑ j, S.m0 i j • ({Sum.inl j} : Multiset (Fin S.B ⊕ (Fin S.s × Fin n)))) +
        μ.parts.map (fun r => Sum.inr (i, toFin n hn r)) := rfl
  rw [hup, Multiset.map_add, Multiset.prod_add, map_sum_nsmul_singleton_prod, Multiset.map_map]
  congr 1
  · simp only [lemma1TC_midVal_inl]
    rfl
  · congr 1
    refine Multiset.map_congr rfl fun r hr => ?_
    have := Nat.Partition.le_of_mem_parts hr
    simp only [Function.comp_apply, lemma1TC_midVal_inr]
    rw [toFin_add_one hn (μ.parts_pos hr) (by omega)]

theorem lemma1TC_value :
    (lemma1TC S n hn hB coef).value =
      ∑ i, if S.D0 i ≤ n then
        ∑ μ, C (S.alpha i * coef i μ) * (S.Hprod i * (μ.parts.map (S.Pform i)).prod)
      else 0 := by
  rw [TC.value]
  have hout : (lemma1TC S n hn hB coef).out = univ.filter (fun u => S.D0 u.1 ≤ n) := rfl
  rw [hout, Finset.sum_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [lemma1TC_upVal]
    rfl
  · simp

end Values

/-! ### Lemma 1 -/

/-- **Lemma 1** of the note. -/
theorem lemma1 : Lemma1Statement.{u} := by
  intro K _ _ N S n hn
  have hn0 : n ≠ 0 := by omega
  -- the two degenerate cases, where `f_n = 0`
  have triv : homogeneousComponent n S.value = 0 →
      ∃ c : Depth5Circuit K N, circuitValue c = homogeneousComponent n S.value ∧
        circuitSize c ≤ N ^ 3 + 2 * S.B + n * S.B + n * S.s + S.s * p n + 1 := by
    intro h
    exact ⟨zeroCircuit K N, by rw [circuitValue_zeroCircuit, h],
      by rw [circuitSize_zeroCircuit]; exact Nat.le_add_left _ _⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    apply triv
    rw [eq_C_of_isEmpty S.value]
    exact homogeneousComponent_C_eq_zero _ hn0
  rcases Nat.eq_zero_or_pos S.B with hB | hB
  · apply triv
    haveI : IsEmpty (Fin S.B) := by rw [hB]; infer_instance
    have hv : S.value = C (∑ i, S.c i) := by
      simp [SPS.value]
    rw [hv]
    exact homogeneousComponent_C_eq_zero _ hn0
  -- the main case
  obtain ⟨coef, hcoef⟩ := S.exists_normal_form n
  refine ⟨(lemma1TC S n hn hB coef).toD5 hN, ?_, ?_⟩
  · rw [TC.circuitValue_toD5, lemma1TC_value, hcoef]
  · rw [TC.circuitSize_toD5]
    have hups : Fintype.card (Σ i : Fin S.s, Nat.Partition (n - S.D0 i)) ≤ S.s * p n := by
      rw [Fintype.card_sigma]
      calc ∑ i : Fin S.s, Fintype.card (Nat.Partition (n - S.D0 i))
          ≤ ∑ _i : Fin S.s, p n := Finset.sum_le_sum fun i _ => p_mono (Nat.sub_le _ _)
        _ = S.s * p n := by simp
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_sum]
    nlinarith [hups]

end

end Depth3Note
