/-
Lemma 2 of the note: `p(n) ≤ exp(π √(2n/3)) < e^{3√n}` for `n ≥ 1`, by the paper's argument:
`p(n) xⁿ ≤ ∏_{k ≤ n} (1 - x^k)^{-1}`, `-log(1 - y) = ∑ y^m/m`, `ζ(2) = π²/6`, `x = e^{-u}`,
`u = π/√(6n)`. Consequently Theorem 3(ii) holds unconditionally (given Hypothesis A).
-/
import Depth3Note.Theorem3ii

universe u

namespace Depth3Note

open Finset

noncomputable section

/-! ### Step A: `p(n) xⁿ ≤ ∏_{i=1}^n ∑_{j=0}^n x^{ij}` -/

theorem card_le_sum_of_pos (s : Multiset ℕ) (h : ∀ x ∈ s, 0 < x) : Multiset.card s ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h1 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have h2 := h a (Multiset.mem_cons_self a s)
    simp only [Multiset.card_cons, Multiset.sum_cons]
    omega

theorem partition_count_le {n : ℕ} (μ : Nat.Partition n) (i : ℕ) : μ.parts.count i ≤ n := by
  calc μ.parts.count i ≤ Multiset.card μ.parts := Multiset.count_le_card _ _
    _ ≤ μ.parts.sum := card_le_sum_of_pos _ fun x hx => μ.parts_pos hx
    _ = n := μ.parts_sum

theorem partition_sum_count {n : ℕ} (μ : Nat.Partition n) :
    ∑ i ∈ Icc 1 n, i * μ.parts.count i = n := by
  have h := μ.toFinsuppAntidiag_mem_finsuppAntidiag
  rw [mem_finsuppAntidiag] at h
  have := h.1
  simpa [Nat.Partition.toFinsuppAntidiag, mul_comm] using this

theorem p_mul_pow_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) :
    (p n : ℝ) * x ^ n ≤ ∏ i ∈ Icc 1 n, ∑ j ∈ range (n + 1), x ^ (i * j) := by
  classical
  rw [Finset.prod_sum]
  let φ : Nat.Partition n → (∀ a ∈ Icc 1 n, ℕ) := fun μ a _ => μ.parts.count a
  have hnot : ∀ (μ : Nat.Partition n) (a : ℕ), a ∉ Icc 1 n → a ∉ μ.parts := fun μ a ha hm =>
    ha (mem_Icc.2 ⟨μ.parts_pos hm, Nat.Partition.le_of_mem_parts hm⟩)
  have hinj : Function.Injective φ := by
    intro μ ν h
    apply Nat.Partition.ext
    ext a
    by_cases ha : a ∈ Icc 1 n
    · exact congrFun (congrFun h a) ha
    · rw [Multiset.count_eq_zero_of_notMem (hnot μ a ha),
        Multiset.count_eq_zero_of_notMem (hnot ν a ha)]
  have hterm : ∀ μ : Nat.Partition n,
      ∏ a ∈ (Icc 1 n).attach, x ^ (a.1 * φ μ a.1 a.2) = x ^ n := by
    intro μ
    rw [Finset.prod_pow_eq_pow_sum,
      Finset.sum_attach (Icc 1 n) (fun a => a * μ.parts.count a), partition_sum_count]
  calc (p n : ℝ) * x ^ n = ∑ _μ : Nat.Partition n, x ^ n := by simp [p]
    _ = ∑ μ : Nat.Partition n, ∏ a ∈ (Icc 1 n).attach, x ^ (a.1 * φ μ a.1 a.2) := by
        simp only [hterm]
    _ = ∑ c ∈ univ.image φ, ∏ a ∈ (Icc 1 n).attach, x ^ (a.1 * c a.1 a.2) :=
        (Finset.sum_image (s := univ) (g := φ)
          (f := fun c : (∀ a ∈ Icc 1 n, ℕ) => ∏ a ∈ (Icc 1 n).attach, x ^ (a.1 * c a.1 a.2))
          (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ c ∈ (Icc 1 n).pi (fun _ => range (n + 1)),
          ∏ a ∈ (Icc 1 n).attach, x ^ (a.1 * c a.1 a.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨μ, -, rfl⟩ := mem_image.1 hc
          rw [mem_pi]
          intro a _
          exact mem_range.2 (Nat.lt_succ_of_le (partition_count_le μ a))
        · intro c _ _
          exact prod_nonneg fun a _ => pow_nonneg hx0 _

/-! ### Step B: `∑_{i=1}^n -log(1 - x^i) ≤ (π²/6) · x/(1-x)` -/

theorem geom_Icc_le (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ i ∈ Icc 1 n, r ^ i ≤ r / (1 - r) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have key : ∑ i ∈ Icc 1 n, r ^ i = r * (1 - r ^ n) / (1 - r) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      field_simp
      ring
  rw [key]
  apply div_le_div_of_nonneg_right _ h1.le
  have : 0 ≤ r ^ n := pow_nonneg hr0 n
  nlinarith

theorem bernoulli_aux (m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((m : ℝ) + 1) * x ^ m * (1 - x) ≤ 1 - x ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : x ^ (m + 1) ≤ x ^ m := pow_le_pow_of_le_one hx0 hx1 (Nat.le_succ m)
    have h2 : 0 ≤ x ^ (m + 1) := pow_nonneg hx0 _
    have h3 : x ^ (m + 1 + 1) = x ^ (m + 1) * x := pow_succ _ _
    have h4 : (0 : ℝ) ≤ 1 - x := by linarith
    have h5 : ((m : ℝ) + 1) * x ^ (m + 1) * (1 - x) ≤ ((m : ℝ) + 1) * x ^ m * (1 - x) := by
      apply mul_le_mul_of_nonneg_right _ h4
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    push_cast
    nlinarith

theorem sum_neg_log_le (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑ i ∈ Icc 1 n, -Real.log (1 - x ^ i) ≤ Real.pi ^ 2 / 6 * (x / (1 - x)) := by
  have hpow : ∀ i ∈ Icc 1 n, |x ^ i| < 1 := by
    intro i hi
    rw [abs_of_nonneg (pow_nonneg hx0.le i)]
    exact pow_lt_one₀ hx0.le hx1 (by have := (mem_Icc.1 hi).1; omega)
  have hL := hasSum_sum (fun i hi => Real.hasSum_pow_div_log_of_abs_lt_one (hpow i hi))
  have hz : HasSum (fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ)) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have hR := hz.mul_right (x / (1 - x))
  refine hasSum_le (fun m => ?_) hL hR
  have h1x : (0 : ℝ) < 1 - x := by linarith
  set r := x ^ (m + 1) with hr
  have hr0 : 0 ≤ r := pow_nonneg hx0.le _
  have hr1 : r < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsum : ∑ i ∈ Icc 1 n, (x ^ i) ^ (m + 1) / ((m : ℝ) + 1) =
      (∑ i ∈ Icc 1 n, r ^ i) / ((m : ℝ) + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr, ← pow_mul, ← pow_mul, mul_comm]
  have hb := bernoulli_aux m hx0.le hx1.le
  have hrx : r / (1 - r) ≤ x / (((m : ℝ) + 1) * (1 - x)) := by
    rw [div_le_div_iff₀ h1r (by positivity)]
    have hrm : r = x ^ m * x := pow_succ _ _
    have e1 : r * (((m : ℝ) + 1) * (1 - x)) = x * (((m : ℝ) + 1) * x ^ m * (1 - x)) := by
      rw [hrm]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hb hx0.le
  rw [hsum]
  calc (∑ i ∈ Icc 1 n, r ^ i) / ((m : ℝ) + 1)
      ≤ (r / (1 - r)) / ((m : ℝ) + 1) :=
        div_le_div_of_nonneg_right (geom_Icc_le n hr0 hr1) hm.le
    _ ≤ (x / (((m : ℝ) + 1) * (1 - x))) / ((m : ℝ) + 1) :=
        div_le_div_of_nonneg_right hrx hm.le
    _ = 1 / (((m + 1 : ℕ) : ℝ)) ^ 2 * (x / (1 - x)) := by
        push_cast
        field_simp

/-! ### Step C -/

theorem p_le_exp (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (p n : ℝ) ≤ Real.exp (n * u + Real.pi ^ 2 / (6 * u)) := by
  set x := Real.exp (-u) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    have h := Real.exp_lt_exp.2 (neg_lt_zero.2 hu)
    rw [Real.exp_zero] at h
    exact h
  have hxi : ∀ i ∈ Icc 1 n, x ^ i < 1 := fun i hi =>
    pow_lt_one₀ hx0.le hx1 (by have := (mem_Icc.1 hi).1; omega)
  have hA := p_mul_pow_le n hx0.le
  have hB : ∏ i ∈ Icc 1 n, ∑ j ∈ range (n + 1), x ^ (i * j) ≤
      ∏ i ∈ Icc 1 n, Real.exp (-Real.log (1 - x ^ i)) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg fun j _ => pow_nonneg hx0.le _
    · intro i hi
      have hlt := hxi i hi
      rw [Real.exp_neg, Real.exp_log (by linarith)]
      have hs := hasSum_geometric_of_lt_one (pow_nonneg hx0.le i) hlt
      have := sum_le_hasSum (range (n + 1)) (fun j _ => pow_nonneg (pow_nonneg hx0.le i) j) hs
      simpa [pow_mul] using this
  rw [← Real.exp_sum] at hB
  have hC := sum_neg_log_le n hx0 hx1
  have hD : x / (1 - x) ≤ 1 / u := by
    rw [div_le_div_iff₀ (by linarith) hu]
    have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h2 : x * Real.exp u = 1 := by rw [hx, ← Real.exp_add]; simp
    nlinarith
  have hE : (p n : ℝ) * x ^ n ≤ Real.exp (Real.pi ^ 2 / (6 * u)) := by
    refine hA.trans (hB.trans (Real.exp_le_exp.2 (hC.trans ?_)))
    have : Real.pi ^ 2 / (6 * u) = Real.pi ^ 2 / 6 * (1 / u) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hxn : x ^ n = (Real.exp (n * u))⁻¹ := by
    rw [hx, ← Real.exp_nat_mul, ← Real.exp_neg]
    ring_nf
  rw [hxn, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at hE
  rw [Real.exp_add, mul_comm]
  exact hE

/-- **Lemma 2** of the note. -/
theorem lemma2 : Lemma2Statement := by
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set s := Real.sqrt (6 * n) with hs
  have hs2 : s ^ 2 = 6 * n := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (2 * n / 3) = s / 3 := by
    rw [show (2 * (n : ℝ) / 3) = (s / 3) ^ 2 by rw [div_pow, hs2]; ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  constructor
  · have h := p_le_exp n (u := Real.pi / s) (by positivity)
    have e : (n : ℝ) * (Real.pi / s) + Real.pi ^ 2 / (6 * (Real.pi / s)) = Real.pi * (s / 3) := by
      have hpi := Real.pi_pos
      field_simp
      nlinarith
    rwa [e] at h
  · apply Real.exp_lt_exp.2
    have h3 : 3 * Real.sqrt n = Real.sqrt (9 * n) := by
      rw [show (9 : ℝ) * n = 3 ^ 2 * n by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [h3]
    apply Real.lt_sqrt_of_sq_lt
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have : Real.pi ^ 2 < 10 := by nlinarith
    have e : (Real.pi * (s / 3)) ^ 2 = Real.pi ^ 2 * (6 * n) / 9 := by
      rw [mul_pow, div_pow, hs2]; ring
    rw [e]
    nlinarith

theorem lemma2_weak : Lemma2WeakStatement := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [p]
  · exact (lemma2 n hn).1.trans (lemma2 n hn).2.le

/-- **Theorem 3(ii)** of the note, unconditional (given Hypothesis A as a hypothesis), with
`n₁ = max n₀ 2560000`. -/
theorem theorem3ii : Theorem3iiStatement.{u} := theorem3ii_of_lemma2 lemma2_weak

end

end Depth3Note
