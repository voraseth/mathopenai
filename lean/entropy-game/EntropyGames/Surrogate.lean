/-
Section 5 of the paper: the rational surrogate of log-sum-exp.
Lemma 5.1 (the function `E`), Lemma 5.2 (exactness), Lemma 5.3 (accuracy).
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

/-! ### The truncated exponential `P_r` and the function `E` of Equation (5.1) -/

/-- `P_r(y) = ∑_{i=0}^{r} y^i / i!`. -/
noncomputable def expPoly (r : ℕ) (y : ℝ) : ℝ := ∑ i ∈ range (r + 1), y ^ i / (i.factorial : ℝ)

/-- Equation (5.1): `E(x) = P_r(x)` for `x ≥ 0` and `1 / P_r(-x)` for `x < 0`. -/
noncomputable def surE (r : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then expPoly r x else 1 / expPoly r (-x)

theorem expPoly_zero (r : ℕ) : expPoly r 0 = 1 := by
  unfold expPoly
  rw [Finset.sum_range_succ']
  simp

theorem continuous_expPoly (r : ℕ) : Continuous (expPoly r) := by
  unfold expPoly
  fun_prop

theorem expPoly_le_exp (r : ℕ) {y : ℝ} (hy : 0 ≤ y) : expPoly r y ≤ Real.exp y :=
  Real.sum_le_exp_of_nonneg hy _

theorem expPoly_mono (r : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : expPoly r a ≤ expPoly r b := by
  unfold expPoly
  refine Finset.sum_le_sum fun i _ => ?_
  have := pow_le_pow_left₀ ha hab i
  gcongr

theorem one_add_le_expPoly {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : 0 ≤ y) : 1 + y ≤ expPoly r y := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  unfold expPoly
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have : 0 ≤ ∑ i ∈ range k, y ^ (i + 1 + 1) / ((i + 1 + 1).factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  simp
  linarith

theorem one_le_expPoly (r : ℕ) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ expPoly r y := by
  rw [← expPoly_zero r]; exact expPoly_mono r le_rfl hy

theorem expPoly_strictMono {r : ℕ} (hr : 1 ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    expPoly r a < expPoly r b := by
  unfold expPoly
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨1, by simp; omega, by simpa using hab⟩
  have := pow_le_pow_left₀ ha hab.le i
  gcongr

theorem surE_eq_abs (r : ℕ) (x : ℝ) :
    surE r x = if 0 ≤ x then expPoly r |x| else 1 / expPoly r |x| := by
  unfold surE
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]

theorem surE_of_nonneg (r : ℕ) {x : ℝ} (h : 0 ≤ x) : surE r x = expPoly r x := by
  simp [surE, h]

theorem surE_of_neg (r : ℕ) {x : ℝ} (h : x < 0) : surE r x = 1 / expPoly r (-x) := by
  simp [surE, not_le.mpr h]

theorem surE_of_nonpos (r : ℕ) {x : ℝ} (h : x ≤ 0) : surE r x = 1 / expPoly r (-x) := by
  rcases h.lt_or_eq with h | h
  · exact surE_of_neg r h
  · subst h; simp [surE, expPoly_zero]

/-- Lemma 5.1(a): `E(0) = 1`. -/
theorem surE_zero (r : ℕ) : surE r 0 = 1 := by simp [surE, expPoly_zero]

theorem surE_pos (r : ℕ) (x : ℝ) : 0 < surE r x := by
  unfold surE
  split_ifs with h
  · linarith [one_le_expPoly r h]
  · have := one_le_expPoly r (y := -x) (by linarith)
    positivity

/-- Lemma 5.1(a): `E` is continuous. -/
theorem continuous_surE (r : ℕ) : Continuous (surE r) := by
  have h : surE r = fun x => if 0 ≤ x then expPoly r |x| else 1 / expPoly r |x| :=
    funext (surE_eq_abs r)
  rw [h]
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact (continuous_expPoly r).comp continuous_abs
  · refine Continuous.div continuous_const ((continuous_expPoly r).comp continuous_abs) ?_
    intro x
    have := one_le_expPoly r (abs_nonneg x)
    linarith
  · intro x hx
    subst hx
    simp [expPoly_zero]

/-- Lemma 5.1(a): `E` is strictly increasing (for `r ≥ 1`). -/
theorem strictMono_surE {r : ℕ} (hr : 1 ≤ r) : StrictMono (surE r) := by
  intro x y hxy
  rcases le_or_gt 0 x with hx | hx
  · rw [surE_of_nonneg r hx, surE_of_nonneg r (hx.trans hxy.le)]
    exact expPoly_strictMono hr hx hxy
  · rcases le_or_gt 0 y with hy | hy
    · rw [surE_of_neg r hx, surE_of_nonneg r hy]
      have h1 : 1 < expPoly r (-x) := by
        have := expPoly_strictMono hr le_rfl (show (0 : ℝ) < -x by linarith)
        rwa [expPoly_zero] at this
      have h2 := one_le_expPoly r hy
      have : 1 / expPoly r (-x) < 1 := by
        rw [div_lt_one (by linarith)]; exact h1
      linarith
    · rw [surE_of_neg r hx, surE_of_neg r hy]
      have h1 := expPoly_strictMono hr (show (0 : ℝ) ≤ -y by linarith) (show -y < -x by linarith)
      have h2 := one_le_expPoly r (show (0 : ℝ) ≤ -y by linarith)
      exact one_div_lt_one_div_of_lt (by linarith) h1

/-- Lemma 5.1(a): `E(x) ≤ e^x` for `x ≥ 0`. -/
theorem surE_le_exp (r : ℕ) {x : ℝ} (hx : 0 ≤ x) : surE r x ≤ Real.exp x := by
  rw [surE_of_nonneg r hx]; exact expPoly_le_exp r hx

/-- Lemma 5.1(a): `E(x) ≥ e^x` for `x ≤ 0`. -/
theorem exp_le_surE (r : ℕ) {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ surE r x := by
  rw [surE_of_nonpos r hx]
  have h1 := expPoly_le_exp r (show (0 : ℝ) ≤ -x by linarith)
  have h2 := one_le_expPoly r (show (0 : ℝ) ≤ -x by linarith)
  rw [show x = -(-x) by ring, Real.exp_neg, ← one_div, neg_neg]
  exact one_div_le_one_div_of_le (by linarith) h1

/-- Lemma 5.1(a): `E(x) → ∞` as `x → ∞` (for `r ≥ 1`). -/
theorem tendsto_surE_atTop {r : ℕ} (hr : 1 ≤ r) : Filter.Tendsto (surE r) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  rw [surE_of_nonneg r hx]
  have := one_add_le_expPoly hr hx
  simp only [id]
  linarith

/-- Lemma 5.1(a): `E(x) → 0` as `x → -∞` (for `r ≥ 1`). -/
theorem tendsto_surE_atBot {r : ℕ} (hr : 1 ≤ r) :
    Filter.Tendsto (surE r) Filter.atBot (nhds 0) := by
  have hlim : Filter.Tendsto (fun x : ℝ => 1 / (1 - x)) Filter.atBot (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => 1 - x) Filter.atBot Filter.atTop := by
      have := Filter.tendsto_neg_atBot_atTop (G := ℝ)
      simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_left Filter.atBot (1 : ℝ) this
    exact (this.inv_tendsto_atTop).congr (fun x => by simp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun x => (surE_pos r x).le) ?_
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
  rw [surE_of_nonpos r hx]
  have h1 := one_add_le_expPoly hr (show (0 : ℝ) ≤ -x by linarith)
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- Tail of the exponential series: `e^y - P_r(y) ≤ y^{r+1}/(r+1)! · e^y` for `y ≥ 0`. -/
theorem expPoly_tail (r : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp y - expPoly r y ≤ y ^ (r + 1) / ((r + 1).factorial : ℝ) * Real.exp y := by
  have hs : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have h1 := (hasSum_nat_add_iff' (r + 1)).mpr hs
  have h2 := hs.mul_left (y ^ (r + 1) / ((r + 1).factorial : ℝ))
  refine hasSum_le (fun n => ?_) h1 h2
  have hf : ((n.factorial : ℝ) * ((r + 1).factorial : ℝ)) ≤ ((n + (r + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add n (r + 1))
  have hp : 0 ≤ y ^ n * y ^ (r + 1) := by positivity
  rw [pow_add, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hf hp]

/-- Lemma 5.1(b). -/
theorem expPoly_ge {r : ℕ} {K0 η0 : ℝ} (hη0 : 0 < η0)
    (hr1 : 2 * Real.exp 1 * K0 ≤ r + 1) (hr2 : Real.logb 2 (2 / η0) ≤ r + 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hyK : y ≤ K0) : (1 - η0) * Real.exp y ≤ expPoly r y := by
  have htail := expPoly_tail r hy0
  set k := r + 1 with hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  -- k^k ≤ e^k k!
  have hfac : (k : ℝ) ^ k ≤ Real.exp 1 ^ k * (k.factorial : ℝ) := by
    have := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
    rw [div_le_iff₀ (by positivity)] at this
    rw [← Real.exp_nat_mul, mul_one]
    exact this
  -- e y ≤ k / 2
  have hey : Real.exp 1 * y ≤ (k : ℝ) / 2 := by
    have : Real.exp 1 * y ≤ Real.exp 1 * K0 := by gcongr
    have hk' : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    rw [hk, hk']; linarith
  have hpow : (Real.exp 1 * y) ^ k ≤ ((k : ℝ) / 2) ^ k :=
    pow_le_pow_left₀ (by positivity) hey k
  -- 2^k ≥ 2/η0
  have h2k : 2 / η0 ≤ (2 : ℝ) ^ k := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 (2 / η0)) = 2 / η0 :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    have h2 : (2 : ℝ) ^ (Real.logb 2 (2 / η0)) ≤ (2 : ℝ) ^ ((k : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hk]; push_cast; linarith
    rw [Real.rpow_natCast] at h2
    linarith
  -- y^k / k! ≤ η0
  have hfpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hbound : y ^ k / (k.factorial : ℝ) ≤ η0 := by
    rw [div_le_iff₀ hfpos]
    have he : 0 < Real.exp 1 ^ k := by positivity
    have h2pos : (0 : ℝ) < 2 ^ k := by positivity
    have h3 : Real.exp 1 ^ k * y ^ k * 2 ^ k ≤ (k : ℝ) ^ k := by
      rw [mul_pow] at hpow
      rw [div_pow, le_div_iff₀ h2pos] at hpow
      exact hpow
    have h4 : 2 ≤ η0 * 2 ^ k := by
      rw [div_le_iff₀ hη0] at h2k; linarith
    -- e^k y^k 2^k ≤ k^k ≤ e^k k!  ⇒ y^k 2^k ≤ k!
    have h5 : y ^ k * 2 ^ k ≤ (k.factorial : ℝ) := by
      have : Real.exp 1 ^ k * (y ^ k * 2 ^ k) ≤ Real.exp 1 ^ k * (k.factorial : ℝ) := by
        calc Real.exp 1 ^ k * (y ^ k * 2 ^ k) = Real.exp 1 ^ k * y ^ k * 2 ^ k := by ring
          _ ≤ (k : ℝ) ^ k := h3
          _ ≤ _ := hfac
      exact le_of_mul_le_mul_left this he
    have hyk : 0 ≤ y ^ k := by positivity
    nlinarith
  have hexp := Real.exp_pos y
  nlinarith

/-! ### Lemma 5.2 (exactness) -/

/-- The hypotheses on `E` in the last sentence of Lemma 5.2: a continuous strictly increasing
map of `ℝ` onto `(0, ∞)`. -/
structure IsExpLike (E : ℝ → ℝ) : Prop where
  cont : Continuous E
  strictMono : StrictMono E
  pos : ∀ x, 0 < E x
  atBot : Filter.Tendsto E Filter.atBot (nhds 0)
  atTop : Filter.Tendsto E Filter.atTop Filter.atTop

/-- Lemma 5.1(a), packaged. -/
theorem isExpLike_surE {r : ℕ} (hr : 1 ≤ r) : IsExpLike (surE r) :=
  ⟨continuous_surE r, strictMono_surE hr, surE_pos r, tendsto_surE_atBot hr, tendsto_surE_atTop hr⟩

variable {ι : Type*}

/-- `Φ_p(t, s) = ∑_{j ∈ D_p} m_{pj} E(t_j - s)`; `S` is the set `D_p`. -/
def Phi (E : ℝ → ℝ) (S : Finset ι) (m : ι → ℝ) (t : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ S, m j * E (t j - s)

/-- `g_p(t)`: the zero of `s ↦ Φ_p(t, s) - 1` (unique under the hypotheses of Lemma 5.2). -/
noncomputable def surrogate (E : ℝ → ℝ) (S : Finset ι) (m : ι → ℝ) (t : ι → ℝ) : ℝ :=
  Classical.epsilon fun s => Phi E S m t s = 1

/-- `ℓ_p(t) = ln ∑_{j ∈ D_p} m_{pj} e^{t_j}`. -/
noncomputable def lse (S : Finset ι) (m : ι → ℝ) (t : ι → ℝ) : ℝ :=
  Real.log (∑ j ∈ S, m j * Real.exp (t j))

section exactness

variable {E : ℝ → ℝ} {S : Finset ι} {m : ι → ℝ}

theorem Phi_strictAnti (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) (t : ι → ℝ) :
    StrictAnti (Phi E S m t) := by
  intro s s' hss
  unfold Phi
  refine Finset.sum_lt_sum_of_nonempty hS fun j hj => ?_
  exact mul_lt_mul_of_pos_left (hE.strictMono (by linarith)) (hm j hj)

theorem exists_Phi_eq_one (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    (t : ι → ℝ) : ∃ s, Phi E S m t s = 1 := by
  have hcont : Continuous (Phi E S m t) := by
    unfold Phi
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hE.cont.comp (continuous_const.sub continuous_id))
  apply mem_range_of_exists_le_of_exists_ge hcont
  · have hM : 0 < ∑ j ∈ S, m j := Finset.sum_pos hm hS
    obtain ⟨x1, hx1⟩ : ∃ x1, E x1 < 1 / ∑ j ∈ S, m j :=
      (hE.atBot.eventually (gt_mem_nhds (by positivity))).exists
    refine ⟨S.sup' hS t - x1, ?_⟩
    calc Phi E S m t (S.sup' hS t - x1) ≤ ∑ j ∈ S, m j * E x1 :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
            (hE.strictMono.monotone (by linarith [Finset.le_sup' t hj])) (hm j hj).le
      _ = (∑ j ∈ S, m j) * E x1 := by rw [Finset.sum_mul]
      _ ≤ 1 := by rw [lt_div_iff₀ hM] at hx1; linarith
  · obtain ⟨j0, hj0⟩ := hS
    obtain ⟨x0, hx0⟩ : ∃ x0, 1 / m j0 ≤ E x0 :=
      (hE.atTop.eventually (Filter.eventually_ge_atTop _)).exists
    refine ⟨t j0 - x0, ?_⟩
    calc (1 : ℝ) ≤ m j0 * E (t j0 - (t j0 - x0)) := by
          rw [sub_sub_cancel]; rw [div_le_iff₀ (hm j0 hj0)] at hx0; linarith
      _ ≤ Phi E S m t (t j0 - x0) :=
          Finset.single_le_sum (f := fun j => m j * E (t j - (t j0 - x0)))
            (fun j hj => (mul_pos (hm j hj) (hE.pos _)).le) hj0

/-- `g_p(t)` is a zero of `Φ_p(t, ·) - 1`. -/
theorem Phi_surrogate (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) (t : ι → ℝ) :
    Phi E S m t (surrogate E S m t) = 1 :=
  Classical.epsilon_spec (exists_Phi_eq_one hE hS hm t)

/-- `g_p(t)` is the unique zero. -/
theorem surrogate_unique (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    {t : ι → ℝ} {s : ℝ} (h : Phi E S m t s = 1) : s = surrogate E S m t :=
  (Phi_strictAnti hE hS hm t).injective (h.trans (Phi_surrogate hE hS hm t).symm)

/-- Lemma 5.2(a): `g_p(t) ≥ s` if and only if `Φ_p(t, s) ≥ 1`. -/
theorem le_surrogate_iff (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    (t : ι → ℝ) (s : ℝ) : s ≤ surrogate E S m t ↔ 1 ≤ Phi E S m t s := by
  rw [← Phi_surrogate hE hS hm t]
  exact ((Phi_strictAnti hE hS hm t).le_iff_ge).symm

/-- Companion of Lemma 5.2(a): `g_p(t) ≤ s` if and only if `Φ_p(t, s) ≤ 1`. -/
theorem surrogate_le_iff (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    (t : ι → ℝ) (s : ℝ) : surrogate E S m t ≤ s ↔ Phi E S m t s ≤ 1 := by
  rw [← Phi_surrogate hE hS hm t]
  exact ((Phi_strictAnti hE hS hm t).le_iff_ge).symm

/-- Lemma 5.2(b): exact monotonicity. -/
theorem surrogate_mono (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    {t t' : ι → ℝ} (htt : ∀ j ∈ S, t j ≤ t' j) : surrogate E S m t ≤ surrogate E S m t' := by
  rw [le_surrogate_iff hE hS hm, ← Phi_surrogate hE hS hm t]
  unfold Phi
  exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
    (hE.strictMono.monotone (by linarith [htt j hj])) (hm j hj).le

/-- Lemma 5.2(c): exact translation-equivariance. -/
theorem surrogate_shift (hE : IsExpLike E) (hS : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j)
    (t : ι → ℝ) (c : ℝ) : surrogate E S m (fun j => t j + c) = surrogate E S m t + c := by
  symm
  apply surrogate_unique hE hS hm
  rw [← Phi_surrogate hE hS hm t]
  unfold Phi
  exact Finset.sum_congr rfl fun j _ => by ring_nf

end exactness

/-! ### Lemma 5.3 (accuracy) -/

/-- Lemma 5.3.  The hypotheses are those printed in the paper; `η₀ = ε / 4` has been
substituted.  (`K₀ ≥ 0` and `r ≥ 1` are consequences of the hypotheses.) -/
theorem surrogate_accuracy {S : Finset ι} {m : ι → ℝ} (hS : S.Nonempty)
    {ε mSum mmin K0 : ℝ} {r : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hSum : ∑ j ∈ S, m j ≤ mSum) (hmin0 : 0 < mmin) (hmin : ∀ j ∈ S, mmin ≤ m j)
    (hK1 : Real.log (4 * mSum / ε) ≤ K0) (hK2 : Real.log (2 / mmin) ≤ K0)
    (hr1 : 2 * Real.exp 1 * K0 ≤ r + 1) (hr2 : Real.logb 2 (2 / (ε / 4)) ≤ r + 1)
    (t : ι → ℝ) : |surrogate (surE r) S m t - lse S m t| ≤ ε := by
  have hm : ∀ j ∈ S, 0 < m j := fun j hj => hmin0.trans_le (hmin j hj)
  obtain ⟨j0, hj0⟩ := id hS
  have hmSum : mmin ≤ mSum := (hmin j0 hj0).trans
    ((Finset.single_le_sum (f := m) (fun j hj => (hm j hj).le) hj0).trans hSum)
  have hmSpos : 0 < mSum := hmin0.trans_le hmSum
  -- consequences of the hypotheses on K0
  have hK1' : 4 * mSum / ε ≤ Real.exp K0 := (Real.log_le_iff_le_exp (by positivity)).mp hK1
  have hK2' : 2 / mmin ≤ Real.exp K0 := (Real.log_le_iff_le_exp (by positivity)).mp hK2
  have hK0 : 0 ≤ K0 := by
    rcases le_or_gt mmin 2 with h | h
    · refine le_trans (Real.log_nonneg ?_) hK2
      rw [le_div_iff₀ hmin0]; linarith
    · refine le_trans (Real.log_nonneg ?_) hK1
      rw [le_div_iff₀ hε]; nlinarith
  -- r ≥ 1
  have hr : 1 ≤ r := by
    by_contra hcon
    have hr0 : r = 0 := by omega
    subst hr0
    have h1 : (2 : ℝ) ^ (Real.logb 2 (2 / (ε / 4))) = 2 / (ε / 4) :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    have h2 : (2 : ℝ) ^ (Real.logb 2 (2 / (ε / 4))) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa using hr2)
    rw [h1, Real.rpow_one, div_le_iff₀ (by positivity)] at h2
    linarith
  have hE := isExpLike_surE hr
  set η0 := ε / 4 with hη0
  have hη0pos : 0 < η0 := by positivity
  have hPK : (1 - η0) * Real.exp K0 ≤ expPoly r K0 := expPoly_ge hη0pos hr1 hr2 hK0 le_rfl
  have hPKpos : 0 < expPoly r K0 := by linarith [one_le_expPoly r hK0]
  -- pointwise upper bound on E
  have hup : ∀ x : ℝ, (1 - η0) * surE r x ≤ Real.exp x + Real.exp (-K0) := by
    intro x
    have hexp := Real.exp_pos x
    have hexpK := Real.exp_pos (-K0)
    rcases le_or_gt 0 x with hx | hx
    · have := surE_le_exp r hx
      have h0 := surE_pos r x
      nlinarith
    · rw [surE_of_neg r hx]
      have hPpos : 0 < expPoly r (-x) := by linarith [one_le_expPoly r (show (0:ℝ) ≤ -x by linarith)]
      rw [mul_one_div, div_le_iff₀ hPpos]
      rcases le_or_gt (-K0) x with hxK | hxK
      · have h1 := expPoly_ge hη0pos hr1 hr2 (show (0 : ℝ) ≤ -x by linarith) (by linarith)
        have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-x)]
      · have h1 : expPoly r K0 ≤ expPoly r (-x) := expPoly_mono r hK0 (by linarith)
        have h2 : Real.exp (-K0) * Real.exp K0 = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos K0]
  -- pointwise lower bounds on E
  have hlow1 : ∀ x : ℝ, x ≤ K0 → (1 - η0) * Real.exp x ≤ surE r x := by
    intro x hxK
    rcases le_or_gt 0 x with hx | hx
    · rw [surE_of_nonneg r hx]; exact expPoly_ge hη0pos hr1 hr2 hx hxK
    · have := exp_le_surE r hx.le
      nlinarith [Real.exp_pos x]
  have hlow2 : ∀ x : ℝ, K0 < x → (1 - η0) * Real.exp K0 ≤ surE r x := by
    intro x hxK
    rw [surE_of_nonneg r (by linarith)]
    exact hPK.trans (expPoly_mono r hK0 hxK.le)
  -- the sum Σ = ∑ m_j e^{t_j}
  set Sg := ∑ j ∈ S, m j * Real.exp (t j) with hSg
  have hSgpos : 0 < Sg := Finset.sum_pos (fun j hj => mul_pos (hm j hj) (Real.exp_pos _)) hS
  have hsum : ∀ s : ℝ, ∑ j ∈ S, m j * Real.exp (t j - s) = Sg * Real.exp (-s) := by
    intro s
    rw [hSg, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_eq_add_neg, Real.exp_add]; ring
  have hexplog : Real.exp (-(lse S m t)) * Sg = 1 := by
    unfold lse
    rw [Real.exp_neg, Real.exp_log hSgpos, inv_mul_cancel₀ hSgpos.ne']
  rw [abs_le]
  constructor
  · -- lower bound: g ≥ ℓ - ε
    have : lse S m t - ε ≤ surrogate (surE r) S m t := by
      rw [le_surrogate_iff hE hS hm]
      set s := lse S m t - ε with hs
      have hsumε : ∑ j ∈ S, m j * Real.exp (t j - s) = Real.exp ε := by
        rw [hsum, hs, show -(lse S m t - ε) = -(lse S m t) + ε by ring, Real.exp_add]
        calc Sg * (Real.exp (-lse S m t) * Real.exp ε)
            = (Real.exp (-lse S m t) * Sg) * Real.exp ε := by ring
          _ = Real.exp ε := by rw [hexplog, one_mul]
      by_cases hbig : ∃ j ∈ S, K0 < t j - s
      · obtain ⟨j, hj, hjK⟩ := hbig
        have h1 := hlow2 _ hjK
        have h2 : m j * surE r (t j - s) ≤ Phi (surE r) S m t s :=
          Finset.single_le_sum (f := fun j => m j * surE r (t j - s))
            (fun j hj => (mul_pos (hm j hj) (surE_pos r _)).le) hj
        have h3 := hmin j hj
        have h4 : 2 ≤ mmin * Real.exp K0 := by
          rw [div_le_iff₀ hmin0] at hK2'; linarith
        have h5 : 0 ≤ (1 - η0) * Real.exp K0 := by
          have := Real.exp_pos K0; nlinarith
        have h6 : mmin * ((1 - η0) * Real.exp K0) ≤ m j * surE r (t j - s) :=
          mul_le_mul h3 h1 h5 (hm j hj).le
        nlinarith
      · push Not at hbig
        have h1 : (1 - η0) * Real.exp ε ≤ Phi (surE r) S m t s := by
          rw [← hsumε, Finset.mul_sum]
          unfold Phi
          refine Finset.sum_le_sum fun j hj => ?_
          have := hlow1 _ (hbig j hj)
          nlinarith [(hm j hj).le]
        have h2 := Real.add_one_le_exp ε
        nlinarith
    linarith
  · -- upper bound: g ≤ ℓ + ε
    have : surrogate (surE r) S m t ≤ lse S m t + ε := by
      rw [surrogate_le_iff hE hS hm]
      set s := lse S m t + ε with hs
      have hsumε : ∑ j ∈ S, m j * Real.exp (t j - s) = Real.exp (-ε) := by
        rw [hsum, hs, show -(lse S m t + ε) = -(lse S m t) + -ε by ring, Real.exp_add]
        calc Sg * (Real.exp (-lse S m t) * Real.exp (-ε))
            = (Real.exp (-lse S m t) * Sg) * Real.exp (-ε) := by ring
          _ = Real.exp (-ε) := by rw [hexplog, one_mul]
      have h1 : (1 - η0) * Phi (surE r) S m t s ≤ Real.exp (-ε) + mSum * Real.exp (-K0) := by
        calc (1 - η0) * Phi (surE r) S m t s
            = ∑ j ∈ S, m j * ((1 - η0) * surE r (t j - s)) := by
              unfold Phi; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ ∑ j ∈ S, m j * (Real.exp (t j - s) + Real.exp (-K0)) :=
              Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hup _) (hm j hj).le
          _ = Real.exp (-ε) + (∑ j ∈ S, m j) * Real.exp (-K0) := by
              rw [← hsumε, Finset.sum_mul, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ Real.exp (-ε) + mSum * Real.exp (-K0) := by
              have := Real.exp_pos (-K0); nlinarith
      -- mSum e^{-K0} ≤ ε/4
      have h2 : mSum * Real.exp (-K0) ≤ ε / 4 := by
        have hK : Real.exp (-K0) * Real.exp K0 = 1 := by rw [← Real.exp_add]; simp
        rw [div_le_iff₀ hε] at hK1'
        have := Real.exp_pos (-K0)
        nlinarith
      -- e^{-ε} ≤ 1 - ε/2
      have h3 : Real.exp (-ε) ≤ 1 - ε / 2 := by
        have h := Real.add_one_le_exp ε
        have hmul : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
        have := Real.exp_pos (-ε)
        nlinarith
      have h4 : (1 - η0) * Phi (surE r) S m t s ≤ 1 - η0 := by linarith only [h1, h2, h3, hη0]
      have h5 : 0 < 1 - η0 := by linarith only [hη0, hε, hε1]
      exact le_of_mul_le_mul_left (by rw [mul_one]; exact h4) h5
    exact sub_le_iff_le_add'.mpr this

end EntropyGames
