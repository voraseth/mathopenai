/-
Section 2 of the paper, paragraph "Normalisation": multiplying all weights by a constant
`c > 0` multiplies every `R^k_d` by `c^k` and hence every `R^∞_d` and the value by `c`.
-/
import EntropyGames.Value

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

variable {D T P : Type*} (Γ : EntropyGame D T P)

/-- The game with all weights multiplied by `c > 0`. -/
def scale (c : ℝ) (hc : 0 < c) : EntropyGame D T P :=
  { Γ with m := fun p d => c * Γ.m p d, m_pos := fun p d hd => mul_pos hc (Γ.m_pos p d hd) }

variable {Γ} {c : ℝ} (hc : 0 < c)

/-- A strategy of Despot in the scaled game is a strategy in the game (same arcs). -/
def DespotStrategy.unscale (σ : DespotStrategy (scale Γ c hc)) : DespotStrategy Γ :=
  ⟨σ.move, σ.legal⟩

/-- A strategy of Tribune in the scaled game is a strategy in the game (same arcs). -/
def TribuneStrategy.unscale (τ : TribuneStrategy (scale Γ c hc)) : TribuneStrategy Γ :=
  ⟨τ.move, τ.legal⟩

/-- A strategy of Despot in the game is a strategy in the scaled game. -/
def DespotStrategy.scale (σ : DespotStrategy Γ) : DespotStrategy (scale Γ c hc) :=
  ⟨σ.move, σ.legal⟩

/-- A strategy of Tribune in the game is a strategy in the scaled game. -/
def TribuneStrategy.scale (τ : TribuneStrategy Γ) : TribuneStrategy (scale Γ c hc) :=
  ⟨τ.move, τ.legal⟩

theorem pay_nonneg (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) :
    ∀ (k : ℕ) (h : List (D × T × P)) (d : D), 0 ≤ pay σ τ k h d
  | 0, _, _ => by simp [pay]
  | k + 1, h, d => by
    simp only [pay]
    exact Finset.sum_nonneg fun d' hd' =>
      mul_nonneg (Γ.m_pos _ _ hd').le (pay_nonneg σ τ k _ d')

/-- `R^k_d` is multiplied by `c^k`. -/
theorem pay_scale (σ : DespotStrategy (scale Γ c hc)) (τ : TribuneStrategy (scale Γ c hc)) :
    ∀ (k : ℕ) (h : List (D × T × P)) (d : D),
      pay σ τ k h d = c ^ k * pay (σ.unscale hc) (τ.unscale hc) k h d
  | 0, _, _ => by simp [pay]
  | k + 1, h, d => by
    simp only [pay]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d' _ => ?_
    rw [pay_scale σ τ k]
    simp only [scale, DespotStrategy.unscale, TribuneStrategy.unscale]
    ring

/-- `limsup (c u) = c limsup u` for `c > 0` (with Lean's conventions for unbounded `u`). -/
theorem limsup_const_mul' {c : ℝ} (hc : 0 < c) (u : ℕ → ℝ) :
    Filter.limsup (fun k => c * u k) Filter.atTop = c * Filter.limsup u Filter.atTop := by
  rw [Filter.limsup_eq, Filter.limsup_eq, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hc.le]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
  constructor
  · intro h
    refine ⟨a / c, ?_, by field_simp⟩
    filter_upwards [h] with n hn
    rw [le_div_iff₀ hc]
    linarith
  · rintro ⟨b, hb, rfl⟩
    filter_upwards [hb] with n hn
    exact mul_le_mul_of_nonneg_left hn hc.le

/-- `R^∞_d` is multiplied by `c`. -/
theorem payInf_scale (σ : DespotStrategy (scale Γ c hc)) (τ : TribuneStrategy (scale Γ c hc))
    (d : D) : payInf σ τ d = c * payInf (σ.unscale hc) (τ.unscale hc) d := by
  unfold payInf
  rw [← limsup_const_mul' hc]
  refine Filter.limsup_congr ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [pay_scale hc σ τ k, Real.mul_rpow (pow_pos hc k).le (pay_nonneg _ _ k _ d),
    ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  have hk' : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [mul_one_div_cancel hk', Real.rpow_one]

variable (Γ)

/-- Section 2, "Normalisation": multiplying the weights by `c` multiplies the value by `c`. -/
theorem isValue_scale (c : ℝ) (hc : 0 < c) (V : D → ℝ) (hV : IsValue Γ V) :
    IsValue (scale Γ c hc) (fun d => c * V d) := by
  obtain ⟨σs, τs, h⟩ := hV
  refine ⟨σs.scale hc, τs.scale hc, fun d σ τ => ?_⟩
  rw [payInf_scale hc, payInf_scale hc]
  have h1 := h d (σ.unscale hc) (τ.unscale hc)
  exact ⟨mul_le_mul_of_nonneg_left h1.1 hc.le, mul_le_mul_of_nonneg_left h1.2 hc.le⟩

/-- Section 2, "Normalisation", as it is used: if `V` is the value of the game and `V'` the
value of the game with all weights divided by the threshold `r > 0`, then `V'_d ≥ 1` exactly
when `V_d ≥ r`.  So deciding the normalised game at threshold `1` decides the given game at
threshold `r`. -/
theorem threshold_scale {r : ℝ} (hr : 0 < r) {V V' : D → ℝ} (hV : IsValue Γ V)
    (hV' : IsValue (scale Γ (1 / r) (one_div_pos.mpr hr)) V') (d : D) :
    1 ≤ V' d ↔ r ≤ V d := by
  have h := IsValue.unique _ hV' (isValue_scale Γ (1 / r) (one_div_pos.mpr hr) V hV)
  rw [h]
  simp only
  rw [one_div_mul_eq_div, le_div_iff₀ hr, one_mul]

/-! ### Boundedness of `(R^k)^{1/k}`

With finitely many People states the sequence `k ↦ R^k_d(σ, τ)^{1/k}` is bounded, for all
strategies; so `payInf`, which is Lean's `Filter.limsup`, is the limsup in the usual sense
(Lean's `limsup` of a real sequence has a default value when the sequence is unbounded). -/

section bounded

variable {D T P : Type*} [Fintype P] {Γ : EntropyGame D T P}

/-- The sum of all weights. -/
noncomputable def weightSum (Γ : EntropyGame D T P) : ℝ := ∑ p, ∑ d ∈ Γ.outP p, Γ.m p d

theorem weightSum_nonneg (Γ : EntropyGame D T P) : 0 ≤ weightSum Γ :=
  Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun d hd => (Γ.m_pos p d hd).le

theorem pay_le_pow (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) :
    ∀ (k : ℕ) (h : List (D × T × P)) (d : D), pay σ τ k h d ≤ weightSum Γ ^ k
  | 0, _, _ => by simp [pay]
  | k + 1, h, d => by
    simp only [pay]
    have hS := weightSum_nonneg Γ
    have hrow : ∀ p, ∑ d' ∈ Γ.outP p, Γ.m p d' ≤ weightSum Γ := fun p =>
      Finset.single_le_sum (f := fun p => ∑ d' ∈ Γ.outP p, Γ.m p d')
        (fun p _ => Finset.sum_nonneg fun d hd => (Γ.m_pos p d hd).le) (Finset.mem_univ p)
    calc _ ≤ ∑ d' ∈ Γ.outP (τ.move h d (σ.move h d)),
            Γ.m (τ.move h d (σ.move h d)) d' * weightSum Γ ^ k :=
          Finset.sum_le_sum fun d' hd' =>
            mul_le_mul_of_nonneg_left (pay_le_pow σ τ k _ d') (Γ.m_pos _ _ hd').le
      _ = (∑ d' ∈ Γ.outP (τ.move h d (σ.move h d)), Γ.m (τ.move h d (σ.move h d)) d')
            * weightSum Γ ^ k := (Finset.sum_mul _ _ _).symm
      _ ≤ weightSum Γ * weightSum Γ ^ k :=
          mul_le_mul_of_nonneg_right (hrow _) (pow_nonneg hS k)
      _ = weightSum Γ ^ (k + 1) := (pow_succ' _ _).symm

/-- `0 ≤ R^k_d(σ, τ)^{1/k} ≤ S` for `k ≥ 1`, `S` the sum of all weights. -/
theorem pay_rpow_bounds (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) (d : D) {k : ℕ}
    (hk : 1 ≤ k) :
    0 ≤ pay σ τ k [] d ^ (1 / (k : ℝ)) ∧ pay σ τ k [] d ^ (1 / (k : ℝ)) ≤ weightSum Γ := by
  have h0 := pay_nonneg σ τ k [] d
  refine ⟨Real.rpow_nonneg h0 _, ?_⟩
  have h1 := Real.rpow_le_rpow h0 (pay_le_pow σ τ k [] d)
    (show (0 : ℝ) ≤ 1 / (k : ℝ) by positivity)
  rw [one_div] at h1 ⊢
  rwa [Real.pow_rpow_inv_natCast (weightSum_nonneg Γ) (by omega)] at h1

/-- The sequence whose limsup is `R^∞_d(σ, τ)` is bounded above and below. -/
theorem payInf_bounded (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) (d : D) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun k : ℕ => pay σ τ k [] d ^ (1 / (k : ℝ))) ∧
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun k : ℕ => pay σ τ k [] d ^ (1 / (k : ℝ))) := by
  constructor
  · refine ⟨weightSum Γ, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact (pay_rpow_bounds σ τ d hk).2
  · refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact (pay_rpow_bounds σ τ d hk).1

end bounded

end EntropyGames
