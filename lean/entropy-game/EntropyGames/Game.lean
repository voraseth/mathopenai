/-
Section 2 (the model, operators in logarithmic coordinates) and Section 5 (Definition 5.4,
Proposition 5.5) of the paper.
-/
import EntropyGames.Contraction
import EntropyGames.Surrogate

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

/-- The arena of an entropy game (Section 2): Despot states `D`, Tribune states `T`, People
states `P`; arcs go `D → T → P → D`; every node has at least one outgoing arc; a positive
weight is attached to every arc from `P` to `D`. -/
structure EntropyGame (D T P : Type*) where
  outD : D → Finset T
  outT : T → Finset P
  outP : P → Finset D
  outD_nonempty : ∀ d, (outD d).Nonempty
  outT_nonempty : ∀ θ, (outT θ).Nonempty
  outP_nonempty : ∀ p, (outP p).Nonempty
  m : P → D → ℝ
  m_pos : ∀ p d, d ∈ outP p → 0 < m p d

variable {D T P : Type*} (Γ : EntropyGame D T P)

namespace EntropyGame

/-- `min` over Despot's moves of `max` over Tribune's moves of a quantity attached to People
states. -/
noncomputable def minmax (h : P → ℝ) (d : D) : ℝ :=
  (Γ.outD d).inf' (Γ.outD_nonempty d) fun θ => (Γ.outT θ).sup' (Γ.outT_nonempty θ) h

/-- `ℓ_p(t)`. -/
noncomputable def ell (p : P) (t : D → ℝ) : ℝ := lse (Γ.outP p) (Γ.m p) t

/-- Equation (2.2): `f = log ∘ 𝓕 ∘ exp`, written as `min max ℓ_p`. -/
noncomputable def f (t : D → ℝ) (d : D) : ℝ := Γ.minmax (fun p => Γ.ell p t) d

/-- `g_p(t)` for the function `E`. -/
noncomputable def g (E : ℝ → ℝ) (p : P) (t : D → ℝ) : ℝ := surrogate E (Γ.outP p) (Γ.m p) t

/-- Definition 5.4: `f̃`. -/
noncomputable def ft (E : ℝ → ℝ) (t : D → ℝ) (d : D) : ℝ := Γ.minmax (fun p => Γ.g E p t) d

/-- Definition 5.4: `G(t) = γ f̃(δ t) / δ`, `γ = 1 - 1/N`. -/
noncomputable def G (E : ℝ → ℝ) (δ : ℝ) (N : ℕ) (t : D → ℝ) (d : D) : ℝ :=
  (1 - 1 / (N : ℝ)) * Γ.ft E (fun j => δ * t j) d / δ

theorem minmax_mono {h h' : P → ℝ} (hh : ∀ p, h p ≤ h' p) (d : D) :
    Γ.minmax h d ≤ Γ.minmax h' d := by
  unfold minmax
  rw [Finset.le_inf'_iff]
  intro θ hθ
  refine (Finset.inf'_le _ hθ).trans ?_
  rw [Finset.sup'_le_iff]
  intro p hp
  exact (hh p).trans (Finset.le_sup' h' hp)

theorem minmax_add_const (h : P → ℝ) (c : ℝ) (d : D) :
    Γ.minmax (fun p => h p + c) d = Γ.minmax h d + c := by
  unfold minmax
  have h1 : ∀ θ, (Γ.outT θ).sup' (Γ.outT_nonempty θ) (fun p => h p + c)
      = (Γ.outT θ).sup' (Γ.outT_nonempty θ) h + c := by
    intro θ
    exact (Finset.apply_sup'_eq_sup'_comp (Γ.outT_nonempty θ) (fun x => x + c)
      (fun x y => (max_add_add_right x y c).symm)).symm
  simp only [h1]
  exact (Finset.apply_inf'_eq_inf'_comp (Γ.outD_nonempty d) (fun x => x + c)
      (fun x y => (min_add_add_right x y c).symm)).symm

theorem minmax_le_of_le {h : P → ℝ} {b : ℝ} (hh : ∀ p, h p ≤ b) (d : D) : Γ.minmax h d ≤ b := by
  unfold minmax
  obtain ⟨θ, hθ⟩ := Γ.outD_nonempty d
  refine (Finset.inf'_le _ hθ).trans ?_
  rw [Finset.sup'_le_iff]
  exact fun p _ => hh p

theorem le_minmax_of_le {h : P → ℝ} {a : ℝ} (hh : ∀ p, a ≤ h p) (d : D) : a ≤ Γ.minmax h d := by
  unfold minmax
  rw [Finset.le_inf'_iff]
  intro θ _
  obtain ⟨p, hp⟩ := Γ.outT_nonempty θ
  exact (hh p).trans (Finset.le_sup' h hp)

/-- `min max` is nonexpansive for the sup norm. -/
theorem abs_minmax_sub_le {h h' : P → ℝ} {ε : ℝ} (hh : ∀ p, |h p - h' p| ≤ ε) (d : D) :
    |Γ.minmax h d - Γ.minmax h' d| ≤ ε := by
  rw [abs_le]
  constructor
  · have := Γ.minmax_mono (h := h') (h' := fun p => h p + ε)
      (fun p => by have := (abs_le.mp (hh p)).1; linarith) d
    rw [minmax_add_const] at this
    linarith
  · have := Γ.minmax_mono (h := h) (h' := fun p => h' p + ε)
      (fun p => by have := (abs_le.mp (hh p)).2; linarith) d
    rw [minmax_add_const] at this
    linarith

variable {E : ℝ → ℝ}

/-- Proposition 5.5(a), first half: `f̃` is monotone. -/
theorem ft_mono (hE : IsExpLike E) : Monotone (Γ.ft E) := by
  intro t t' htt d
  exact Γ.minmax_mono (fun p => surrogate_mono hE (Γ.outP_nonempty p) (Γ.m_pos p)
    (fun j _ => htt j)) d

/-- Proposition 5.5(a), first half: `f̃(t + c𝟙) = f̃(t) + c𝟙`. -/
theorem ft_shift (hE : IsExpLike E) (t : D → ℝ) (c : ℝ) :
    Γ.ft E (fun j => t j + c) = fun d => Γ.ft E t d + c := by
  funext d
  unfold ft g
  rw [← minmax_add_const]
  congr 1
  funext p
  exact surrogate_shift hE (Γ.outP_nonempty p) (Γ.m_pos p) t c

/-- Proposition 5.5(a): `G` satisfies Equation (4.1) exactly. -/
theorem G_isDiscounted (hE : IsExpLike E) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 2 ≤ N) :
    IsDiscounted (1 - 1 / (N : ℝ)) (Γ.G E δ N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hγ : 0 ≤ 1 - 1 / (N : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  constructor
  · intro t t' htt d
    unfold G
    have := Γ.ft_mono hE (a := fun j => δ * t j) (b := fun j => δ * t' j)
      (fun j => mul_le_mul_of_nonneg_left (htt j) hδ.le) d
    gcongr
  · intro t c
    funext d
    unfold G
    have h1 : (fun j => δ * (t j + c)) = fun j => δ * t j + δ * c := by funext j; ring
    rw [h1, Γ.ft_shift hE]
    field_simp

/-- Proposition 5.5(b): if every `g_p` is within `ε` of `ℓ_p`, then `‖f̃(t) - f(t)‖_∞ ≤ ε`. -/
theorem abs_ft_sub_f_le {ε : ℝ} (t : D → ℝ) (hacc : ∀ p, |Γ.g E p t - Γ.ell p t| ≤ ε) (d : D) :
    |Γ.ft E t d - Γ.f t d| ≤ ε :=
  Γ.abs_minmax_sub_le hacc d

/-- Proposition 5.5(b) with the hypotheses of Lemma 5.3 for every `p`. -/
theorem abs_ft_sub_f_le' {ε mSum mmin K0 : ℝ} {r : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hSum : ∀ p, ∑ j ∈ Γ.outP p, Γ.m p j ≤ mSum) (hmin0 : 0 < mmin)
    (hmin : ∀ p, ∀ j ∈ Γ.outP p, mmin ≤ Γ.m p j)
    (hK1 : Real.log (4 * mSum / ε) ≤ K0) (hK2 : Real.log (2 / mmin) ≤ K0)
    (hr1 : 2 * Real.exp 1 * K0 ≤ r + 1) (hr2 : Real.logb 2 (2 / (ε / 4)) ≤ r + 1)
    (t : D → ℝ) (d : D) : |Γ.ft (surE r) t d - Γ.f t d| ≤ ε :=
  Γ.abs_ft_sub_f_le t (fun p => surrogate_accuracy (Γ.outP_nonempty p) hε hε1 (hSum p) hmin0
    (hmin p) hK1 hK2 hr1 hr2 t) d

/-- Proposition 5.5(c): the exact test for `G_d(t) ≥ k`.  (The paper states it for integer
`t` and `k`; it holds for real ones.) -/
theorem le_G_iff (hE : IsExpLike E) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 2 ≤ N)
    (t : D → ℝ) (k : ℝ) (d : D) :
    k ≤ Γ.G E δ N t d ↔ ∀ θ ∈ Γ.outD d, ∃ p ∈ Γ.outT θ,
      1 ≤ ∑ j ∈ Γ.outP p, Γ.m p j * E (δ * (t j - k * N / (N - 1))) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hγ : 1 - 1 / (N : ℝ) = (N - 1) / N := by field_simp
  have h1 : k ≤ Γ.G E δ N t d ↔ δ * (k * N / (N - 1)) ≤ Γ.ft E (fun j => δ * t j) d := by
    unfold G
    rw [hγ, le_div_iff₀ hδ, div_mul_eq_mul_div, le_div_iff₀ (by linarith),
      mul_div_assoc', div_le_iff₀ hN1]
    constructor <;> intro h <;> nlinarith
  rw [h1]
  unfold ft minmax
  rw [Finset.le_inf'_iff]
  refine forall₂_congr fun θ _ => ?_
  rw [Finset.le_sup'_iff]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  unfold g
  rw [le_surrogate_iff hE (Γ.outP_nonempty p) (Γ.m_pos p)]
  unfold Phi
  have : ∀ j, δ * t j - δ * (k * N / (N - 1)) = δ * (t j - k * N / (N - 1)) := fun j => by ring
  simp only [this]

/-- Bounds on `ℓ_p` used in Proposition 5.5(d). -/
theorem ell_le {Ω : ℝ} (hΩ : ∀ p, ∑ j ∈ Γ.outP p, Γ.m p j ≤ Real.exp Ω) (p : P) (y : D → ℝ)
    {ymax : ℝ} (hy : ∀ j, y j ≤ ymax) : Γ.ell p y ≤ ymax + Ω := by
  unfold ell lse
  have hpos : 0 < ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (y j) :=
    Finset.sum_pos (fun j hj => mul_pos (Γ.m_pos p j hj) (Real.exp_pos _)) (Γ.outP_nonempty p)
  rw [Real.log_le_iff_le_exp hpos, Real.exp_add]
  calc ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (y j)
      ≤ ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp ymax :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (hy j)) (Γ.m_pos p j hj).le
    _ = (∑ j ∈ Γ.outP p, Γ.m p j) * Real.exp ymax := by rw [Finset.sum_mul]
    _ ≤ Real.exp Ω * Real.exp ymax := mul_le_mul_of_nonneg_right (hΩ p) (Real.exp_pos _).le
    _ = Real.exp ymax * Real.exp Ω := mul_comm _ _

theorem le_ell {Ω : ℝ} (hΩ : ∀ p, ∀ j ∈ Γ.outP p, Real.exp (-Ω) ≤ Γ.m p j) (p : P) (y : D → ℝ)
    {ymin : ℝ} (hy : ∀ j, ymin ≤ y j) : ymin - Ω ≤ Γ.ell p y := by
  unfold ell lse
  have hpos : 0 < ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (y j) :=
    Finset.sum_pos (fun j hj => mul_pos (Γ.m_pos p j hj) (Real.exp_pos _)) (Γ.outP_nonempty p)
  rw [Real.le_log_iff_exp_le hpos, sub_eq_add_neg, Real.exp_add]
  obtain ⟨j0, hj0⟩ := Γ.outP_nonempty p
  calc Real.exp ymin * Real.exp (-Ω) ≤ Real.exp (y j0) * Γ.m p j0 :=
        mul_le_mul (Real.exp_le_exp.mpr (hy j0)) (hΩ p j0 hj0) (Real.exp_pos _).le
          (Real.exp_pos _).le
    _ = Γ.m p j0 * Real.exp (y j0) := mul_comm _ _
    _ ≤ _ := Finset.single_le_sum (f := fun j => Γ.m p j * Real.exp (y j))
        (fun j hj => (mul_pos (Γ.m_pos p j hj) (Real.exp_pos _)).le) hj0

/-- Proposition 5.5(d).  The accuracy hypothesis `‖f̃ - f‖ ≤ ε` (part (b)) is used in the proof
and is therefore a hypothesis here; the paper's statement of (d) does not repeat it. -/
theorem G_bounds {Ω ε δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 2 ≤ N)
    (hΩ1 : ∀ p, ∑ j ∈ Γ.outP p, Γ.m p j ≤ Real.exp Ω)
    (hΩ2 : ∀ p, ∀ j ∈ Γ.outP p, Real.exp (-Ω) ≤ Γ.m p j)
    (hacc : ∀ p (y : D → ℝ), |Γ.g E p y - Γ.ell p y| ≤ ε)
    (t : D → ℝ) {tmin tmax : ℝ} (hmin : ∀ j, tmin ≤ t j) (hmax : ∀ j, t j ≤ tmax) (d : D) :
    (1 - 1 / (N : ℝ)) * (tmin - (Ω + ε) / δ) ≤ Γ.G E δ N t d ∧
      Γ.G E δ N t d ≤ (1 - 1 / (N : ℝ)) * (tmax + (Ω + ε) / δ) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hγ : 0 ≤ 1 - 1 / (N : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hlo : δ * tmin - Ω - ε ≤ Γ.ft E (fun j => δ * t j) d := by
    refine Γ.le_minmax_of_le (fun p => ?_) d
    have h1 := Γ.le_ell hΩ2 p (fun j => δ * t j) (ymin := δ * tmin)
      (fun j => mul_le_mul_of_nonneg_left (hmin j) hδ.le)
    have h2 := (abs_le.mp (hacc p (fun j => δ * t j))).1
    linarith
  have hhi : Γ.ft E (fun j => δ * t j) d ≤ δ * tmax + Ω + ε := by
    refine Γ.minmax_le_of_le (fun p => ?_) d
    have h1 := Γ.ell_le hΩ1 p (fun j => δ * t j) (ymax := δ * tmax)
      (fun j => mul_le_mul_of_nonneg_left (hmax j) hδ.le)
    have h2 := (abs_le.mp (hacc p (fun j => δ * t j))).2
    linarith
  unfold G
  constructor
  · rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ
    rw [le_div_iff₀ hδ]
    have : (tmin - (Ω + ε) / δ) * δ = δ * tmin - Ω - ε := by field_simp; ring
    linarith
  · rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ
    rw [div_le_iff₀ hδ]
    have : (tmax + (Ω + ε) / δ) * δ = δ * tmax + Ω + ε := by field_simp; ring
    linarith

end EntropyGame

end EntropyGames
