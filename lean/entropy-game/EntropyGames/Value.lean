/-
Section 2 of the paper: strategies, policies, payments, the value, the part of the cited
existence theorem that the paper uses (as a proposition, to be used as a hypothesis), the
matrices `M^{στ}`, and Lemma 7.1(b).
-/
import EntropyGames.Game

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

variable {D T P : Type*} (Γ : EntropyGame D T P)

/-- A strategy of Despot (Section 2): a move for every history.  A history ending in the Despot
state `d` is given by the list of completed turns and `d`.  Strategies are deterministic and
may depend on the whole history. -/
structure DespotStrategy where
  move : List (D × T × P) → D → T
  legal : ∀ h d, move h d ∈ Γ.outD d

/-- A strategy of Tribune: a move for every history ending in a Tribune state `θ`, given by
the completed turns, the current Despot state and Despot's move `θ`. -/
structure TribuneStrategy where
  move : List (D × T × P) → D → T → P
  legal : ∀ h d θ, move h d θ ∈ Γ.outT θ

/-- A policy of Despot: `σ : D → T` with `(d, σ d) ∈ E`. -/
structure DespotPolicy where
  move : D → T
  legal : ∀ d, move d ∈ Γ.outD d

/-- A policy of Tribune: `τ : T → P` with `(θ, τ θ) ∈ E`. -/
structure TribunePolicy where
  move : T → P
  legal : ∀ θ, move θ ∈ Γ.outT θ

variable {Γ}

/-- A policy as a strategy. -/
def DespotPolicy.toStrategy (σ : DespotPolicy Γ) : DespotStrategy Γ :=
  ⟨fun _ d => σ.move d, fun _ d => σ.legal d⟩

/-- A policy as a strategy. -/
def TribunePolicy.toStrategy (τ : TribunePolicy Γ) : TribuneStrategy Γ :=
  ⟨fun _ _ θ => τ.move θ, fun _ _ θ => τ.legal θ⟩

/-- `R^k_d(σ, τ)` after the history `h`: the sum of the weights of all paths of `k` turns
starting at `d` and compatible with `σ, τ`. -/
noncomputable def pay (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) :
    ℕ → List (D × T × P) → D → ℝ
  | 0, _, _ => 1
  | k + 1, h, d =>
      ∑ d' ∈ Γ.outP (τ.move h d (σ.move h d)),
        Γ.m (τ.move h d (σ.move h d)) d' *
          pay σ τ k (h ++ [(d, σ.move h d, τ.move h d (σ.move h d))]) d'

/-- `R^∞_d(σ, τ) = limsup_k R^k_d(σ, τ)^{1/k}`. -/
noncomputable def payInf (σ : DespotStrategy Γ) (τ : TribuneStrategy Γ) (d : D) : ℝ :=
  Filter.limsup (fun k : ℕ => (pay σ τ k [] d) ^ (1 / (k : ℝ))) Filter.atTop

variable (Γ)

/-- `V` is the value vector: the saddle-point condition of Section 2. -/
def IsValue (V : D → ℝ) : Prop :=
  ∃ (σs : DespotStrategy Γ) (τs : TribuneStrategy Γ), ∀ d (σ : DespotStrategy Γ)
    (τ : TribuneStrategy Γ), V d ≤ payInf σ τs d ∧ payInf σs τ d ≤ V d

/-- The part of the cited existence theorem that the paper uses: `V` is the value and there are
optimal *positional* strategies, optimal against all strategies.  It enters theorems as an
explicit hypothesis. -/
def IsValueWithPolicies (V : D → ℝ) : Prop :=
  ∃ (σs : DespotPolicy Γ) (τs : TribunePolicy Γ), ∀ d (σ : DespotStrategy Γ)
    (τ : TribuneStrategy Γ),
    V d ≤ payInf σ τs.toStrategy d ∧ payInf σs.toStrategy τ d ≤ V d

theorem IsValueWithPolicies.isValue {V : D → ℝ} (h : IsValueWithPolicies Γ V) : IsValue Γ V := by
  obtain ⟨σs, τs, h⟩ := h
  exact ⟨σs.toStrategy, τs.toStrategy, h⟩

/-- The value vector is unique. -/
theorem IsValue.unique {V V' : D → ℝ} (h : IsValue Γ V) (h' : IsValue Γ V') : V = V' := by
  obtain ⟨σs, τs, h⟩ := h
  obtain ⟨σs', τs', h'⟩ := h'
  funext d
  have h1 := (h d σs' τs').1
  have h2 := (h' d σs' τs).2
  have h3 := (h' d σs τs').1
  have h4 := (h d σs τs').2
  have h5 := (h d σs' τs).1
  have h6 := (h' d σs' τs).2
  linarith

/-- The cited existence theorem as a proposition about one game. -/
def ExistenceTheorem : Prop := ∃ V : D → ℝ, IsValueWithPolicies Γ V

/-- The matrix `M^{στ}`. -/
noncomputable def polMatrix [DecidableEq D] (σ : DespotPolicy Γ) (τ : TribunePolicy Γ) :
    D → D → ℝ :=
  fun d d' => if d' ∈ Γ.outP (τ.move (σ.move d)) then Γ.m (τ.move (σ.move d)) d' else 0

/-- Section 2, last display: `R^k_d(σ, τ) = ((M^{στ})^k 𝟙)_d` for policies. -/
theorem pay_policy [Fintype D] [DecidableEq D] (σ : DespotPolicy Γ) (τ : TribunePolicy Γ)
    (k : ℕ) (h : List (D × T × P)) (d : D) :
    pay σ.toStrategy τ.toStrategy k h d
      = ((Matrix.of (polMatrix Γ σ τ)) ^ k).mulVec (fun _ => 1) d := by
  induction k generalizing h d with
  | zero => simp [pay, Matrix.mulVec, dotProduct, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [pay, DespotPolicy.toStrategy, TribunePolicy.toStrategy]
    simp only [DespotPolicy.toStrategy, TribunePolicy.toStrategy] at ih
    simp only [ih]
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.of_apply, polMatrix, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Lemma 7.1(b): the min–max representation of a discounted fixed point.  `y` is the fixed
point of `γ h`, `h_d = min max h_p`, and `y^{στ}` that of `γ h^{στ}`.  The conclusion
`y = min_σ max_τ y^{στ}` is written without `min` and `max`: some `σ` has `y^{στ} ≤ y` for all
`τ`, and every `σ` has some `τ` with `y ≤ y^{στ}` (coordinatewise, with `σ`, `τ` independent
of the coordinate). -/
theorem minmax_fixed_point [Fintype D] {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hp : P → (D → ℝ) → ℝ)
    (hmono : ∀ p, Monotone (hp p))
    (hshift : ∀ p (t : D → ℝ) (c : ℝ), hp p (fun j => t j + c) = hp p t + c)
    {y : D → ℝ} (hy : ∀ d, y d = γ * Γ.minmax (fun p => hp p y) d)
    (ypol : DespotPolicy Γ → TribunePolicy Γ → D → ℝ)
    (hypol : ∀ σ τ d, ypol σ τ d = γ * hp (τ.move (σ.move d)) (ypol σ τ)) :
    (∃ σ : DespotPolicy Γ, ∀ τ : TribunePolicy Γ, ypol σ τ ≤ y) ∧
    (∀ σ : DespotPolicy Γ, ∃ τ : TribunePolicy Γ, y ≤ ypol σ τ) := by
  have hsub : ∀ (σ : DespotPolicy Γ) (τ : TribunePolicy Γ),
      IsSubDiscounted γ (fun t d => γ * hp (τ.move (σ.move d)) t) := by
    intro σ τ
    refine ⟨fun t t' htt d => mul_le_mul_of_nonneg_left (hmono _ htt) hγ0, fun t c _ d => ?_⟩
    simp only [hshift]
    linarith [mul_add γ (hp (τ.move (σ.move d)) t) c]
  have hfix : ∀ σ τ, (fun t d => γ * hp (τ.move (σ.move d)) t) (ypol σ τ) = ypol σ τ :=
    fun σ τ => funext fun d => (hypol σ τ d).symm
  constructor
  · -- σ* attains the minimum at y
    have hex : ∀ d, ∃ θ ∈ Γ.outD d, Γ.minmax (fun p => hp p y) d
        = (Γ.outT θ).sup' (Γ.outT_nonempty θ) (fun p => hp p y) :=
      fun d => Finset.exists_mem_eq_inf' (Γ.outD_nonempty d) _
    choose s hs1 hs2 using hex
    refine ⟨⟨s, hs1⟩, fun τ => ?_⟩
    refine (hsub ⟨s, hs1⟩ τ).fixed_le hγ1 (hfix ⟨s, hs1⟩ τ) fun d => ?_
    simp only
    rw [hy d, hs2 d]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun p => hp p y) (τ.legal (s d))) hγ0
  · intro σ
    have hex : ∀ θ, ∃ p ∈ Γ.outT θ,
        (Γ.outT θ).sup' (Γ.outT_nonempty θ) (fun p => hp p y) = hp p y :=
      fun θ => Finset.exists_mem_eq_sup' (Γ.outT_nonempty θ) _
    choose t ht1 ht2 using hex
    refine ⟨⟨t, ht1⟩, ?_⟩
    refine (hsub σ ⟨t, ht1⟩).le_fixed hγ1 (hfix σ ⟨t, ht1⟩) fun d => ?_
    simp only
    rw [hy d, ← ht2 (σ.move d)]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (σ.legal d)) hγ0

end EntropyGames
