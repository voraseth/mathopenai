/-
Section 4 of the paper: Proposition 4.3 (fixed-point localisation), proved from
Assumption 3.1(a) only.  The assumption is the explicit hypothesis `hA`.
-/
import EntropyGames.Procedure

set_option linter.unusedSectionVars false

namespace EntropyGames

open Classical

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The permitted width `h 2^d`. -/
def wd (h d : ℕ) : ℤ := (h : ℤ) * 2 ^ d

/-- The predecessor of the permitted width `h 2^d`: `(h-1) 2^d` if `h > 128`, and
`255 · 2^{d-1}` if `h = 128`. -/
def predHD (h d : ℕ) : ℕ × ℕ := if 128 < h then (h - 1, d) else (255, d - 1)

/-- The input `(A, h 2^d, a, b)` with `a_i = b_i = 1/n` used by the loop. -/
def loopInput (ι : Type*) [Fintype ι] (A : ι → ℤ) (h d : ℕ) : LInput ι :=
  ⟨A, h, d, fun _ => 1 / (Fintype.card ι : ℚ), fun _ => 1 / (Fintype.card ι : ℚ)⟩

/-- One update of the loop of Proposition 4.3: `A_i` becomes `A_i + (D - D')` where `ℓ_i = +`. -/
def loopStep (A : ι → ℤ) (h d : ℕ) (l : ι → Bool) : ι → ℤ :=
  fun i => if l i then A i + (wd h d - wd (predHD h d).1 (predHD h d).2) else A i

/-- The loop of Proposition 4.3, as an execution relation: `Loop F K A h d A' c` says that the
loop started in the state `(A, D = h 2^d)` ends with the corner `A'` after `c` calls of `𝓛`. -/
inductive Loop (F : (ι → ℝ) → ι → ℝ) (K : ℤ) : (ι → ℤ) → ℕ → ℕ → (ι → ℤ) → ℕ → Prop
  | done (A : ι → ℤ) (h d : ℕ) (hK : wd h d ≤ K) : Loop F K A h d A 0
  | step (A : ι → ℤ) (h d : ℕ) (l : ι → Bool) (n : ℕ) (Afin : ι → ℤ) (c : ℕ) (hK : K < wd h d)
      (hrun : Run F (loopInput ι A h d) l n)
      (rest : Loop F K (loopStep A h d l) (predHD h d).1 (predHD h d).2 Afin c) :
      Loop F K A h d Afin (c + 1)

/-- Facts on the predecessor width (the paragraph before Proposition 4.3). -/
theorem predHD_facts {h d : ℕ} (hh : 128 ≤ h ∧ h ≤ 255) {K : ℤ} (hK : 768 ≤ K)
    (hKw : K < wd h d) :
    (128 ≤ (predHD h d).1 ∧ (predHD h d).1 ≤ 255) ∧
    0 < wd h d - wd (predHD h d).1 (predHD h d).2 ∧
    128 * (wd h d - wd (predHD h d).1 (predHD h d).2) ≤ wd h d ∧
    128 * (predHD h d).2 + (predHD h d).1 + 1 = 128 * d + h := by
  unfold predHD
  have h2pos : (0 : ℤ) < 2 ^ d := by positivity
  split_ifs with hcase
  · refine ⟨⟨by omega, by omega⟩, ?_, ?_, by omega⟩
    · simp only [wd]
      have : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
      rw [this]; nlinarith
    · simp only [wd]
      have : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
      rw [this]
      have : (128 : ℤ) ≤ h := by omega
      nlinarith
  · have h128 : h = 128 := by omega
    subst h128
    have hd : 1 ≤ d := by
      by_contra hcon
      have : d = 0 := by omega
      subst this
      simp [wd] at hKw
      omega
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hepos : (0 : ℤ) < 2 ^ e := by positivity
    refine ⟨⟨by omega, by omega⟩, ?_, ?_, by simp; omega⟩
    · simp only [wd, Nat.add_sub_cancel, pow_succ]; push_cast; nlinarith
    · simp only [wd, Nat.add_sub_cancel, pow_succ]; push_cast; nlinarith

/-- One iteration of the loop preserves the invariant `A ≤ Y`, `Z ≤ A + D𝟙` (the core of the
proof of Proposition 4.3). -/
theorem loopStep_invariant (hA : Assumption31a ι) {γ : ℝ} {F : (ι → ℝ) → ι → ℝ}
    (hF : IsEq31 γ F) {Y Z : ι → ℤ}
    (hY : ∀ i, (Y i : ℝ) ≤ F (fun j => (Y j : ℝ)) i)
    (hZ : ∀ i, F (fun j => (Z j : ℝ)) i ≤ (Z i : ℝ))
    (hYZ : ∀ i, Y i ≤ Z i) {K : ℤ} (hK : 768 ≤ K) (hgap : ∀ i, 128 * (Z i - Y i) ≤ K)
    {A : ι → ℤ} {h d : ℕ} (hh : 128 ≤ h ∧ h ≤ 255) (hAY : ∀ i, A i ≤ Y i)
    (hZu : ∀ i, Z i ≤ A i + wd h d) (hKw : K < wd h d) {l : ι → Bool} {n : ℕ}
    (hrun : Run F (loopInput ι A h d) l n) :
    (∀ i, loopStep A h d l i ≤ Y i) ∧
    (∀ i, Z i ≤ loopStep A h d l i + wd (predHD h d).1 (predHD h d).2) := by
  have hcard : (0 : ℚ) < (Fintype.card ι : ℚ) := by exact_mod_cast Fintype.card_pos
  have hvalid : (loopInput ι A h d).Valid :=
    ⟨hh.1, hh.2, fun _ => by simp only [loopInput]; positivity,
      fun _ => by simp only [loopInput]; positivity⟩
  have hG := hA.guarantee γ F hF _ hvalid l n hrun
  have hmass : ∀ s : Finset ι, ∑ _i ∈ s, (1 / (Fintype.card ι : ℚ)) ≤ 1 := by
    intro s
    calc ∑ _i ∈ s, (1 / (Fintype.card ι : ℚ)) ≤ ∑ _i ∈ (Finset.univ : Finset ι), (1 / (Fintype.card ι : ℚ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard.ne']
  have hplus : IsPlusWitness F (loopInput ι A h d) Y :=
    ⟨fun i => ⟨hAY i, (hYZ i).trans (hZu i)⟩, fun i _ => hY i, hmass _⟩
  have hminus : IsMinusWitness F (loopInput ι A h d) Z :=
    ⟨fun i => ⟨(hAY i).trans (hYZ i), hZu i⟩, fun i _ => hZ i, hmass _⟩
  obtain ⟨_, hδpos, hδ, _⟩ := predHD_facts hh hK hKw
  set W := wd h d with hW
  set W' := wd (predHD h d).1 (predHD h d).2 with hW'
  have hWq : ((loopInput ι A h d).width : ℚ) = (W : ℚ) := rfl
  have hAq : ∀ i, (loopInput ι A h d).A i = A i := fun _ => rfl
  have key : ∀ i, loopStep A h d l i ≤ Y i ∧ Z i ≤ loopStep A h d l i + W' := by
    intro i
    have hg := hgap i
    have hgq : (128 : ℚ) * ((Z i : ℚ) - Y i) ≤ K := by exact_mod_cast hg
    have hKq : (K : ℚ) < W := by exact_mod_cast hKw
    have hδq : (128 : ℚ) * ((W : ℚ) - W') ≤ W := by exact_mod_cast hδ
    have hWpos : (0 : ℚ) < W := by
      have : (0 : ℤ) < W := by linarith
      exact_mod_cast this
    unfold loopStep
    cases hl : l i with
    | true =>
      simp only [if_true]
      have h1 : ¬ ((Z i : ℚ) ≤ (A i : ℚ) + (W : ℚ) / 32) := by
        intro hcon
        have := hG.2 Z hminus i (by rw [hWq, hAq]; exact hcon)
        rw [hl] at this
        exact Bool.noConfusion this
      rw [not_le] at h1
      constructor
      · have : ((A i + (W - W') : ℤ) : ℚ) ≤ (Y i : ℚ) := by push_cast; linarith
        exact_mod_cast this
      · have := hZu i
        linarith
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have h1 : ¬ ((A i : ℚ) + W - (W : ℚ) / 32 ≤ (Y i : ℚ)) := by
        intro hcon
        have := hG.1 Y hplus i (by rw [hWq, hAq]; exact hcon)
        rw [hl] at this
        exact Bool.noConfusion this
      rw [not_le] at h1
      refine ⟨hAY i, ?_⟩
      have : (Z i : ℚ) ≤ ((A i + W' : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

/-- Partial correctness and the bound on the number of calls, for any run of the loop. -/
theorem Loop.spec (hA : Assumption31a ι) {γ : ℝ} {F : (ι → ℝ) → ι → ℝ}
    (hF : IsEq31 γ F) {Y Z : ι → ℤ}
    (hY : ∀ i, (Y i : ℝ) ≤ F (fun j => (Y j : ℝ)) i)
    (hZ : ∀ i, F (fun j => (Z j : ℝ)) i ≤ (Z i : ℝ))
    (hYZ : ∀ i, Y i ≤ Z i) {K : ℤ} (hK : 768 ≤ K) (hgap : ∀ i, 128 * (Z i - Y i) ≤ K)
    {A : ι → ℤ} {h d : ℕ} {Afin : ι → ℤ} {c : ℕ} (hloop : Loop F K A h d Afin c) :
    (128 ≤ h ∧ h ≤ 255) → (∀ i, A i ≤ Y i) → (∀ i, Z i ≤ A i + wd h d) →
    c + 128 ≤ 128 * d + h ∧ (∀ i, Afin i ≤ Y i) ∧ (∀ i, Z i ≤ Afin i + K) := by
  induction hloop with
  | done A h d hKw =>
    intro hh hAY hZu
    exact ⟨by omega, hAY, fun i => by have := hZu i; linarith⟩
  | step A h d l n Afin c hKw hrun _ ih =>
    intro hh hAY hZu
    obtain ⟨h1, h2⟩ := loopStep_invariant hA hF hY hZ hYZ hK hgap hh hAY hZu hKw hrun
    obtain ⟨hh', _, _, hmeas⟩ := predHD_facts hh hK hKw
    obtain ⟨hc, r2, r3⟩ := ih hh' h1 h2
    exact ⟨by omega, r2, r3⟩

/-- The loop terminates (given that `𝓛` terminates, Assumption 3.1(a)). -/
theorem Loop.exists (hA : Assumption31a ι) {γ : ℝ} {F : (ι → ℝ) → ι → ℝ}
    (hF : IsEq31 γ F) {Y Z : ι → ℤ}
    (hY : ∀ i, (Y i : ℝ) ≤ F (fun j => (Y j : ℝ)) i)
    (hZ : ∀ i, F (fun j => (Z j : ℝ)) i ≤ (Z i : ℝ))
    (hYZ : ∀ i, Y i ≤ Z i) {K : ℤ} (hK : 768 ≤ K) (hgap : ∀ i, 128 * (Z i - Y i) ≤ K) :
    ∀ (m : ℕ) (A : ι → ℤ) (h d : ℕ), 128 * d + h = m → (128 ≤ h ∧ h ≤ 255) →
      (∀ i, A i ≤ Y i) → (∀ i, Z i ≤ A i + wd h d) → ∃ Afin c, Loop F K A h d Afin c := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A h d hm hh hAY hZu
    by_cases hKw : wd h d ≤ K
    · exact ⟨A, 0, Loop.done A h d hKw⟩
    · rw [not_le] at hKw
      have hcard : (0 : ℚ) < (Fintype.card ι : ℚ) := by exact_mod_cast Fintype.card_pos
      have hvalid : (loopInput ι A h d).Valid :=
        ⟨hh.1, hh.2, fun _ => by simp only [loopInput]; positivity,
          fun _ => by simp only [loopInput]; positivity⟩
      obtain ⟨l, n, hrun⟩ := hA.terminates γ F hF _ hvalid
      obtain ⟨h1, h2⟩ := loopStep_invariant hA hF hY hZ hYZ hK hgap hh hAY hZu hKw hrun
      obtain ⟨hh', _, _, hmeas⟩ := predHD_facts hh hK hKw
      obtain ⟨Afin, c, hrest⟩ := ih (128 * (predHD h d).2 + (predHD h d).1) (by omega)
        (loopStep A h d l) _ _ rfl hh' h1 h2
      exact ⟨Afin, c + 1, Loop.step A h d l n Afin c hKw hrun hrest⟩

/-- **Proposition 4.3 (localisation).**  Assume Assumption 3.1(a).  Let `G` satisfy (4.1) with
`γ = 1 - 1/N`, `N ≥ 2`, with fixed point `x`; let `J` be an integer with `‖x‖_∞ + N + 1 ≤ J`,
`K = 256 (N + 1)`, and `128 · 2^{d₀} ≥ 2J`.  Then the loop started with `A = -J𝟙`,
`D = 128 · 2^{d₀}` terminates, makes at most `128 (d₀ + 1)` calls of `𝓛`, and ends with
`A ∈ ℤ^n`, `A_i ≤ x_i ≤ A_i + K`. -/
theorem localisation (hA : Assumption31a ι) {N : ℕ} (hN : 2 ≤ N) {G : (ι → ℝ) → ι → ℝ}
    (hG : IsDiscounted (1 - 1 / (N : ℝ)) G) {x : ι → ℝ} (hx : G x = x) {J : ℤ}
    (hJ : ∀ i, |x i| + N + 1 ≤ J) {d0 : ℕ} (hd0 : 2 * J ≤ 128 * 2 ^ d0) :
    (∃ Afin c, Loop G (256 * (N + 1)) (fun _ => -J) 128 d0 Afin c) ∧
    ∀ Afin c, Loop G (256 * (N + 1)) (fun _ => -J) 128 d0 Afin c →
      c ≤ 128 * (d0 + 1) ∧ ∀ i, (Afin i : ℝ) ≤ x i ∧ x i ≤ (Afin i : ℝ) + (256 * (N + 1) : ℤ) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hF : IsEq31 (1 - 1 / (N : ℝ)) G := by
    refine ⟨hG, ?_, ?_⟩
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
    · have : 0 < 1 / (N : ℝ) := by positivity
      linarith
  obtain ⟨hY, hZ, hYx, hxZ, hZY⟩ := comparison_vectors hN hG hx
  set Y : ι → ℤ := fun i => ⌊x i⌋ - N with hYdef
  set Z : ι → ℤ := fun i => ⌈x i⌉ + N with hZdef
  have hYZ : ∀ i, Y i ≤ Z i := fun i => by
    have : (Y i : ℝ) ≤ Z i := (hYx i).trans (hxZ i)
    exact_mod_cast this
  have hK : (768 : ℤ) ≤ 256 * (N + 1) := by
    have : (2 : ℤ) ≤ N := by exact_mod_cast hN
    linarith
  have hgap : ∀ i, 128 * (Z i - Y i) ≤ (256 * (N + 1) : ℤ) := fun i => by
    have := hZY i; linarith
  have hAY : ∀ i, (fun _ : ι => -J) i ≤ Y i := fun i => by
    have h1 := hJ i
    have h2 := Int.lt_floor_add_one (x i)
    have h3 := neg_abs_le (x i)
    have : ((-J : ℤ) : ℝ) < ((Y i + 1 : ℤ) : ℝ) := by
      simp only [hYdef]; push_cast; linarith
    have : -J < Y i + 1 := by exact_mod_cast this
    simp only; omega
  have hZu : ∀ i, Z i ≤ (fun _ : ι => -J) i + wd 128 d0 := fun i => by
    have h1 := hJ i
    have h2 := Int.ceil_lt_add_one (x i)
    have h3 := le_abs_self (x i)
    have : ((Z i : ℤ) : ℝ) < ((J : ℤ) : ℝ) := by
      simp only [hZdef]; push_cast; linarith
    have : Z i < J := by exact_mod_cast this
    simp only [wd]; push_cast; linarith
  constructor
  · exact Loop.exists hA hF hY hZ hYZ hK hgap _ _ _ _ rfl ⟨le_rfl, by norm_num⟩ hAY hZu
  · intro Afin c hloop
    obtain ⟨hc, r2, r3⟩ := Loop.spec hA hF hY hZ hYZ hK hgap hloop ⟨le_rfl, by norm_num⟩ hAY hZu
    refine ⟨by omega, fun i => ⟨?_, ?_⟩⟩
    · have : (Afin i : ℝ) ≤ Y i := by exact_mod_cast r2 i
      exact this.trans (hYx i)
    · have : (Z i : ℝ) ≤ ((Afin i + 256 * (N + 1) : ℤ) : ℝ) := by exact_mod_cast r3 i
      push_cast at this ⊢
      linarith [hxZ i]

end EntropyGames
