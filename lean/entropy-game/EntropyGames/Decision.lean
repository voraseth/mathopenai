/-
Sections 7 and 8 of the paper: Lemma 7.1(d), and the correctness part of the proof of
Theorem 1.1, conditional on
  * Assumption 3.1(a) (explicit hypothesis `hA`), and
  * three facts about the numbers `χ_d` that are proved in the paper in Lemma 6.1(a),
    Lemma 7.1(a),(c) (which rests on Theorem 6.2 and on the cited existence theorem) and
    Lemma 7.2; here they are explicit hypotheses `hχ`, `hdisc`, `hsep`.
-/
import EntropyGames.Game
import EntropyGames.Localisation

set_option linter.unusedSectionVars false

namespace EntropyGames

open Finset

namespace EntropyGame

variable {D T P : Type*} (Γ : EntropyGame D T P)

theorem ell_sum_pos (p : P) (t : D → ℝ) : 0 < ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (t j) :=
  Finset.sum_pos (fun j hj => mul_pos (Γ.m_pos p j hj) (Real.exp_pos _)) (Γ.outP_nonempty p)

theorem ell_mono (p : P) : Monotone (Γ.ell p) := by
  intro t t' htt
  unfold ell lse
  refine Real.log_le_log (Γ.ell_sum_pos p t) ?_
  exact Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (htt j)) (Γ.m_pos p j hj).le

theorem ell_shift (p : P) (t : D → ℝ) (c : ℝ) : Γ.ell p (fun j => t j + c) = Γ.ell p t + c := by
  unfold ell lse
  have h1 : ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (t j + c)
      = Real.exp c * ∑ j ∈ Γ.outP p, Γ.m p j * Real.exp (t j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.exp_add]; ring
  rw [h1, Real.log_mul (Real.exp_pos c).ne' (Γ.ell_sum_pos p t).ne', Real.log_exp]
  ring

theorem f_mono : Monotone Γ.f := fun _ _ htt d => Γ.minmax_mono (fun p => Γ.ell_mono p htt) d

theorem f_shift (t : D → ℝ) (c : ℝ) : Γ.f (fun j => t j + c) = fun d => Γ.f t d + c := by
  funext d
  unfold f
  rw [← minmax_add_const]
  congr 1
  funext p
  exact Γ.ell_shift p t c

/-- `γ f̃` satisfies (4.1). -/
theorem gft_isDiscounted {E : ℝ → ℝ} (hE : IsExpLike E) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsDiscounted γ (fun t d => γ * Γ.ft E t d) := by
  constructor
  · intro t t' htt d
    exact mul_le_mul_of_nonneg_left (Γ.ft_mono hE htt d) hγ
  · intro t c
    funext d
    simp only [Γ.ft_shift hE]
    ring

/-- `γ f` satisfies (4.1). -/
theorem gf_isDiscounted {γ : ℝ} (hγ : 0 ≤ γ) : IsDiscounted γ (fun t d => γ * Γ.f t d) := by
  constructor
  · intro t t' htt d
    exact mul_le_mul_of_nonneg_left (Γ.f_mono htt d) hγ
  · intro t c
    funext d
    simp only [Γ.f_shift]
    ring

/-- Lemma 7.1(d): if `‖f̃ - f‖_∞ ≤ ε`, `y` is the fixed point of `γ f̃` and `v` that of `γ f`,
then `(1 - γ) ‖y - v‖_∞ ≤ γ ε` (so `θ ‖y - v‖_∞ ≤ ε`). -/
theorem fixed_points_close [Finite D] {E : ℝ → ℝ} {ε γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hacc : ∀ t d, |Γ.ft E t d - Γ.f t d| ≤ ε) {y v : D → ℝ}
    (hy : ∀ d, y d = γ * Γ.ft E y d) (hv : ∀ d, v d = γ * Γ.f v d) (d : D) :
    (1 - γ) * |y d - v d| ≤ γ * ε := by
  haveI : Nonempty D := ⟨d⟩
  obtain ⟨d0, hd0⟩ := Finite.exists_max (fun d => |y d - v d|)
  set c := |y d0 - v d0| with hc
  have hle1 : y ≤ fun j => v j + c := fun j => by
    have : |y j - v j| ≤ c := hd0 j
    linarith [le_abs_self (y j - v j)]
  have hle2 : v ≤ fun j => y j + c := fun j => by
    have : |y j - v j| ≤ c := hd0 j
    linarith [neg_abs_le (y j - v j)]
  have h1 : Γ.f y d0 ≤ Γ.f v d0 + c := by
    have := Γ.f_mono hle1 d0
    rwa [Γ.f_shift] at this
  have h2 : Γ.f v d0 ≤ Γ.f y d0 + c := by
    have := Γ.f_mono hle2 d0
    rwa [Γ.f_shift] at this
  have h3 := abs_le.mp (hacc y d0)
  have habs : |Γ.ft E y d0 - Γ.f v d0| ≤ ε + c := by
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]
  have hceq : |y d0 - v d0| = γ * |Γ.ft E y d0 - Γ.f v d0| := by
    conv_lhs => rw [hy d0, hv d0]
    rw [← mul_sub, abs_mul, abs_of_nonneg hγ0]
  have hmain : c ≤ γ * (ε + c) := by
    calc c = |y d0 - v d0| := hc
      _ = γ * |Γ.ft E y d0 - Γ.f v d0| := hceq
      _ ≤ γ * (ε + c) := mul_le_mul_of_nonneg_left habs hγ0
  have hdc : |y d - v d| ≤ c := hd0 d
  nlinarith

end EntropyGame

/-- **Correctness of the threshold decision** (the "Correctness" paragraph of the proof of
Theorem 1.1), conditional on Assumption 3.1(a) and on the three facts `hχ`, `hdisc`, `hsep`
about the numbers `χ_d` (see the header of this file).

`H`, `Ωh`, `N`, `r` are the parameters of Section 8; `ε = 1/(64H)`, `δ = 1/(2^15 H)`,
`K = 256(N+1)`, `J = 2^15 H N (Ωh + 1) + N + 1`; `v` is the fixed point of `γ f`.
The conclusion: the loop of Proposition 4.3 terminates after at most `128 (d₀ + 1)` calls of
`𝓛`, and for its result `A`, `A_d ≥ -2^13 N` if and only if `χ_d ≥ 0`. -/
theorem decision_correct {D T P : Type*} [Fintype D] [Nonempty D] (Γ : EntropyGame D T P)
    (hA : Assumption31a D) {N H Ωh r : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H) (hr : 1 ≤ r)
    (hacc : ∀ t d, |Γ.ft (surE r) t d - Γ.f t d| ≤ 1 / (64 * (H : ℝ)))
    {R : ℝ} (hR : R / N ≤ 1 / (64 * (H : ℝ)))
    {v χ : D → ℝ} (hv : ∀ d, v d = (1 - 1 / (N : ℝ)) * Γ.f v d)
    (hχ : ∀ d, |χ d| ≤ Ωh) (hdisc : ∀ d, |v d / N - χ d| ≤ R / N)
    (hsep : ∀ d, χ d < 0 → χ d ≤ -1 / (H : ℝ))
    {d0 : ℕ} (hd0 : 2 * ((2 ^ 15 * H * N * (Ωh + 1) + N + 1 : ℕ) : ℤ) ≤ 128 * 2 ^ d0) :
    (∃ Afin c, Loop (Γ.G (surE r) (1 / (2 ^ 15 * (H : ℝ))) N) (256 * (N + 1))
        (fun _ => -((2 ^ 15 * H * N * (Ωh + 1) + N + 1 : ℕ) : ℤ)) 128 d0 Afin c) ∧
    ∀ Afin c, Loop (Γ.G (surE r) (1 / (2 ^ 15 * (H : ℝ))) N) (256 * (N + 1))
        (fun _ => -((2 ^ 15 * H * N * (Ωh + 1) + N + 1 : ℕ) : ℤ)) 128 d0 Afin c →
      c ≤ 128 * (d0 + 1) ∧ ∀ d, (-(2 ^ 13 * (N : ℤ)) ≤ Afin d ↔ 0 ≤ χ d) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hNpos : (0 : ℝ) < N := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  set γ : ℝ := 1 - 1 / (N : ℝ) with hγdef
  have hθ : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]; linarith
  have hθpos : 0 < 1 / (N : ℝ) := by positivity
  have hγ0 : 0 ≤ γ := by linarith
  have hγ1 : γ < 1 := by linarith
  set δ : ℝ := 1 / (2 ^ 15 * (H : ℝ)) with hδdef
  have hδ : 0 < δ := by positivity
  have hE := isExpLike_surE hr
  have hG := Γ.G_isDiscounted hE hδ hN
  -- the fixed point y of γ f̃ and the fixed point x = y / δ of G
  have hgft := Γ.gft_isDiscounted hE hγ0
  obtain ⟨y, hy, _⟩ := hgft.existsUnique_fixed hγ0 hγ1
  have hy' : ∀ d, y d = γ * Γ.ft (surE r) y d := fun d => (congrFun hy d).symm
  set x : D → ℝ := fun d => y d / δ with hxdef
  have hx : Γ.G (surE r) δ N x = x := by
    funext d
    unfold EntropyGame.G
    have h1 : (fun j => δ * x j) = y := by
      funext j; simp only [hxdef]; field_simp
    rw [h1, ← hγdef, ← hy' d]
  -- Lemma 7.1(d)
  have hclose : ∀ d, |y d - v d| / N ≤ 1 / (64 * (H : ℝ)) := by
    intro d
    have h := Γ.fixed_points_close hγ0 hγ1.le hacc hy' hv d
    have h1 : 1 - γ = 1 / (N : ℝ) := by rw [hγdef]; ring
    rw [h1] at h
    have h2 : γ * (1 / (64 * (H : ℝ))) ≤ 1 / (64 * (H : ℝ)) :=
      mul_le_of_le_one_left (by positivity) hγ1.le
    calc |y d - v d| / N = 1 / (N : ℝ) * |y d - v d| := by ring
      _ ≤ _ := h.trans h2
  -- |θ y_d - χ_d| ≤ 1/(32H)
  have hyχ : ∀ d, |y d / N - χ d| ≤ 1 / (32 * (H : ℝ)) := by
    intro d
    have h1 : y d / N - χ d = (y d - v d) / N + (v d / N - χ d) := by ring
    have h2 : |(y d - v d) / N| = |y d - v d| / N := by
      rw [abs_div, abs_of_pos hNpos]
    calc |y d / N - χ d| ≤ |(y d - v d) / N| + |v d / N - χ d| := by rw [h1]; exact abs_add_le _ _
      _ ≤ 1 / (64 * (H : ℝ)) + 1 / (64 * (H : ℝ)) := by
          rw [h2]; exact add_le_add (hclose d) ((hdisc d).trans hR)
      _ = 1 / (32 * (H : ℝ)) := by field_simp; ring
  have h32 : 1 / (32 * (H : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  -- ‖x‖ + N + 1 ≤ J
  have hJ : ∀ d, |x d| + N + 1 ≤ ((2 ^ 15 * H * N * (Ωh + 1) + N + 1 : ℕ) : ℤ) := by
    intro d
    have h1 := abs_le.mp (hyχ d)
    have h2 := abs_le.mp (hχ d)
    have h3 : |y d / N| ≤ Ωh + 1 := by
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have h4 : |y d| ≤ N * ((Ωh : ℝ) + 1) := by
      rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos] at h3
      linarith
    have h5 : |x d| = 2 ^ 15 * (H : ℝ) * |y d| := by
      simp only [hxdef, hδdef]
      rw [div_div_eq_mul_div, div_one, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 15 * H)]
      ring
    have h6 : 2 ^ 15 * (H : ℝ) * |y d| ≤ 2 ^ 15 * (H : ℝ) * (N * ((Ωh : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [h5]
    push_cast
    linarith
  obtain ⟨hex, hall⟩ := localisation hA hN hG hx hJ hd0
  refine ⟨hex, fun Afin c hloop => ?_⟩
  obtain ⟨hc, hloc⟩ := hall Afin c hloop
  refine ⟨hc, fun d => ?_⟩
  obtain ⟨hlo, hhi⟩ := hloc d
  have h1 := abs_le.mp (hyχ d)
  -- T = N 2^15 H ; x_d = T (y_d / N)
  have hxd : x d = (N : ℝ) * 2 ^ 15 * H * (y d / N) := by
    simp only [hxdef, hδdef]; field_simp
  have hT : (0 : ℝ) < (N : ℝ) * 2 ^ 15 * H := by positivity
  have hT32 : (N : ℝ) * 2 ^ 15 * H * (1 / (32 * (H : ℝ))) = N * 2 ^ 10 := by
    field_simp; norm_num
  have hup : (N : ℝ) * 2 ^ 15 * H * (y d / N) ≤ (N : ℝ) * 2 ^ 15 * H * (χ d + 1 / (32 * (H : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith [h1.2]) hT.le
  have hdn : (N : ℝ) * 2 ^ 15 * H * (χ d - 1 / (32 * (H : ℝ))) ≤ (N : ℝ) * 2 ^ 15 * H * (y d / N) :=
    mul_le_mul_of_nonneg_left (by linarith [h1.1]) hT.le
  rw [mul_add, hT32] at hup
  rw [mul_sub, hT32] at hdn
  push_cast at hhi
  constructor
  · intro hA13
    by_contra hneg
    rw [not_le] at hneg
    have hs := hsep d hneg
    have h2 : (N : ℝ) * 2 ^ 15 * H * χ d ≤ (N : ℝ) * 2 ^ 15 * H * (-1 / (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hs hT.le
    have h3 : (N : ℝ) * 2 ^ 15 * H * (-1 / (H : ℝ)) = -(N * 2 ^ 15) := by field_simp
    have h4 : (-(2 ^ 13 * (N : ℤ)) : ℝ) ≤ (Afin d : ℝ) := by exact_mod_cast hA13
    push_cast at h4
    nlinarith
  · intro hpos
    have h2 : 0 ≤ (N : ℝ) * 2 ^ 15 * H * χ d := mul_nonneg hT.le hpos
    have h4 : ((-(2 ^ 13 * (N : ℤ)) : ℤ) : ℝ) ≤ (Afin d : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h4

end EntropyGames
