/-
Section 3 and Appendix A of the paper: the imported setting, the witnesses, the text of the
procedure `𝓛` (as a big-step execution relation), and Assumption 3.1 as explicit hypotheses
(`Prop`s).  Nothing in this file is an axiom: `Assumption31a/b/c` are propositions that the
theorems of the project take as hypotheses.
-/
import EntropyGames.Contraction

set_option linter.unusedSectionVars false

namespace EntropyGames

open Classical

/-- Equation (3.1) of the release: `F` monotone, `F (t + c𝟙) = F t + γ c 𝟙`, `0 < γ < 1`.
(`n ≥ 1` is the instance `[Nonempty ι]` where it is needed.) -/
def IsEq31 {ι : Type*} (γ : ℝ) (F : (ι → ℝ) → ι → ℝ) : Prop :=
  IsDiscounted γ F ∧ 0 < γ ∧ γ < 1

/-- An input of the procedure (Equation (3.2) and Definition 3.1 of the release): a corner
`A ∈ ℤ^n`, a width `D = h 2^d` given by the pair `(h, d)`, and mass vectors `a, b`. -/
structure LInput (ι : Type*) where
  A : ι → ℤ
  h : ℕ
  d : ℕ
  a : ι → ℚ
  b : ι → ℚ

namespace LInput

variable {ι : Type*}

/-- The width `D = h 2^d`. -/
def width (I : LInput ι) : ℤ := (I.h : ℤ) * 2 ^ I.d

/-- The upper corner `u = A + D𝟙`. -/
def u (I : LInput ι) : ι → ℤ := fun i => I.A i + I.width

/-- "An input as in Equation (3.2) and Definition 3.1": `128 ≤ h ≤ 255`, `d ≥ 0`, positive
rational masses. -/
structure Valid (I : LInput ι) : Prop where
  h_ge : 128 ≤ I.h
  h_le : I.h ≤ 255
  a_pos : ∀ i, 0 < I.a i
  b_pos : ∀ i, 0 < I.b i

/-- The condition of Step 1 (mass base case): `a_i b_i > 1` for every `i`. -/
def massBase (I : LInput ι) : Prop := ∀ i, 1 < I.a i * I.b i

/-- `c = A + (D/2)𝟙` (an integer vector when `d ≥ 1`). -/
def centre (I : LInput ι) : ι → ℤ := fun i => I.A i + (I.h : ℤ) * 2 ^ (I.d - 1)

/-- `M = D/8` (an integer when `d ≥ 3`). -/
def bigM (I : LInput ι) : ℤ := (I.h : ℤ) * 2 ^ (I.d - 3)

/-- `P = D/32` (an integer when `d ≥ 5`; used as an integer only in nonbase calls). -/
def bigP (I : LInput ι) : ℤ := (I.h : ℤ) * 2 ^ (I.d - 5)

/-- `p = D/4096` (an integer when `d ≥ 12`). -/
def smallp (I : LInput ι) : ℤ := (I.h : ℤ) * 2 ^ (I.d - 12)

/-- The centered call of width `q = D/128 = h 2^{d-7}` at the pivot `k`, with masses `a', b'`:
`𝓛(k - (q/2)𝟙, q, a', b')`. -/
def centredQ (I : LInput ι) (k : ι → ℤ) (a' b' : ι → ℚ) : LInput ι :=
  ⟨fun i => k i - (I.h : ℤ) * 2 ^ (I.d - 8), I.h, I.d - 7, a', b'⟩

/-- The call made in the downward pass (Step 3): masses `(a, (4/3) b)`. -/
def downCall (I : LInput ι) (k : ι → ℤ) : LInput ι := I.centredQ k I.a (fun i => 4 / 3 * I.b i)

/-- The call made in the upward pass (Step 4): masses `((4/3) a, b)`. -/
def upCall (I : LInput ι) (k : ι → ℤ) : LInput ι := I.centredQ k (fun i => 4 / 3 * I.a i) I.b

/-- The update of Step 3; `true` is the label `+`. -/
def downUpdate (I : LInput ι) (k : ι → ℤ) (l : ι → Bool) : ι → ℤ :=
  fun i => if l i then k i else max (I.centre i - I.bigM) (k i - I.smallp)

/-- The update of Step 4. -/
def upUpdate (I : LInput ι) (k : ι → ℤ) (l : ι → Bool) : ι → ℤ :=
  fun i => if l i then min (I.centre i + I.bigM) (k i + I.smallp) else k i

/-- The provisional call of Step 5: centered, width `D/2`, at `k^f`, masses `(a, b)`. -/
def provCall (I : LInput ι) (kf : ι → ℤ) : LInput ι :=
  ⟨fun i => kf i - (I.h : ℤ) * 2 ^ (I.d - 2), I.h, I.d - 1, I.a, I.b⟩

/-- The continuation of Step 6: `𝓛(A, D, ā, b̄)` with the masses of Step 5. -/
def contCall (I : LInput ι) (l0 : ι → Bool) : LInput ι :=
  ⟨I.A, I.h, I.d, fun i => if l0 i then 4 / 5 * I.a i else 8 / 5 * I.a i,
    fun i => if l0 i then 8 / 5 * I.b i else 4 / 5 * I.b i⟩

/-- The overrides of Step 6: `-` on `I_- = {k↓_i < c_i - P}`, `+` on `I_+ \ I_-`,
`I_+ = {k^f_i > c_i + P}`. -/
def override (I : LInput ι) (kdown kf : ι → ℤ) (lc : ι → Bool) : ι → Bool :=
  fun i => if kdown i < I.centre i - I.bigP then false
    else if I.centre i + I.bigP < kf i then true else lc i

/-- The box of `J` lies inside the box of `I`. -/
def BoxIn (J I : LInput ι) : Prop := ∀ i, I.A i ≤ J.A i ∧ J.A i + J.width ≤ I.A i + I.width

end LInput

section witnesses

variable {ι : Type*} [Fintype ι]

/-- Definition 3.1 of the release: plus witness. -/
def IsPlusWitness (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) (y : ι → ℤ) : Prop :=
  (∀ i, I.A i ≤ y i ∧ y i ≤ I.u i) ∧
  (∀ i, I.A i < y i → (y i : ℝ) ≤ F (fun j => (y j : ℝ)) i) ∧
  ∑ i ∈ Finset.univ.filter (fun i => I.A i < y i), I.a i ≤ 1

/-- Definition 3.1 of the release: minus witness. -/
def IsMinusWitness (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) (z : ι → ℤ) : Prop :=
  (∀ i, I.A i ≤ z i ∧ z i ≤ I.u i) ∧
  (∀ i, z i < I.u i → F (fun j => (z j : ℝ)) i ≤ (z i : ℝ)) ∧
  ∑ i ∈ Finset.univ.filter (fun i => z i < I.u i), I.b i ≤ 1

/-- The guarantee of Theorem 3.2 of the release, with `P = D/32` a rational number. -/
def Guarantee (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) (l : ι → Bool) : Prop :=
  (∀ y, IsPlusWitness F I y → ∀ i,
      ((I.A i : ℚ) + I.width - (I.width : ℚ) / 32 ≤ y i) → l i = true) ∧
  (∀ z, IsMinusWitness F I z → ∀ i,
      ((z i : ℚ) ≤ (I.A i : ℚ) + (I.width : ℚ) / 32) → l i = false)

end witnesses

section procedure

variable {ι : Type*}

/-- The map `T(t) = min{u, max{A, ⌊F(t)⌋}}` of Equation (3.3). -/
noncomputable def clipT (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) (t : ι → ℤ) : ι → ℤ :=
  fun i => min (I.u i) (max (I.A i) ⌊F (fun j => (t j : ℝ)) i⌋)

/-- The iteration (3.3): `Iter F I t t* e` says that iterating `T` from `t` stops at the first
fixed point `t*` after `e` evaluations of `⌊F⌋`. -/
inductive Iter (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) : (ι → ℤ) → (ι → ℤ) → ℕ → Prop
  | stop (t : ι → ℤ) (h : clipT F I t = t) : Iter F I t t 1
  | step (t tstar : ι → ℤ) (e : ℕ) (h : clipT F I t ≠ t) (rest : Iter F I (clipT F I t) tstar e) :
      Iter F I t tstar (e + 1)

mutual
  /-- `Run F I l n`: the procedure `𝓛` of Appendix A, run on the input `I` with the map `F`,
  terminates with the label vector `l` (`true` is `+`), and its recursion tree has `n` nodes. -/
  inductive Run (F : (ι → ℝ) → ι → ℝ) : LInput ι → (ι → Bool) → ℕ → Prop
    /-- Step 1, mass base case. -/
    | massBase (I : LInput ι) (hm : I.massBase) : Run F I (fun i => decide (1 < I.b i)) 1
    /-- Step 2, width base case: `+` at `i` when `t*_i > A_i + D/2`. -/
    | widthBase (I : LInput ι) (hm : ¬ I.massBase) (hd : I.d < 12) (tstar : ι → ℤ) (e : ℕ)
        (hit : Iter F I I.u tstar e) :
        Run F I (fun i => decide (2 * I.A i + I.width < 2 * tstar i)) 1
    /-- Steps 3 to 6. -/
    | nonbase (I : LInput ι) (hm : ¬ I.massBase) (hd : 12 ≤ I.d)
        (kdown kf : ι → ℤ) (l0 lc : ι → Bool) (c1 c2 n1 n2 n3 n4 : ℕ)
        (hdown : Down F I I.centre kdown c1 n1) (hup : Up F I kdown kf c2 n2)
        (hprov : Run F (I.provCall kf) l0 n3) (hcont : Run F (I.contCall l0) lc n4) :
        Run F I (I.override kdown kf lc) (1 + n1 + n2 + n3 + n4)
  /-- `Down F I k k↓ c n`: the downward pass of the call `I`, continued from the pivot `k`,
  ends at the pivot `k↓` after `c` centered calls whose trees have `n` nodes in total. -/
  inductive Down (F : (ι → ℝ) → ι → ℝ) : LInput ι → (ι → ℤ) → (ι → ℤ) → ℕ → ℕ → Prop
    | stop (I : LInput ι) (k : ι → ℤ) (l : ι → Bool) (n : ℕ) (hcall : Run F (I.downCall k) l n)
        (hfix : I.downUpdate k l = k) : Down F I k k 1 n
    | step (I : LInput ι) (k kfin : ι → ℤ) (l : ι → Bool) (n c n' : ℕ)
        (hcall : Run F (I.downCall k) l n) (hne : I.downUpdate k l ≠ k)
        (rest : Down F I (I.downUpdate k l) kfin c n') : Down F I k kfin (c + 1) (n + n')
  /-- The upward pass, in the same way. -/
  inductive Up (F : (ι → ℝ) → ι → ℝ) : LInput ι → (ι → ℤ) → (ι → ℤ) → ℕ → ℕ → Prop
    | stop (I : LInput ι) (k : ι → ℤ) (l : ι → Bool) (n : ℕ) (hcall : Run F (I.upCall k) l n)
        (hfix : I.upUpdate k l = k) : Up F I k k 1 n
    | step (I : LInput ι) (k kfin : ι → ℤ) (l : ι → Bool) (n c n' : ℕ)
        (hcall : Run F (I.upCall k) l n) (hne : I.upUpdate k l ≠ k)
        (rest : Up F I (I.upUpdate k l) kfin c n') : Up F I k kfin (c + 1) (n + n')
end

/-- Pivots reached during the downward pass of the call `I`. -/
inductive DownReach (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) : (ι → ℤ) → Prop
  | start : DownReach F I I.centre
  | next {k : ι → ℤ} {l : ι → Bool} {n : ℕ} : DownReach F I k → Run F (I.downCall k) l n →
      DownReach F I (I.downUpdate k l)

/-- Pivots reached during the upward pass of the call `I`. -/
inductive UpReach (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) : (ι → ℤ) → Prop
  | start {kdown : ι → ℤ} {c n : ℕ} : Down F I I.centre kdown c n → UpReach F I kdown
  | next {k : ι → ℤ} {l : ι → Bool} {n : ℕ} : UpReach F I k → Run F (I.upCall k) l n →
      UpReach F I (I.upUpdate k l)

/-- The provisional child of a nonbase call. -/
inductive ProvChild (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) : LInput ι → Prop
  | mk {kdown kf : ι → ℤ} {c1 n1 c2 n2 : ℕ} : Down F I I.centre kdown c1 n1 →
      Up F I kdown kf c2 n2 → ProvChild F I (I.provCall kf)

/-- The other children of a nonbase call: the calls of the two passes and the continuation. -/
inductive OtherChild (F : (ι → ℝ) → ι → ℝ) (I : LInput ι) : LInput ι → Prop
  | down {k : ι → ℤ} : DownReach F I k → OtherChild F I (I.downCall k)
  | up {k : ι → ℤ} : UpReach F I k → OtherChild F I (I.upCall k)
  | cont {kdown kf : ι → ℤ} {c1 n1 c2 n2 n3 : ℕ} {l0 : ι → Bool} :
      Down F I I.centre kdown c1 n1 → Up F I kdown kf c2 n2 → Run F (I.provCall kf) l0 n3 →
      OtherChild F I (I.contCall l0)

end procedure

section rank

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `B(μ) = min {j ≥ 0 : ρ^j μ > 1}`, `ρ = 32/25` (Equation (3.10) of the release). -/
noncomputable def Bfun (μ : ℚ) : ℕ := sInf {j : ℕ | 1 < (32 / 25 : ℚ) ^ j * μ}

/-- `μ(a, b) = min_i a_i b_i`. -/
noncomputable def LInput.mu (I : LInput ι) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => I.a i * I.b i

/-- `B(μ(a, b))`. -/
noncomputable def LInput.B (I : LInput ι) : ℕ := Bfun I.mu

/-- The rank `d + B(μ(a, b))`. -/
noncomputable def LInput.rank (I : LInput ι) : ℕ := I.d + I.B

end rank

section assumption

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- Assumption 3.1(a): for every `F` as in (3.1), `𝓛` terminates on every valid input and its
output has the guarantee of Theorem 3.2 of the release. -/
structure Assumption31a : Prop where
  terminates : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ∃ l n, Run F I l n
  guarantee : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ∀ l n, Run F I l n → Guarantee F I l

/-- Assumption 3.1(b): Lemma 3.4 of the release holds for `𝓛`. -/
structure Assumption31b : Prop where
  /-- "Every child input is valid and its box lies inside its parent's box." -/
  child : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ J, (ProvChild F I J ∨ OtherChild F I J) → J.Valid ∧ J.BoxIn I
  /-- "each pivot pass makes at most `1024 n + 1` calls" (downward pass). -/
  pass_down : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ kdown c n, Down F I I.centre kdown c n →
    c ≤ 1024 * Fintype.card ι + 1
  /-- "each pivot pass makes at most `1024 n + 1` calls" (upward pass). -/
  pass_up : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ kdown c n, Down F I I.centre kdown c n →
    ∀ kf c2 n2, Up F I kdown kf c2 n2 → c2 ≤ 1024 * Fintype.card ι + 1
  /-- "The width base case makes at most `522240 n + 1` evaluations of `⌊F⌋`." -/
  base_evals : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → I.d < 12 → ∀ tstar e, Iter F I I.u tstar e →
    e ≤ 522240 * Fintype.card ι + 1

/-- Assumption 3.1(c): Lemma 3.5 of the release holds for `𝓛`. -/
structure Assumption31c : Prop where
  /-- "The procedure terminates." -/
  terminates : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ∃ l n, Run F I l n
  /-- "At a nonbase call every child has smaller rank." -/
  rank_lt : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ J, (ProvChild F I J ∨ OtherChild F I J) → J.rank < I.rank
  /-- "the provisional call [preserves `B`], and it decreases `d` by one." -/
  prov : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ J, ProvChild F I J → J.B = I.B ∧ J.d + 1 = I.d
  /-- "each [other child] decreases `B` by at least one and does not increase `d`." -/
  other : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ J, OtherChild F I J → J.B + 1 ≤ I.B ∧ J.d ≤ I.d
  /-- "There are at most `2048 n + 3` other children." -/
  other_count : ∀ (γ : ℝ) (F : (ι → ℝ) → ι → ℝ), IsEq31 γ F → ∀ I : LInput ι, I.Valid →
    ¬ I.massBase → 12 ≤ I.d → ∀ kdown c1 n1, Down F I I.centre kdown c1 n1 →
    ∀ kf c2 n2, Up F I kdown kf c2 n2 → c1 + c2 + 1 ≤ 2048 * Fintype.card ι + 3

/-- Assumption 3.1 of the paper. -/
structure Assumption31 : Prop where
  a : Assumption31a ι
  b : Assumption31b ι
  c : Assumption31c ι

end assumption

end EntropyGames
