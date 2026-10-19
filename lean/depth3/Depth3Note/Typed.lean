/-
A convenience layer: layered circuits whose gates are indexed by arbitrary finite types, and their
conversion to the release's structure `OAI.Problem335.Depth5Circuit` (gates indexed by `Fin k`,
inputs given as lists). The conversion preserves the polynomial computed, and the size of the
resulting circuit is `N³` (one leaf per variable) plus the number of gates in the four inner layers
plus one.
-/
import Depth3Note.Statements

universe u

namespace Depth3Note

open OAI.Problem335 MvPolynomial Finset

noncomputable section

/-- A layered circuit with typed gates. The leaves are the `N³` variables, no constants; every
bottom sum reads every leaf (coefficient `botCoef`, possibly zero); lower and upper products read
multisets of gates; middle sums and the output read finite sets of gates with coefficients.
`mid_ne`, `mid_hom`, `out_hom` are what syntactic homogeneity in the release's sense requires:
with every bottom sum of formal degree `1`, a lower product has formal degree the number of its
inputs. -/
structure TC (K : Type u) (N : ℕ) (β lam mu ups : Type) where
  botCoef : β → ImmVar N → K
  low : lam → Multiset β
  mid : mu → Finset lam
  midCoef : mu → lam → K
  up : ups → Multiset mu
  out : Finset ups
  outCoef : ups → K
  midDeg : mu → ℕ
  outDeg : ℕ
  mid_ne : ∀ i, (mid i).Nonempty
  mid_hom : ∀ i, ∀ e ∈ mid i, Multiset.card (low e) = midDeg i
  out_hom : ∀ e ∈ out, ((up e).map midDeg).sum = outDeg

theorem toList_map_prod {α M : Type*} [CommMonoid M] (s : Multiset α) (g : α → M) :
    (s.toList.map g).prod = (s.map g).prod := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

theorem toList_map_sum {α M : Type*} [AddCommMonoid M] (s : Multiset α) (g : α → M) :
    (s.toList.map g).sum = (s.map g).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

namespace TC

variable {K : Type u} [CommSemiring K] {N : ℕ} {β lam mu ups : Type}

def botVal (T : TC K N β lam mu ups) (b : β) : MvPolynomial (ImmVar N) K :=
  ∑ v, C (T.botCoef b v) * X v

def lowVal (T : TC K N β lam mu ups) (l : lam) : MvPolynomial (ImmVar N) K :=
  ((T.low l).map T.botVal).prod

def midVal (T : TC K N β lam mu ups) (m : mu) : MvPolynomial (ImmVar N) K :=
  ∑ e ∈ T.mid m, C (T.midCoef m e) * T.lowVal e

def upVal (T : TC K N β lam mu ups) (u : ups) : MvPolynomial (ImmVar N) K :=
  ((T.up u).map T.midVal).prod

def value (T : TC K N β lam mu ups) : MvPolynomial (ImmVar N) K :=
  ∑ e ∈ T.out, C (T.outCoef e) * T.upVal e

variable [Fintype β] [Fintype lam] [Fintype mu] [Fintype ups]

/-- Conversion to the release's structure. -/
def toD5 (T : TC K N β lam mu ups) (hN : 0 < N) : Depth5Circuit K N where
  leafCount := Fintype.card (ImmVar N)
  leaves := fun i => D5Leaf.variable ((Fintype.equivFin (ImmVar N)).symm i)
  bottomCount := Fintype.card β
  bottomInputs := fun i => (univ : Finset (ImmVar N)).toList.map
    (fun v => (T.botCoef ((Fintype.equivFin β).symm i) v, Fintype.equivFin (ImmVar N) v))
  bottomDegree := fun _ => 1
  bottomHomogeneous := by
    intro i entry _
    rfl
  bottomEmpty := by
    intro i h
    exfalso
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hne : (univ : Finset (ImmVar N)).Nonempty := univ_nonempty
    rw [List.map_eq_nil_iff, Finset.toList_eq_nil] at h
    exact hne.ne_empty h
  lowerCount := Fintype.card lam
  lowerInputs := fun i =>
    ((T.low ((Fintype.equivFin lam).symm i)).map (Fintype.equivFin β)).toList
  middleCount := Fintype.card mu
  middleInputs := fun i => (T.mid ((Fintype.equivFin mu).symm i)).toList.map
    (fun e => (T.midCoef ((Fintype.equivFin mu).symm i) e, Fintype.equivFin lam e))
  middleDegree := fun i => T.midDeg ((Fintype.equivFin mu).symm i)
  middleHomogeneous := by
    intro i entry h
    rw [List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    simp only [Equiv.symm_apply_apply, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
      Multiset.length_toList, Multiset.card_map]
    exact T.mid_hom _ e (Finset.mem_toList.1 he)
  middleEmpty := by
    intro i h
    exfalso
    rw [List.map_eq_nil_iff, Finset.toList_eq_nil] at h
    exact (T.mid_ne _).ne_empty h
  upperCount := Fintype.card ups
  upperInputs := fun i =>
    ((T.up ((Fintype.equivFin ups).symm i)).map (Fintype.equivFin mu)).toList
  outputInputs := T.out.toList.map (fun e => (T.outCoef e, Fintype.equivFin ups e))
  outputDegree := if T.out.card = 0 then 0 else T.outDeg
  outputHomogeneous := by
    intro entry h
    rw [List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    have he' : e ∈ T.out := Finset.mem_toList.1 he
    have hc : T.out.card ≠ 0 := Finset.card_ne_zero.2 ⟨e, he'⟩
    simp only [Equiv.symm_apply_apply]
    rw [toList_map_sum, Multiset.map_map, if_neg hc, ← T.out_hom e he']
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  outputEmpty := by
    intro h
    rw [List.map_eq_nil_iff, Finset.toList_eq_nil] at h
    simp [h]

variable (T : TC K N β lam mu ups) (hN : 0 < N)

theorem bottomValue_toD5 (i) :
    bottomValue (T.toD5 hN) i = T.botVal ((Fintype.equivFin β).symm i) := by
  simp only [bottomValue, toD5, botVal, List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp [d5LeafValue]

theorem lowerValue_toD5 (i) :
    lowerValue (T.toD5 hN) i = T.lowVal ((Fintype.equivFin lam).symm i) := by
  have hb : (fun j => bottomValue (T.toD5 hN) j) =
      fun j => T.botVal ((Fintype.equivFin β).symm j) := funext (bottomValue_toD5 T hN)
  simp only [lowerValue, hb]
  simp only [toD5, lowVal]
  rw [toList_map_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp

theorem middleValue_toD5 (i) :
    middleValue (T.toD5 hN) i = T.midVal ((Fintype.equivFin mu).symm i) := by
  simp only [middleValue, lowerValue_toD5]
  simp only [toD5, midVal, List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp

theorem upperValue_toD5 (i) :
    upperValue (T.toD5 hN) i = T.upVal ((Fintype.equivFin ups).symm i) := by
  have hb : (fun j => middleValue (T.toD5 hN) j) =
      fun j => T.midVal ((Fintype.equivFin mu).symm j) := funext (middleValue_toD5 T hN)
  simp only [upperValue, hb]
  simp only [toD5, upVal]
  rw [toList_map_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp

theorem circuitValue_toD5 : circuitValue (T.toD5 hN) = T.value := by
  simp only [circuitValue, upperValue_toD5]
  simp only [toD5, value, List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp

theorem circuitSize_toD5 :
    circuitSize (T.toD5 hN) =
      N ^ 3 + Fintype.card β + Fintype.card lam + Fintype.card mu + Fintype.card ups + 1 := by
  simp only [circuitSize, toD5, ImmVar, Fintype.card_prod, Fintype.card_fin]
  ring

end TC

end

end Depth3Note
