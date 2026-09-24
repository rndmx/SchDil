import MulticenterTower
import MulticenterMonopoly
import MulticenterNonZeroDivisor
import MulticenterIterate
import Mathlib.RingTheory.Ideal.Quotient.Operations

suppress_compilation

universe u

open Family Multicenter Dilatation

section IdealProd

theorem Ideal.map_finset_prod {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type*} (S : Finset ι) (I : ι → Ideal A) :
    Ideal.map f (∏ s ∈ S, I s) = ∏ s ∈ S, Ideal.map f (I s) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Ideal.one_eq_top]
    exact Ideal.map_top f
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

end IdealProd

namespace Multicenter

section injective

variable {R : Type (u+1)} [CommRing R] (G : Multicenter R)

lemma familyPow_mem_nonZeroDivisors (h : ∀ i, G.elem i ∈ nonZeroDivisors R)
    (β : G.index →₀ ℕ) : G.elem ^ β ∈ nonZeroDivisors R := by
  classical
  simp only [familyPow_def, Finsupp.prod]
  exact prod_mem fun i _ => pow_mem (h i) _

theorem algebraMap_injective_of_elem_nzd (h : ∀ i, G.elem i ∈ nonZeroDivisors R) :
    Function.Injective (algebraMap R R[G]) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [algebraMap_apply, zero_def, mk_eq_mk] at hx
  obtain ⟨β, hβ⟩ := hx
  simp only [add_zero, zero_mul] at hβ
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff
    (G.familyPow_mem_nonZeroDivisors h β)).mp hβ

end injective

section quotCenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) (T : Ideal A)

def quotCenter : Multicenter (A ⧸ T) where
  index := F.index
  ideal i := Ideal.map (Ideal.Quotient.mk T) (F.ideal i)
  elem i := Ideal.Quotient.mk T (F.elem i)

@[simp] lemma quotCenter_index : (F.quotCenter T).index = F.index := rfl

@[simp] lemma quotCenter_ideal (i : F.index) :
    (F.quotCenter T).ideal i = Ideal.map (Ideal.Quotient.mk T) (F.ideal i) := rfl

@[simp] lemma quotCenter_elem (i : F.index) :
    (F.quotCenter T).elem i = Ideal.Quotient.mk T (F.elem i) := rfl

lemma algebraMap_quotCenter (x : A) :
    algebraMap A ((A ⧸ T)[F.quotCenter T]) x =
      algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T]) (Ideal.Quotient.mk T x) := rfl

variable (hT : ∀ i, Ideal.Quotient.mk T (F.elem i) ∈ nonZeroDivisors (A ⧸ T))

lemma quotHom_nzd (i : F.index) :
    algebraMap A ((A ⧸ T)[F.quotCenter T]) (F.elem i) ∈
      nonZeroDivisors ((A ⧸ T)[F.quotCenter T]) := by
  rw [F.algebraMap_quotCenter T]
  have h := Dilatation.nonzerodiv_image (F := F.quotCenter T) (Finsupp.single i 1)
  rw [familyPow_single] at h
  exact h

lemma quotHom_gen (i : F.index) :
    Ideal.span {algebraMap A ((A ⧸ T)[F.quotCenter T]) (F.elem i)} =
      Ideal.map (algebraMap A ((A ⧸ T)[F.quotCenter T])) (F.LargeIdeal i) := by
  refine (gen_iff_le F i).mpr ?_
  have hcomp : (algebraMap A ((A ⧸ T)[F.quotCenter T])) =
      (algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])).comp (Ideal.Quotient.mk T) :=
    RingHom.ext fun x => F.algebraMap_quotCenter T x
  rw [hcomp, ← Ideal.map_map, RingHom.comp_apply]
  exact Multicenter.self_le (F.quotCenter T) i

noncomputable def quotHom : A[F] →ₐ[A] (A ⧸ T)[F.quotCenter T] :=
  desc F (F.quotHom_nzd T) (F.quotHom_gen T)

lemma quotHom_frac_spec (ν : F.index →₀ ℕ) (m : F.LargeIdeal ^ ν) :
    algebraMap A ((A ⧸ T)[F.quotCenter T]) (F.elem ^ ν) *
        F.quotHom T (m /. ν) =
      algebraMap A ((A ⧸ T)[F.quotCenter T]) (m : A) :=
  dsc_spec F ν m (F.quotHom_nzd T) (F.quotHom_gen T)

lemma quotHom_elemPow_nzd (ν : F.index →₀ ℕ) :
    algebraMap A ((A ⧸ T)[F.quotCenter T]) (F.elem ^ ν) ∈
      nonZeroDivisors ((A ⧸ T)[F.quotCenter T]) := by
  classical
  simp only [familyPow_def, Finsupp.prod, map_prod, map_pow]
  exact prod_mem fun i _ => pow_mem (F.quotHom_nzd T i) _

lemma quotCenter_largeIdeal (i : F.index) :
    (F.quotCenter T).LargeIdeal i =
      Ideal.map (Ideal.Quotient.mk T) (F.LargeIdeal i) := by
  show Ideal.map (Ideal.Quotient.mk T) (F.ideal i) +
      Ideal.span {Ideal.Quotient.mk T (F.elem i)} = _
  rw [LargeIdeal, Submodule.add_eq_sup, Submodule.add_eq_sup, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton]

lemma quotCenter_largeIdealPow (ν : (F.quotCenter T).index →₀ ℕ) :
    (ν.prod fun i k => (F.quotCenter T).LargeIdeal i ^ k) =
      Ideal.map (Ideal.Quotient.mk T) (ν.prod fun i k => F.LargeIdeal i ^ k) := by
  classical
  rw [Finsupp.prod, Finsupp.prod, Ideal.map_finset_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Ideal.map_pow, F.quotCenter_largeIdeal T]

lemma quotCenter_elemPow (ν : (F.quotCenter T).index →₀ ℕ) :
    (ν.prod fun i k => (F.quotCenter T).elem i ^ k) =
      Ideal.Quotient.mk T (ν.prod fun i k => F.elem i ^ k) := by
  classical
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm

theorem quotHom_surjective : Function.Surjective (F.quotHom T) := by
  intro y
  induction y using Dilatation.induction_on with
  | h pd =>
    obtain ⟨ν, y', hy'⟩ := pd
    have hy'' : y' ∈ Ideal.map (Ideal.Quotient.mk T)
        (ν.prod fun i k => F.LargeIdeal i ^ k) := by
      rw [← F.quotCenter_largeIdealPow T ν]
      exact hy'
    obtain ⟨ℓ, hℓ, hℓy⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hy''
    refine ⟨Dilatation.frac (F := F) ν ⟨ℓ, hℓ⟩, ?_⟩
    have hnzd : algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])
        (ν.prod fun i k => (F.quotCenter T).elem i ^ k) ∈
        nonZeroDivisors ((A ⧸ T)[F.quotCenter T]) :=
      Dilatation.nonzerodiv_image (F := F.quotCenter T) ν
    have hlhs : algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])
        (ν.prod fun i k => (F.quotCenter T).elem i ^ k) *
        F.quotHom T (Dilatation.frac (F := F) ν ⟨ℓ, hℓ⟩) =
        algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T]) y' := by
      rw [F.quotCenter_elemPow T ν, ← hℓy]
      exact F.quotHom_frac_spec T ν ⟨ℓ, hℓ⟩
    have hrhs : algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])
        (ν.prod fun i k => (F.quotCenter T).elem i ^ k) *
        Dilatation.frac (F := F.quotCenter T) ν ⟨y', hy'⟩ =
        algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T]) y' :=
      ((F.quotCenter T).algebraMap_eq_pow_mul_frac ν y' hy').symm
    exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp (hlhs.trans hrhs.symm)

def kerFracIdeal : Ideal A[F] :=
  Ideal.span {x : A[F] | ∃ (ν : F.index →₀ ℕ) (m : A) (hm : m ∈ F.LargeIdeal ^ ν),
    m ∈ T ∧ x = Dilatation.frac ν ⟨m, hm⟩}

lemma frac_mem_kerFracIdeal (ν : F.index →₀ ℕ) (m : A) (hm : m ∈ F.LargeIdeal ^ ν)
    (hmT : m ∈ T) : Dilatation.frac ν ⟨m, hm⟩ ∈ F.kerFracIdeal T :=
  Ideal.subset_span ⟨ν, m, hm, hmT, rfl⟩

include hT in
theorem ker_quotHom :
    RingHom.ker (F.quotHom T) = F.kerFracIdeal T := by
  have hinj : Function.Injective
      (algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])) :=
    algebraMap_injective_of_elem_nzd _ hT
  refine le_antisymm ?_ ?_
  · intro x hx
    induction x using Dilatation.induction_on with
    | h pd =>
      obtain ⟨ν, ℓ, hℓ⟩ := pd
      have hx0 : F.quotHom T (Dilatation.frac ν ⟨ℓ, hℓ⟩) = 0 := RingHom.mem_ker.mp hx
      have hspec := F.quotHom_frac_spec T ν ⟨ℓ, hℓ⟩
      rw [hx0, mul_zero] at hspec
      have h0 : algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])
          (Ideal.Quotient.mk T ℓ) = 0 := hspec.symm
      have hz : Ideal.Quotient.mk T ℓ = 0 := hinj (by rw [map_zero]; exact h0)
      exact F.frac_mem_kerFracIdeal T ν ℓ hℓ (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · rw [kerFracIdeal, Ideal.span_le]
    rintro x ⟨ν, m, hm, hmT, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hspec := F.quotHom_frac_spec T ν ⟨m, hm⟩
    have hzero : algebraMap A ((A ⧸ T)[F.quotCenter T])
        ((⟨m, hm⟩ : F.LargeIdeal ^ ν) : A) = 0 := by
      show algebraMap (A ⧸ T) ((A ⧸ T)[F.quotCenter T])
        (Ideal.Quotient.mk T m) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmT, map_zero]
    rw [hzero] at hspec
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff
      (F.quotHom_elemPow_nzd T ν)).mp hspec

end quotCenter

end Multicenter
