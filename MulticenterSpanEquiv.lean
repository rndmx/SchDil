import MulticenterTower
import MulticenterMonopoly

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)
  (e : F.index → A)

def elemReplace : Multicenter A where
  index := F.index
  ideal := F.ideal
  elem := e

@[simp] lemma elemReplace_index : (F.elemReplace e).index = F.index := rfl
@[simp] lemma elemReplace_ideal (i : F.index) : (F.elemReplace e).ideal i = F.ideal i := rfl
@[simp] lemma elemReplace_elem (i : F.index) : (F.elemReplace e).elem i = e i := rfl

variable (hspan : ∀ i, Ideal.span {e i} = Ideal.span {F.elem i})

include hspan in
lemma span_algebraMap_eq {B : Type (u+1)} [CommRing B] [Algebra A B] (i : F.index) :
    Ideal.span {algebraMap A B (e i)} = Ideal.span {algebraMap A B (F.elem i)} := by
  have h := congrArg (Ideal.map (algebraMap A B)) (hspan i)
  rwa [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at h

include hspan in
lemma elemReplace_elem_nzd (i : F.index) :
    algebraMap A A[F.elemReplace e] (F.elem i) ∈
      nonZeroDivisors A[F.elemReplace e] := by
  have hmem : e i ∈ Ideal.span {F.elem i} := by
    rw [← hspan i]; exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h := nonzerodiv_image_single (F.elemReplace e) i
  rw [elemReplace_elem, ← hc, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

include hspan in
lemma elem_nzd_in_elemReplace (i : F.index) :
    algebraMap A A[F] (e i) ∈ nonZeroDivisors A[F] := by
  have hmem : F.elem i ∈ Ideal.span {e i} := by
    rw [hspan i]; exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h := nonzerodiv_image_single F i
  rw [← hc, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

include hspan in
def toElemReplace : A[F] →ₐ[A] A[F.elemReplace e] :=
  desc F (F.elemReplace_elem_nzd e hspan)
    (fun i => (gen_iff_le F i).mpr (by
      exact le_trans (Multicenter.self_le (F.elemReplace e) i)
        (le_of_eq (F.span_algebraMap_eq e hspan i))))

include hspan in
def fromElemReplace : A[F.elemReplace e] →ₐ[A] A[F] :=
  desc (F.elemReplace e) (fun i => F.elem_nzd_in_elemReplace e hspan i)
    (fun i => (gen_iff_le (F.elemReplace e) i).mpr (by
      exact le_trans (Multicenter.self_le F i)
        (le_of_eq (F.span_algebraMap_eq e hspan i).symm)))

include hspan in
theorem fromElemReplace_comp_toElemReplace :
    (F.fromElemReplace e hspan).comp (F.toElemReplace e hspan) = AlgHom.id A A[F] :=
  lemma_exists_unique_morphism' F (fun i => nonzerodiv_image_single F i)
    (fun i => reciprocal_for_univ F (AlgHom.id A A[F]) i) _ _

include hspan in
theorem toElemReplace_comp_fromElemReplace :
    (F.toElemReplace e hspan).comp (F.fromElemReplace e hspan) =
      AlgHom.id A A[F.elemReplace e] :=
  lemma_exists_unique_morphism' (F.elemReplace e)
    (fun i => nonzerodiv_image_single (F.elemReplace e) i)
    (fun i => reciprocal_for_univ (F.elemReplace e)
      (AlgHom.id A A[F.elemReplace e]) i) _ _

include hspan in
def spanEquiv : A[F] ≃ₐ[A] A[F.elemReplace e] :=
  AlgEquiv.ofAlgHom (F.toElemReplace e hspan) (F.fromElemReplace e hspan)
    (F.toElemReplace_comp_fromElemReplace e hspan)
    (F.fromElemReplace_comp_toElemReplace e hspan)

include hspan in
@[simp] theorem spanEquiv_apply (x : A[F]) :
    F.spanEquiv e hspan x = F.toElemReplace e hspan x := rfl

include hspan in
@[simp] theorem spanEquiv_algebraMap (a : A) :
    F.spanEquiv e hspan (algebraMap A A[F] a) = algebraMap A A[F.elemReplace e] a :=
  (F.toElemReplace e hspan).commutes a

include hspan in
theorem toElemReplace_unique (χ : A[F] →ₐ[A] A[F.elemReplace e]) :
    χ = F.toElemReplace e hspan :=
  lemma_exists_unique_morphism' F (F.elemReplace_elem_nzd e hspan)
    (fun i => (gen_iff_le F i).mpr (by
      exact le_trans (Multicenter.self_le (F.elemReplace e) i)
        (le_of_eq (F.span_algebraMap_eq e hspan i)))) _ _

end Multicenter
