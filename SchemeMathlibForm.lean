import Remark37

suppress_compilation

universe u

open AlgebraicGeometry TopologicalSpace CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {ι : Type} [Finite ι] {D : ι → Scheme.{u}}

noncomputable def principalOpen (f : ∀ i, D i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) (x : X) : X.affineOpens :=
  (exists_affineOpen_ker_isPrincipal_forall f h x).choose

theorem mem_principalOpen (f : ∀ i, D i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) (x : X) :
    x ∈ (principalOpen f h x).1 :=
  (exists_affineOpen_ker_isPrincipal_forall f h x).choose_spec.1

theorem isPrincipal_principalOpen (f : ∀ i, D i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) (x : X) (i : ι) :
    (RingHom.ker ((f i).app (principalOpen f h x)).hom).IsPrincipal :=
  (exists_affineOpen_ker_isPrincipal_forall f h x).choose_spec.2 i

noncomputable def principalCover (f : ∀ i, D i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) :
    Scheme.AffineCover.{u} (P := @IsOpenImmersion) X where
  J := X
  obj x := Γ(X, (principalOpen f h x).1)
  map x := (principalOpen f h x).2.fromSpec
  f x := x
  covers x := by
    rw [(principalOpen f h x).2.range_fromSpec]
    exact mem_principalOpen f h x
  map_prop x := inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData
