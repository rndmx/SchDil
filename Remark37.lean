import TransportPrinciple
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

suppress_compilation

universe u

open AlgebraicGeometry TopologicalSpace CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

def IsLocallyPrincipal (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ (I.ideal U).IsPrincipal

theorem isPrincipal_of_le {I : X.IdealSheafData} {U V : X.affineOpens} (h : U ≤ V)
    (hV : (I.ideal V).IsPrincipal) : (I.ideal U).IsPrincipal := by
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (I.ideal V)
  refine ⟨⟨(X.presheaf.map (homOfLE h).op).hom a, ?_⟩⟩
  rw [← I.map_ideal h, show I.ideal V = Ideal.span {a} from ha, Ideal.map_span,
    Set.image_singleton]
  rfl

theorem exists_affineOpen_isPrincipal_forall {ι : Type*} [Finite ι]
    (I : ι → X.IdealSheafData) (h : ∀ i, IsLocallyPrincipal (I i)) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∀ i, ((I i).ideal U).IsPrincipal := by
  choose U hxU hU using fun i => h i x
  have hopen : IsOpen (⋂ i, ((U i).1 : Set X)) :=
    isOpen_iInter_of_finite fun i => (U i).1.2
  have hx : x ∈ ⋂ i, ((U i).1 : Set X) := Set.mem_iInter.mpr hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hx hopen
  refine ⟨⟨V, hV⟩, hxV, fun i => isPrincipal_of_le (V := U i) ?_ (hU i)⟩
  intro z hz
  exact Set.mem_iInter.mp (hVW hz) i

theorem iUnion_affineOpens_isPrincipal_forall {ι : Type*} [Finite ι]
    (I : ι → X.IdealSheafData) (h : ∀ i, IsLocallyPrincipal (I i)) :
    ⋃ V ∈ {V : X.affineOpens | ∀ i, ((I i).ideal V).IsPrincipal}, (V.1 : Set X) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨U, hxU, hU⟩ := exists_affineOpen_isPrincipal_forall I h x
  exact Set.mem_biUnion hU hxU

def IsLocallyPrincipalOver {D : Scheme.{u}} (f : D ⟶ X) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens,
    x ∈ U.1 ∧ (RingHom.ker (f.app U).hom).IsPrincipal

theorem isLocallyPrincipalOver_iff {D : Scheme.{u}} (f : D ⟶ X)
    [IsClosedImmersion f] :
    IsLocallyPrincipalOver f ↔ IsLocallyPrincipal f.ker := by
  constructor <;> intro h x <;> obtain ⟨U, hxU, hU⟩ := h x <;>
    exact ⟨U, hxU, by simpa using hU⟩

theorem exists_affineOpen_ker_isPrincipal_forall {ι : Type*} [Finite ι]
    {D : ι → Scheme.{u}} (f : ∀ i, D i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∀ i, (RingHom.ker ((f i).app U).hom).IsPrincipal := by
  obtain ⟨U, hxU, hU⟩ := exists_affineOpen_isPrincipal_forall (fun i => (f i).ker)
    (fun i => (isLocallyPrincipalOver_iff (f i)).mp (h i)) x
  exact ⟨U, hxU, fun i => by simpa using hU i⟩

theorem iUnion_affineOpens_ker_isPrincipal_forall {ι : Type*} [Finite ι]
    {D : ι → Scheme.{u}} (f : ∀ i, D i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (h : ∀ i, IsLocallyPrincipalOver (f i)) :
    ⋃ V ∈ {V : X.affineOpens |
        ∀ i, (RingHom.ker ((f i).app V).hom).IsPrincipal}, (V.1 : Set X) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨U, hxU, hU⟩ := exists_affineOpen_ker_isPrincipal_forall f h x
  exact Set.mem_biUnion hU hxU

end AlgebraicGeometry.Scheme.IdealSheafData
