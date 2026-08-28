import MulticenterRing
import PreClosClosedImmersion

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

def singletonCovering (A : CommRingCat.{u+1}) :
    Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) (Spec A) where
  J := PUnit
  obj _ := A
  map _ := 𝟙 _
  f _ := PUnit.unit
  covers x := by simp
  map_prop _ := inferInstance

namespace Multicenter

variable {A : CommRingCat.{u+1}} (F : Multicenter A)

variable (ι : Type) (I : ι → Ideal A)

def _root_.idealFamilyPreClos : PreClos (Spec A) where
  indnumb := ι
  subscheme i := Spec (CommRingCat.of (A ⧸ I i))
  over i := ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))⟩
  cov := singletonCovering A
  ideal i _ := I i
  condiso i _ :=
    ⟨Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.rid A A (A ⧸ I i)) : _ →+* _)),
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.rid A A (A ⧸ I i)).symm : _ →+* _)),
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        ext x
        exact (Algebra.TensorProduct.rid A A (A ⧸ I i)).apply_symm_apply x),
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        ext x
        exact (Algebra.TensorProduct.rid A A (A ⧸ I i)).symm_apply_apply x)⟩ ≪≫
      (AlgebraicGeometry.pullbackSpecIso A (A ⧸ I i) A).symm ≪≫
      pullback.congrHom rfl (Spec.map_id _)
  condover i _ := by
    rw [Scheme.Hom.isOver_iff]
    simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom]
    erw [pullback.lift_snd]
    rw [Category.comp_id]
    erw [pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
    ext a
    simp [Algebra.smul_def]

def toPreClosY : PreClos (Spec A) := idealFamilyPreClos F.index F.ideal

def toPreClosD : PreClos (Spec A) :=
  idealFamilyPreClos F.index (fun i => Ideal.span {F.elem i})

def toClosY : Clos (Spec A) := Quotient.mk'' F.toPreClosY

def toClosD : Clos (Spec A) := Quotient.mk'' F.toPreClosD

@[simp] theorem toPreClosY_ideal (i : F.index) (γ : (singletonCovering A).J) :
    F.toPreClosY.ideal i γ = F.ideal i := rfl

@[simp] theorem toPreClosD_ideal (i : F.index) (γ : (singletonCovering A).J) :
    F.toPreClosD.ideal i γ = Ideal.span {F.elem i} := rfl

end Multicenter
