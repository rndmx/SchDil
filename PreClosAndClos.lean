import Project.Blowups.PreClosAndClos
import Project.ForMathlib.CubeIdentity
import Project.ForMathlib.AlgEquivRestrictScalars
import Project.ForMathlib.Flat

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct

noncomputable def quotTensorQuotEquiv (A : Type*) [CommRing A] (I J : Ideal A) :
    ((A ⧸ I) ⊗[A] (A ⧸ J)) ≃+* (A ⧸ (I ⊔ J)) :=
  ((lemma_iso A (A ⧸ J) I).symm.toRingEquiv).trans
    ((Ideal.quotEquivOfEq (by rfl)).trans
      ((DoubleQuot.quotQuotEquivQuotSup J I).trans
        (Ideal.quotEquivOfEq (sup_comm J I))))

def PreClosF (X : Scheme.{u+1}) (ι : Type) :=
  { Z : PreClos X // Z.indnumb = ι }

structure relStructureF {X : Scheme.{u+1}} {ι : Type}
    (Z Z' : PreClosF X ι) where
  toRel : relStructure Z.1 Z'.1
  rigid : ∀ i, toRel.indnumb_equiv i = cast (Z.2.trans Z'.2.symm) i

instance relSetoidF (X : Scheme.{u+1}) (ι : Type) :
    Setoid (PreClosF X ι) where
  r Z Z' := Nonempty (relStructureF Z Z')
  iseqv :=
    { refl := fun Z => ⟨⟨relStructure.refl Z.1, fun i => by simp; rfl⟩⟩
      symm := fun ⟨R⟩ => ⟨⟨R.toRel.symm, fun i => by
        have h := R.rigid
        simp only [relStructure.symm] at *
        apply (Equiv.symm_apply_eq _).mpr
        rw [h]
        simp⟩⟩
      trans := fun ⟨R⟩ ⟨R'⟩ => ⟨⟨R.toRel.trans R'.toRel, fun i => by
        simp only [relStructure.trans, Equiv.trans_apply, R.rigid, R'.rigid]
        simp⟩⟩ }

def ClosF (X : Scheme.{u+1}) (ι : Type) := Quotient (relSetoidF X ι)
