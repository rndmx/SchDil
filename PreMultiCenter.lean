import MulticenterRing
import PreClosAndClos
import PreClosClosedImmersion

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

structure PreMultiCenter (X : Scheme.{u+1}) where
  (indnumb : Type)
  (cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X)
  (Ysub : indnumb → Scheme)
  (Dsub : indnumb → Scheme)
  [Yover : ∀ (i : indnumb), Scheme.Over (Ysub i) X]
  [Dover : ∀ (i : indnumb), Scheme.Over (Dsub i) X]
  (Yideal : ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ))
  (Dideal : ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ))
  (YcondIso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ Yideal i γ)) ≅
    pullback (f := Ysub i ↘ X) (g := cov.map γ))
  (YcondOver : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (YcondIso i γ).hom (Spec (CommRingCat.of (cov.obj γ))))
  (DcondIso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ Dideal i γ)) ≅
    pullback (f := Dsub i ↘ X) (g := cov.map γ))
  (DcondOver : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (DcondIso i γ).hom (Spec (CommRingCat.of (cov.obj γ))))
  (Dprin : ∀ i γ, (Dideal i γ).IsPrincipal)

attribute [instance] PreMultiCenter.Yover PreMultiCenter.Dover

namespace PreMultiCenter

variable (M : PreMultiCenter X)

def Yrep : PreClos X where
  indnumb := M.indnumb
  subscheme := M.Ysub
  cov := M.cov
  ideal := M.Yideal
  condiso := M.YcondIso
  condover := M.YcondOver

def Drep : PreClos X where
  indnumb := M.indnumb
  subscheme := M.Dsub
  cov := M.cov
  ideal := M.Dideal
  condiso := M.DcondIso
  condover := M.DcondOver

theorem Drep_isPrePri : IsPrePri X M.Drep := ⟨M.Dprin⟩

noncomputable def Y : Clos X := Quotient.mk'' M.Yrep

noncomputable def D : Clos X := Quotient.mk'' M.Drep

theorem Yrep_eq : (Quotient.mk'' M.Yrep : Clos X) = M.Y := rfl

theorem Drep_eq : (Quotient.mk'' M.Drep : Clos X) = M.D := rfl

theorem D_isPri : IsPri X M.D := ⟨M.Drep, M.Drep_isPrePri, rfl⟩

def localMulticenter (γ : M.cov.J) : Multicenter (M.cov.obj γ) where
  index := M.indnumb
  ideal i := M.Yideal i γ
  elem i := (M.Dprin i γ).generator

end PreMultiCenter

namespace PreMultiCenter

structure relStructure (M M' : PreMultiCenter X) where
  RY : _root_.relStructure M.Yrep M'.Yrep
  RD : _root_.relStructure M.Drep M'.Drep
  eq_equiv : RY.indnumb_equiv = RD.indnumb_equiv

@[refl]
def relStructure.refl (M : PreMultiCenter X) : relStructure M M :=
  ⟨.refl _, .refl _, rfl⟩

@[symm]
def relStructure.symm {M M' : PreMultiCenter X} (R : relStructure M M') :
    relStructure M' M :=
  ⟨R.RY.symm, R.RD.symm, by
    show R.RY.indnumb_equiv.symm = R.RD.indnumb_equiv.symm
    rw [R.eq_equiv]⟩

@[trans]
def relStructure.trans {M M' M'' : PreMultiCenter X}
    (R : relStructure M M') (R' : relStructure M' M'') : relStructure M M'' :=
  ⟨R.RY.trans R'.RY, R.RD.trans R'.RD, by
    show R.RY.indnumb_equiv.trans R'.RY.indnumb_equiv =
      R.RD.indnumb_equiv.trans R'.RD.indnumb_equiv
    rw [R.eq_equiv, R'.eq_equiv]⟩

variable (X) in
def rel : PreMultiCenter X → PreMultiCenter X → Prop :=
  fun M M' => Nonempty (relStructure M M')

variable (X) in
instance relSetoid : Setoid (PreMultiCenter X) where
  r := rel X
  iseqv :=
    { refl := fun M => ⟨.refl M⟩
      symm := Nonempty.map .symm
      trans := by
        rintro _ _ _ ⟨R⟩ ⟨R'⟩
        exact ⟨R.trans R'⟩ }

end PreMultiCenter

end SchemeDilatation
