import PreMultiCenter

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

section BaseChangeComp

variable {X T T' : Scheme.{u+1}}

def pullback_PreClos_comp (Z : PreClos X) (p : T ⟶ X) (g : T' ⟶ T) :
    relStructure (pullback_PreClos T T' g (pullback_PreClos X T p Z))
      (pullback_PreClos X T' (g ≫ p) Z) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso i := pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) p g
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact pullbackLeftPullbackSndIso_hom_snd _ _ _

theorem pullback_Clos_comp (Z : Clos X) (p : T ⟶ X) (g : T' ⟶ T) :
    pullback_Clos g (pullback_Clos p Z) = pullback_Clos (g ≫ p) Z := by
  induction Z using Quotient.inductionOn with | h Z =>
  exact Quotient.sound ⟨pullback_PreClos_comp Z p g⟩

end BaseChangeComp

namespace SchemeDilatation

variable {X : Scheme.{u+1}} {T : Scheme.{u+1}}

namespace PreMultiCenter

variable (M : PreMultiCenter X) (f : T ⟶ X)

theorem pull_cov_Yrep_eq_Drep :
    pull_cov X M.Yrep T f = pull_cov X M.Drep T f := rfl

def baseChange : PreMultiCenter T where
  indnumb := M.indnumb
  cov := pull_cov X M.Yrep T f
  Ysub i := pullback (M.Ysub i ↘ X) f
  Dsub i := pullback (M.Dsub i ↘ X) f
  Yover i := ⟨pullback.snd _ _⟩
  Dover i := ⟨pullback.snd _ _⟩
  Yideal i γβ := pull_ideal X M.Yrep T f γβ i
  Dideal i γβ := pull_ideal X M.Drep T f γβ i
  YcondIso i γβ := pullback_PreClos_condiso X γβ i
  YcondOver i γβ := pullback_PreClos_condover X γβ i
  DcondIso i γβ := pullback_PreClos_condiso (Z := M.Drep) X γβ i
  DcondOver i γβ := pullback_PreClos_condover (Z := M.Drep) X γβ i
  Dprin i γβ := by
    apply Submodule.IsPrincipal.map_ringHom
    exact M.Dprin i γβ.1

@[simp] theorem baseChange_indnumb : (M.baseChange f).indnumb = M.indnumb := rfl

@[simp] theorem baseChange_cov : (M.baseChange f).cov = pull_cov X M.Yrep T f := rfl

@[simp] theorem baseChange_Yrep :
    (M.baseChange f).Yrep = pullback_PreClos X T f M.Yrep := rfl

@[simp] theorem baseChange_Drep :
    (M.baseChange f).Drep = pullback_PreClos X T f M.Drep := rfl

@[simp] theorem baseChange_Y : (M.baseChange f).Y = pullback_Clos f M.Y := rfl

@[simp] theorem baseChange_D : (M.baseChange f).D = pullback_Clos f M.D := rfl

@[simp] theorem baseChange_Yideal (i : M.indnumb) (γβ : (M.baseChange f).cov.J) :
    (M.baseChange f).Yideal i γβ =
      Ideal.map (pull_mor_ring X M.Yrep T f γβ).hom (M.Yideal i γβ.1) := rfl

@[simp] theorem baseChange_Dideal (i : M.indnumb) (γβ : (M.baseChange f).cov.J) :
    (M.baseChange f).Dideal i γβ =
      Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Dideal i γβ.1) := rfl

theorem baseChange_localMulticenter_ideal (γβ : (M.baseChange f).cov.J)
    (i : M.indnumb) :
    ((M.baseChange f).localMulticenter γβ).ideal i =
      Ideal.map (pull_mor_ring X M.Yrep T f γβ).hom
        ((M.localMulticenter γβ.1).ideal i) := rfl

theorem baseChange_localMulticenter_elem_span (γβ : (M.baseChange f).cov.J)
    (i : M.indnumb) :
    Ideal.span {((M.baseChange f).localMulticenter γβ).elem i} =
      Ideal.map (pull_mor_ring X M.Drep T f γβ).hom
        (Ideal.span {(M.localMulticenter γβ.1).elem i}) := by
  letI hbc : ((M.baseChange f).Dideal i γβ).IsPrincipal := (M.baseChange f).Dprin i γβ
  letI hM : (M.Dideal i γβ.1).IsPrincipal := M.Dprin i γβ.1
  have e₁ : Ideal.span {((M.baseChange f).localMulticenter γβ).elem i} =
      (M.baseChange f).Dideal i γβ := Ideal.span_singleton_generator _
  have e₂ : Ideal.span {(M.localMulticenter γβ.1).elem i} = M.Dideal i γβ.1 :=
    Ideal.span_singleton_generator _
  rw [e₁, e₂, baseChange_Dideal]

section BaseChangeComp

variable {T' : Scheme.{u+1}}

def baseChangeComp (p : T ⟶ X) (g : T' ⟶ T) :
    relStructure ((M.baseChange p).baseChange g) (M.baseChange (g ≫ p)) where
  RY := pullback_PreClos_comp M.Yrep p g
  RD := pullback_PreClos_comp M.Drep p g
  eq_equiv := rfl

theorem baseChange_comp_Y (p : T ⟶ X) (g : T' ⟶ T) :
    ((M.baseChange p).baseChange g).Y = (M.baseChange (g ≫ p)).Y :=
  Quotient.sound ⟨(M.baseChangeComp p g).RY⟩

theorem baseChange_comp_D (p : T ⟶ X) (g : T' ⟶ T) :
    ((M.baseChange p).baseChange g).D = (M.baseChange (g ≫ p)).D :=
  Quotient.sound ⟨(M.baseChangeComp p g).RD⟩

theorem pullback_Clos_baseChange_D (p : T ⟶ X) (g : T' ⟶ T) :
    pullback_Clos g (pullback_Clos p M.D) = (M.baseChange (g ≫ p)).D := by
  rw [pullback_Clos_comp, baseChange_D]

end BaseChangeComp

end PreMultiCenter

end SchemeDilatation
