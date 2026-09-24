import RestrictedDatum
import Functoriality

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb)

def restDRel :
    _root_.relStructure
      (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Drep)
      (M.restCenterScheme J i).Drep where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

def restYRel :
    _root_.relStructure (M.restCenterScheme J i).Yrep
      (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

theorem restReindexIdeal (j : (M.defSpace J).indnumb)
    (γ : (M.restCenterScheme J i).cov.J) :
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep).reindexIdeal
        (M.restCenterScheme J i).cov j γ =
      (M.restCenterScheme J i).Yideal j γ :=
  ((M.restCenterScheme J i).Yrep.ideal_eq_reindexIdeal
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep)
    (M.restYRel J i) γ j).symm

theorem restHY (j : (M.defSpace J).indnumb)
    (γ : (M.restCenterScheme J i).cov.J) :
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep).reindexIdeal
        (M.restCenterScheme J i).cov j γ ≤
      (M.restCenterScheme J i).Yideal ((M.restDRel J i).indnumb_equiv j) γ ⊔
        (M.restCenterScheme J i).Dideal ((M.restDRel J i).indnumb_equiv j) γ := by
  rw [M.restReindexIdeal J i j γ]
  exact le_sup_left

def panelHomScheme : (M.restCenterScheme J i).dilatation ⟶ (M.defSpace J).dilatation :=
  functorialityHom (M.defSpace J) (M.restCenterScheme J i) (M.Ysub i ↘ X)
    (M.restDRel J i) (M.restHY J i)

@[simp] theorem panelHomScheme_over :
    M.panelHomScheme J i ≫ (M.defSpace J).structureMap =
      (M.restCenterScheme J i).structureMap ≫ (M.Ysub i ↘ X) :=
  functorialityHom_over (M.defSpace J) (M.restCenterScheme J i) (M.Ysub i ↘ X)
    (M.restDRel J i) (M.restHY J i)

theorem panelHomScheme_unique (g : (M.restCenterScheme J i).dilatation ⟶
      (M.defSpace J).dilatation)
    (hg : g ≫ (M.defSpace J).structureMap =
      (M.restCenterScheme J i).structureMap ≫ (M.Ysub i ↘ X)) :
    g = M.panelHomScheme J i :=
  functorialityHom_unique (M.defSpace J) (M.restCenterScheme J i) (M.Ysub i ↘ X)
    (M.restDRel J i) (M.restHY J i) g hg

end PreMultiCenter

end SchemeDilatation
