import RestrictedPanelClosed
import PolyptychPaperForm

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)


section PanelIdentification

def panelPreClos (i' : (M.panelStage J).indnumb) :
    PreClos ((M.defSpace J).dilatation) where
  indnumb := PUnit
  subscheme _ := (M.panelStage J).Ysub i'
  over _ := (M.panelStage J).Yover i'
  cov := (M.defSpace J).dilatationCover
  ideal _ γ := (M.panelStage J).Yideal i' γ
  condiso _ γ := (M.panelStage J).YcondIso i' γ
  condover _ γ := (M.panelStage J).YcondOver i' γ

def restPanelRel (i' : (M.panelStage J).indnumb) :
    haveI := M.panelHomScheme_isClosedImmersion J i'.1
    _root_.relStructure
      (presentPreClos (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover))
      (M.panelPreClos J i') :=
  haveI := M.panelHomScheme_isClosedImmersion J i'.1
  PreClos.relStructure_of_ideal_eq
    (presentPreClos (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover))
    (M.panelPreClos J i') (Equiv.refl PUnit)
    (fun u γ => by
      have h1 := (M.presentIdeal_panelHomScheme J i'.1 γ).trans
        (M.panelStage_Yideal_eq J i' γ).symm
      show presentIdeal (M.panelHomScheme J i'.1) ((M.defSpace J).dilatationCover) γ =
        (M.panelPreClos J i').reindexIdeal
          (M.panelPreClos J i').cov u γ
      rw [PreClos.reindexIdeal_self]
      exact h1)

def restPanelIso (i' : (M.panelStage J).indnumb) :
    M.restPanel J i'.1 ≅ (M.panelStage J).Ysub i' :=
  haveI := M.panelHomScheme_isClosedImmersion J i'.1
  (M.restPanelRel J i').subscheme_iso PUnit.unit

theorem restPanelIso_over (i' : (M.panelStage J).indnumb) :
    (M.restPanelIso J i').hom ≫
        ((M.panelStage J).Ysub i' ↘ (M.defSpace J).dilatation) =
      M.panelHomScheme J i'.1 := by
  haveI := M.panelHomScheme_isClosedImmersion J i'.1
  have h := (M.restPanelRel J i').subscheme_iso_over PUnit.unit
  rw [Scheme.Hom.isOver_iff] at h
  exact h

theorem panelStage_Ysub_eq_restPanel (i' : (M.panelStage J).indnumb) :
    Nonempty (M.restPanel J i'.1 ≅ (M.panelStage J).Ysub i') :=
  ⟨M.restPanelIso J i'⟩

end PanelIdentification

end PreMultiCenter

end SchemeDilatation
