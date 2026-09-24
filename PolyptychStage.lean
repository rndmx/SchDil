import PolyptychPanelLift
import RestrictedPanelClosed

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

def panelDChartDatum (J : Finset M.indnumb) (i : M.indnumb) :
    ChartDatum (M.defSpace J).dilatation where
  cov := (M.defSpace J).dilatationCover
  idl γ := Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
      (∏ s ∈ (Polyptych.Comp J).filter (fun s => i ≤ s), M.Dideal s γ)
  compat {W} _ {γ γ'} a b hab := by
    classical
    have hab' : (a ≫ (M.defSpace J).chartHom γ) ≫ M.cov.map γ =
        (b ≫ (M.defSpace J).chartHom γ') ≫ M.cov.map γ' := by
      simp only [Category.assoc]
      show a ≫ (M.defSpace J).chartToX γ = b ≫ (M.defSpace J).chartToX γ'
      rw [← (M.defSpace J).structureMap_chart γ,
        ← (M.defSpace J).structureMap_chart γ', ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ (M.defSpace J).structureMap) hab
    have hpa : Spec.preimage (W.isoSpec.inv ≫ a ≫ (M.defSpace J).chartHom γ) =
        CommRingCat.ofHom (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))) ≫
          Spec.preimage (W.isoSpec.inv ≫ a) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ a ≫ (M.defSpace J).chartHom γ =
        (W.isoSpec.inv ≫ a) ≫ (M.defSpace J).chartHom γ
      rw [Category.assoc]
    have hpb : Spec.preimage (W.isoSpec.inv ≫ b ≫ (M.defSpace J).chartHom γ') =
        CommRingCat.ofHom (algebraMap ((M.defSpace J).cov.obj γ')
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ'))) ≫
          Spec.preimage (W.isoSpec.inv ≫ b) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ b ≫ (M.defSpace J).chartHom γ' =
        (W.isoSpec.inv ≫ b) ≫ (M.defSpace J).chartHom γ'
      rw [Category.assoc]
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_finset_prod, Ideal.map_finset_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h := chartIdeal_agree M.Drep (a ≫ (M.defSpace J).chartHom γ)
      (b ≫ (M.defSpace J).chartHom γ') hab' s
    rw [hpa, hpb, CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    exact h

@[simp] theorem panelDChartDatum_idl (J : Finset M.indnumb) (i : M.indnumb)
    (γ : M.cov.J) :
    (M.panelDChartDatum J i).idl γ =
      Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ (Polyptych.Comp J).filter (fun s => i ≤ s), M.Dideal s γ) := rfl

def panelCenterDatum (J : Finset M.indnumb) (i : M.indnumb) :
    ChartDatum (M.defSpace J).dilatation where
  cov := (M.defSpace J).dilatationCover
  idl γ := M.panelChartIdeal J i γ
  compat {W} _ {γ γ'} a b hab := by
    haveI := M.panelHomScheme_isClosedImmersion J i
    have h := chartIdeal_agree
      (presentPreClos (M.panelHomScheme J i) ((M.defSpace J).dilatationCover))
      a b hab PUnit.unit
    rw [presentPreClos_ideal, presentPreClos_ideal,
      M.presentIdeal_panelHomScheme J i γ, M.presentIdeal_panelHomScheme J i γ'] at h
    exact h

@[simp] theorem panelCenterDatum_idl (J : Finset M.indnumb) (i : M.indnumb)
    (γ : M.cov.J) :
    (M.panelCenterDatum J i).idl γ = M.panelChartIdeal J i γ := rfl

def panelStage (J : Finset M.indnumb) : PreMultiCenter (M.defSpace J).dilatation where
  indnumb := {i // i ∈ Polyptych.Comp J}
  cov := (M.defSpace J).dilatationCover
  Ysub i := (M.panelCenterDatum J i.1).glued
  Dsub i := (M.panelDChartDatum J i.1).glued
  Yover i := ⟨(M.panelCenterDatum J i.1).structureMap⟩
  Dover i := ⟨(M.panelDChartDatum J i.1).structureMap⟩
  Yideal i γ := (M.panelCenterDatum J i.1).idl γ
  Dideal i γ := (M.panelDChartDatum J i.1).idl γ
  YcondIso i γ :=
    asIso ((M.panelCenterDatum J i.1).chartCompare γ)
  YcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.panelCenterDatum J i.1).chartCompare γ ≫
        pullback.snd ((M.panelCenterDatum J i.1).structureMap)
          ((M.defSpace J).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((M.panelCenterDatum J i.1).idl γ)))
    exact (M.panelCenterDatum J i.1).chartCompare_snd γ
  DcondIso i γ := asIso ((M.panelDChartDatum J i.1).chartCompare γ)
  DcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.panelDChartDatum J i.1).chartCompare γ ≫
        pullback.snd ((M.panelDChartDatum J i.1).structureMap)
          ((M.defSpace J).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((M.panelDChartDatum J i.1).idl γ)))
    exact (M.panelDChartDatum J i.1).chartCompare_snd γ
  Dprin i γ := by
    classical
    refine ⟨⟨algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
      (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s),
        (M.localMulticenter γ).elem s), ?_⟩⟩
    rw [Ideal.submodule_span_eq]
    show Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) = _
    have hD : (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) =
        Ideal.span {∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s),
          (M.localMulticenter γ).elem s} := by
      rw [Ideal.span_singleton_finset_prod]
      exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s
    rw [hD, Ideal.map_span, Set.image_singleton]
    rfl

@[simp] theorem panelStage_Yideal (J : Finset M.indnumb)
    (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    (M.panelStage J).Yideal i γ = M.panelChartIdeal J i.1 γ := rfl

@[simp] theorem panelStage_Dideal (J : Finset M.indnumb)
    (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    (M.panelStage J).Dideal i γ =
      Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) := rfl

@[simp] theorem panelStage_cov (J : Finset M.indnumb) :
    (M.panelStage J).cov = (M.defSpace J).dilatationCover := rfl

def panelSpace (J : Finset M.indnumb) : Scheme.{u+1} :=
  (M.panelStage J).dilatation

def tauJ (J : Finset M.indnumb) :
    M.panelSpace J ⟶ (M.defSpace J).dilatation :=
  (M.panelStage J).structureMap

def panelSpaceToX (J : Finset M.indnumb) : M.panelSpace J ⟶ X :=
  M.tauJ J ≫ (M.defSpace J).structureMap

end PreMultiCenter
end SchemeDilatation
