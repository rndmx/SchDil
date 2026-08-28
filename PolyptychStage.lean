import PolyptychPanelLift

/-!
# The second stage `𝔻𝔻_J` : the panel datum on `𝔻_J`

This file assembles Definition `def:panel-datum` of Dubouloz-Mayeux, *A polyptych of
multi-centered deformation spaces*: the multicenter on `𝔻_J` whose centers are the panels
`(𝔻_J)ᵢ` and whose divisors are the total transforms `σ_J^{-1}(Σ_{s ∈ (I∖J)≥i} D_s)`,
for `i ∈ I ∖ J`.  Its dilatation is the `J`-th panel `𝔻𝔻_J` of `𝔻_I`.

The centers come from `panelYChartDatum` (`PolyptychPanelLift`); the divisors are glued by
`panelDChartDatum`, exactly as `SchemeLemma44.transformDChartDatum` glues the total
transform of a single divisor.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

/-- The chart datum, on the charts of `𝔻_J`, of the total transform of
`Σ_{s ∈ (I∖J)≥i} D_s`. -/
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

/-- **The panel datum `𝔻𝔻_J`** of Definition `def:panel-datum`: on `𝔻_J`, the centers are
the panels `(𝔻_J)ᵢ` and the divisors are the total transforms of
`Σ_{s ∈ (I∖J)≥i} D_s`, indexed by `i ∈ I ∖ J`. -/
def panelStage (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
    (hM : M.MonoDatum) : PreMultiCenter (M.defSpace J).dilatation where
  indnumb := {i // i ∈ Polyptych.Comp J}
  cov := (M.defSpace J).dilatationCover
  Ysub i := (M.panelYChartDatum J i.1 hC hb hM).glued
  Dsub i := (M.panelDChartDatum J i.1).glued
  Yover i := ⟨(M.panelYChartDatum J i.1 hC hb hM).structureMap⟩
  Dover i := ⟨(M.panelDChartDatum J i.1).structureMap⟩
  Yideal i γ := (M.panelYChartDatum J i.1 hC hb hM).idl γ
  Dideal i γ := (M.panelDChartDatum J i.1).idl γ
  YcondIso i γ := asIso ((M.panelYChartDatum J i.1 hC hb hM).chartCompare γ)
  YcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (M.panelYChartDatum J i.1 hC hb hM).chartCompare γ ≫
        pullback.snd ((M.panelYChartDatum J i.1 hC hb hM).structureMap)
          ((M.defSpace J).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((M.panelYChartDatum J i.1 hC hb hM).idl γ)))
    exact (M.panelYChartDatum J i.1 hC hb hM).chartCompare_snd γ
  DcondIso i γ := asIso ((M.panelDChartDatum J i.1).chartCompare γ)
  DcondOver i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
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

@[simp] theorem panelStage_Yideal (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hb : M.CarsOnCenterAll) (hM : M.MonoDatum)
    (i : (M.panelStage J hC hb hM).indnumb) (γ : M.cov.J) :
    (M.panelStage J hC hb hM).Yideal i γ =
      Ideal.map (M.panelChartRho J i.1 γ hM).toRingHom
        (((M.panelInt J i.1).localMulticenter γ).genFracIdeal) := rfl

@[simp] theorem panelStage_Dideal (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hb : M.CarsOnCenterAll) (hM : M.MonoDatum)
    (i : (M.panelStage J hC hb hM).indnumb) (γ : M.cov.J) :
    (M.panelStage J hC hb hM).Dideal i γ =
      Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) := rfl

@[simp] theorem panelStage_cov (J : Finset M.indnumb) (hC : M.CartierDatum)
    (hb : M.CarsOnCenterAll) (hM : M.MonoDatum) :
    (M.panelStage J hC hb hM).cov = (M.defSpace J).dilatationCover := rfl

/-- **The J-th panel DD_J of D_I** (Definition `def:panel-datum`). -/
def panelSpace (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
    (hM : M.MonoDatum) : Scheme.{u+1} := (M.panelStage J hC hb hM).dilatation

/-- The structure morphism `τ_J : 𝔻𝔻_J → 𝔻_J`. -/
def tauJ (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
    (hM : M.MonoDatum) : M.panelSpace J hC hb hM ⟶ (M.defSpace J).dilatation :=
  (M.panelStage J hC hb hM).structureMap

/-- The composite `𝔻𝔻_J → X`. -/
def panelSpaceToX (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
    (hM : M.MonoDatum) : M.panelSpace J hC hb hM ⟶ X :=
  M.tauJ J hC hb hM ≫ (M.defSpace J).structureMap

end PreMultiCenter
end SchemeDilatation
