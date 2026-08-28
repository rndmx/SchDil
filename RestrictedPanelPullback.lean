import RestrictedPanelCone

/-!
# The chart of the panel is the fibre product

The square

```
chart_γ((𝔻_J)_i) → (𝔻_J)_i
      ↓                 ↓
chart_γ(𝔻_J)     →   𝔻_J
```

is cartesian.  This is the geometric heart of the identification of the constructed panel
with the panel of `PolyptychStage`: it says that `(𝔻_J)_i` meets each chart of `𝔻_J` in
exactly `Spec` of the quotient by `ker(F_J(i)^*)`, so `panelHomScheme` is a closed immersion
and its chart ideal is the panel ideal.

The proof transposes `SchemeFact51.centerToPullback_isIso`; the extra ingredient is
`chartCompare_isIso`, which realises the chart of `(𝔻_J)_i` as a fibre product over `X_i`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

/-- The comparison `chart_γ((𝔻_J)_i) ⟶ (𝔻_J)_i ×_{𝔻_J} chart_γ(𝔻_J)`. -/
def restChartToPullback (hC : M.CartierDatum) :
    (M.restCenterScheme J i).chart γ ⟶
      pullback (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) :=
  pullback.lift ((M.restCenterScheme J i).chartTo γ) (M.restRhoSch J i γ hC)
    (M.rest_chart_cone J i γ hC)

/-- The cone condition for the second leg of the inverse comparison. -/
theorem restPullback_cone :
    (pullback.fst (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ≫
        (M.restCenterScheme J i).structureMap) ≫ (M.Ysub i ↘ X) =
      (pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ≫
        (M.defSpace J).chartHom γ) ≫ M.cov.map γ := by
  rw [Category.assoc, ← M.panelHomScheme_over J i, ← Category.assoc,
    pullback.condition, Category.assoc, (M.defSpace J).structureMap_chart γ,
    Category.assoc]
  rfl

/-- The second leg of the inverse comparison: the map to the chart `Spec (A_γ ⧸ M_i)` of
`X_i`. -/
def pullbackToRestChartLeg :
    pullback (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ⟶
      Spec ((M.centerCover i).obj γ) :=
  pullback.lift
      (pullback.fst (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ≫
        (M.restCenterScheme J i).structureMap)
      (pullback.snd (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ≫
        (M.defSpace J).chartHom γ)
      (M.restPullback_cone J i γ) ≫
    (M.YcondIso i γ).inv

theorem pullbackToRestChartLeg_map :
    M.pullbackToRestChartLeg J i γ ≫ (M.centerCover i).map γ =
      pullback.fst (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ≫
        (M.restCenterScheme J i).structureMap := by
  rw [pullbackToRestChartLeg, centerCover_map, chartOfCenter_to, Category.assoc,
    Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The inverse comparison `(𝔻_J)_i ×_{𝔻_J} chart_γ(𝔻_J) ⟶ chart_γ((𝔻_J)_i)`. -/
def pullbackToRestChart :
    pullback (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) ⟶
      (M.restCenterScheme J i).chart γ :=
  pullback.lift (pullback.fst (M.panelHomScheme J i) ((M.defSpace J).chartTo γ))
      (M.pullbackToRestChartLeg J i γ)
      (M.pullbackToRestChartLeg_map J i γ).symm ≫
    inv ((M.restCenterScheme J i).chartCompare γ)

theorem pullbackToRestChart_chartTo :
    M.pullbackToRestChart J i γ ≫ (M.restCenterScheme J i).chartTo γ =
      pullback.fst (M.panelHomScheme J i) ((M.defSpace J).chartTo γ) := by
  rw [pullbackToRestChart, Category.assoc,
    show inv ((M.restCenterScheme J i).chartCompare γ) ≫
        (M.restCenterScheme J i).chartTo γ =
      pullback.fst ((M.restCenterScheme J i).structureMap)
        ((M.restCenterScheme J i).cov.map γ) by
      rw [← (M.restCenterScheme J i).chartCompare_fst γ, ← Category.assoc,
        IsIso.inv_hom_id, Category.id_comp]]
  exact pullback.lift_fst _ _ _

theorem restChartToPullback_comp_pullbackToRestChart (hC : M.CartierDatum) :
    M.restChartToPullback J i γ hC ≫ M.pullbackToRestChart J i γ = 𝟙 _ := by
  have hover := M.YcondOver i γ
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  rw [pullbackToRestChart, ← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, restChartToPullback, pullback.lift_fst]
    exact ((M.restCenterScheme J i).chartCompare_fst γ).symm
  · rw [Category.assoc, pullback.lift_snd,
      show (M.restCenterScheme J i).chartCompare γ ≫
          pullback.snd (M.restCenterScheme J i).structureMap ((M.centerCover i).map γ) =
          (M.restCenterScheme J i).chartHom γ from
        (M.restCenterScheme J i).chartCompare_snd γ,
      pullbackToRestChartLeg, ← Category.assoc, Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, restChartToPullback, ← Category.assoc,
        pullback.lift_fst, (M.restCenterScheme J i).structureMap_chart γ,
        Category.assoc]
      show (M.restCenterScheme J i).chartHom γ ≫ (M.centerCover i).map γ =
        (M.restCenterScheme J i).chartHom γ ≫
          ((M.YcondIso i γ).hom ≫ pullback.fst (M.Ysub i ↘ X) (M.cov.map γ))
      rw [← chartOfCenter_to]
      rfl
    · rw [Category.assoc, pullback.lift_snd, restChartToPullback, ← Category.assoc,
        pullback.lift_snd, Category.assoc, hover, M.restRhoSch_chartHom J i γ hC]

theorem pullbackToRestChart_comp_restChartToPullback (hC : M.CartierDatum) :
    M.pullbackToRestChart J i γ ≫ M.restChartToPullback J i γ hC = 𝟙 _ := by
  haveI : Mono ((M.defSpace J).chartTo γ) := by
    haveI := (M.defSpace J).chartTo_isOpenImmersion γ
    infer_instance
  apply pullback.hom_ext
  · rw [Category.assoc, restChartToPullback, pullback.lift_fst, Category.id_comp]
    exact M.pullbackToRestChart_chartTo J i γ
  · rw [Category.assoc, restChartToPullback, pullback.lift_snd, Category.id_comp]
    apply Mono.right_cancellation (f := (M.defSpace J).chartTo γ)
    rw [Category.assoc, ← M.rest_chart_cone J i γ hC, ← Category.assoc,
      M.pullbackToRestChart_chartTo J i γ]
    exact pullback.condition

/-- **The chart square is cartesian.** -/
instance restChartToPullback_isIso (hC : M.CartierDatum) :
    IsIso (M.restChartToPullback J i γ hC) :=
  ⟨M.pullbackToRestChart J i γ,
    M.restChartToPullback_comp_pullbackToRestChart J i γ hC,
    M.pullbackToRestChart_comp_restChartToPullback J i γ hC⟩

end PreMultiCenter

end SchemeDilatation
