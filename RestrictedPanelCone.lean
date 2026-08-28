import RestrictedPanelChart

/-!
# The chart cone for `(𝔻_J)_i ⟶ 𝔻_J`

On charts, the comparison morphism of `RestrictedPanelHom` is `Spec` of the ring map
`restChartRho`, i.e. of `F_J(i)^*`.  As everywhere in this development the identification is
obtained from the universal property of `𝔻_J`, whose two inputs here are
`functoriality_isCars` (no hypothesis) and `pullSubset_of_over_dilatation'`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

/-- The chart of `(𝔻_J)_i` maps to `X` through `𝔻_J`. -/
theorem restChart_overX :
    ((M.restCenterScheme J i).chartTo γ ≫ M.panelHomScheme J i) ≫
        (M.defSpace J).structureMap =
      (M.restCenterScheme J i).chartToX γ ≫ (M.Ysub i ↘ X) := by
  rw [Category.assoc, M.panelHomScheme_over J i, ← Category.assoc,
    (M.restCenterScheme J i).structureMap_chart γ]

/-- The Cartier condition for the chart of `(𝔻_J)_i` with respect to `𝔻_J`. -/
theorem restChart_isCars :
    IsCars ((M.restCenterScheme J i).chart γ)
      (Clos.pullback ((M.restCenterScheme J i).chartToX γ ≫ (M.Ysub i ↘ X))
        (M.defSpace J).D) := by
  have heq : (M.restCenterScheme J i).chartToX γ ≫ (M.Ysub i ↘ X) =
      (M.restCenterScheme J i).chartTo γ ≫
        ((M.restCenterScheme J i).structureMap ≫ (M.Ysub i ↘ X)) := by
    rw [← Category.assoc, (M.restCenterScheme J i).structureMap_chart γ]
  rw [heq]
  have hstep : Clos.pullback
      ((M.restCenterScheme J i).chartTo γ ≫
        ((M.restCenterScheme J i).structureMap ≫ (M.Ysub i ↘ X))) (M.defSpace J).D =
      pullback_Clos ((M.restCenterScheme J i).chartTo γ)
        (Clos.pullback ((M.restCenterScheme J i).structureMap ≫ (M.Ysub i ↘ X))
          (M.defSpace J).D) := by
    show pullback_Clos _ (Quotient.mk'' (M.defSpace J).Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  haveI : IsOpenImmersion ((M.restCenterScheme J i).chartTo γ) :=
    (M.restCenterScheme J i).chartTo_isOpenImmersion γ
  haveI : AlgebraicGeometry.Flat ((M.restCenterScheme J i).chartTo γ) := inferInstance
  exact pullback_IsCars _ _ _
    (functoriality_isCars (M.defSpace J) (M.restCenterScheme J i) (M.Ysub i ↘ X)
      (M.restDRel J i))

/-- The containment condition for the chart of `(𝔻_J)_i` with respect to `𝔻_J`. -/
theorem restChart_pullSubset :
    (M.defSpace J).pullSubset
      ((M.restCenterScheme J i).chartToX γ ≫ (M.Ysub i ↘ X)) := by
  have h := (M.defSpace J).pullSubset_of_over_dilatation'
    ((M.restCenterScheme J i).chartTo γ ≫ M.panelHomScheme J i)
  rwa [M.restChart_overX J i γ] at h

/-- **The chart cone**: on charts, `(𝔻_J)_i ⟶ 𝔻_J` is `Spec` of `F_J(i)^*`. -/
theorem rest_chart_cone (hC : M.CartierDatum) :
    (M.restCenterScheme J i).chartTo γ ≫ M.panelHomScheme J i =
      M.restRhoSch J i γ hC ≫ (M.defSpace J).chartTo γ := by
  refine ((M.defSpace J).universal_property ((M.restCenterScheme J i).chart γ)
    ((M.restCenterScheme J i).chartToX γ ≫ (M.Ysub i ↘ X))
    (M.restChart_isCars J i γ) (M.restChart_pullSubset J i γ)).unique ?_ ?_
  · exact M.restChart_overX J i γ
  · rw [Category.assoc, (M.defSpace J).structureMap_chart γ,
      show (M.defSpace J).chartToX γ =
        (M.defSpace J).chartHom γ ≫ M.cov.map γ from rfl,
      ← Category.assoc, M.restRhoSch_chartHom J i γ hC, Category.assoc,
      ← M.centerCover_map_overX i γ, ← Category.assoc]
    rfl

end PreMultiCenter

end SchemeDilatation
