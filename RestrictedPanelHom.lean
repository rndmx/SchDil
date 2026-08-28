import RestrictedDatum
import Functoriality

/-!
# The comparison morphism `(𝔻_J)_i ⟶ 𝔻_J`

The panel `(𝔻_J)_i = 𝔻((D_J, X_J)|_{X_i} / X_i)` of `RestrictedDatum` maps to `𝔻_J` by
functoriality of the dilatation (`functorialityHom`), because its centers and divisors are
*literally* the base changes along `X_i ↪ X` of those of `𝔻_J`: the two comparison
`relStructure`s are `Iso.refl` on every subscheme, and the containment hypothesis is
`PreClos.ideal_eq_reindexIdeal` followed by `le_sup_left`.

No hypothesis at all is needed for this: `panelHomScheme` exists for every deformation
datum.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb)

/-- The divisors of the restricted datum **are** the base-changed divisors of `𝔻_J`. -/
def restDRel :
    _root_.relStructure
      (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Drep)
      (M.restCenterScheme J i).Drep where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

/-- The centers of the restricted datum **are** the base-changed centers of `𝔻_J`. -/
def restYRel :
    _root_.relStructure (M.restCenterScheme J i).Yrep
      (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

/-- The chart ideals of the base-changed centers, read on `centerCover`, are the chart
ideals of the restricted datum. -/
theorem restReindexIdeal (j : (M.defSpace J).indnumb)
    (γ : (M.restCenterScheme J i).cov.J) :
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep).reindexIdeal
        (M.restCenterScheme J i).cov j γ =
      (M.restCenterScheme J i).Yideal j γ :=
  ((M.restCenterScheme J i).Yrep.ideal_eq_reindexIdeal
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep)
    (M.restYRel J i) γ j).symm

/-- The containment hypothesis of `functorialityHom`. -/
theorem restHY (j : (M.defSpace J).indnumb)
    (γ : (M.restCenterScheme J i).cov.J) :
    (pullback_PreClos X (M.Ysub i) (M.Ysub i ↘ X) (M.defSpace J).Yrep).reindexIdeal
        (M.restCenterScheme J i).cov j γ ≤
      (M.restCenterScheme J i).Yideal ((M.restDRel J i).indnumb_equiv j) γ ⊔
        (M.restCenterScheme J i).Dideal ((M.restDRel J i).indnumb_equiv j) γ := by
  rw [M.restReindexIdeal J i j γ]
  exact le_sup_left

/-- **The comparison morphism `(𝔻_J)_i ⟶ 𝔻_J`**: the panel, constructed as the dilatation
of the restricted datum on `X_i`, maps to the deformation space `𝔻_J`. -/
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
