import RestrictedPanelHom
import PolyptychRestricted

/-!
# The chart bridge for the restricted datum

On the chart `γ`, the restricted datum `(D_J, X_J)|_{X_i}` of `RestrictedDatum` is exactly
the ring-level restricted datum `resM`/`resd` of `PolyptychRestricted`: the centers agree
on the nose, and the distinguished elements generate the same ideals.  So
`Multicenter.spanEquiv` identifies the two dilatations, exactly as `chartEquiv` does for
`𝔻_J` itself.

This is what makes the constructed panel computable: chart `γ` of `(𝔻_J)_i` is the ring
`R_J` of the restricted datum over `A_γ ⧸ M_i`, which is the codomain of `F_J(i)^*`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

/-- On a chart, the centers of the restricted datum are those of the ring-level restricted
datum `resM`. -/
theorem restCenterScheme_localMulticenter_ideal (j : (M.defSpace J).indnumb) :
    ((M.restCenterScheme J i).localMulticenter γ).ideal j =
      (restCenter (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J).ideal j :=
  rfl

/-- On a chart, the distinguished element of the restricted datum generates the same ideal
as the ring-level `elemOf` of the restricted datum. -/
theorem restCenterScheme_local_Dideal_span (j : (M.defSpace J).indnumb) :
    Ideal.span {((M.restCenterScheme J i).localMulticenter γ).elem j} =
      Ideal.span {elemOf (resd (M.chartM γ) (M.chartd γ) i) J j.1} := by
  classical
  letI : Submodule.IsPrincipal ((M.restCenterScheme J i).Dideal j γ) :=
    (M.restCenterScheme J i).Dprin j γ
  have h1 : Ideal.span {((M.restCenterScheme J i).localMulticenter γ).elem j} =
      (M.restCenterScheme J i).Dideal j γ :=
    Ideal.span_singleton_generator _
  rw [h1, M.restCenterScheme_Dideal J i j γ]
  simp only [elemOf, resd]
  rw [Ideal.span_singleton_finset_prod, Ideal.map_finset_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Ideal.span_singleton_map]
  congr 1
  letI : Submodule.IsPrincipal (M.Dideal s γ) := M.Dprin s γ
  exact (Ideal.span_singleton_generator (M.Dideal s γ)).symm

/-- **The chart bridge for the panel**: on the chart `γ`, the panel `(𝔻_J)_i` is the
ring-level `R_J` of the restricted datum over `A_γ ⧸ M_i`. -/
def restChartEquiv :
    Ring (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J ≃+*
      Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ) :=
  (Multicenter.spanEquiv
    (restCenter (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J)
    (fun j => ((M.restCenterScheme J i).Dprin j γ).generator)
    (fun j => M.restCenterScheme_local_Dideal_span J i γ j)).toRingEquiv

@[simp] theorem restChartEquiv_algebraMap (a : M.cov.obj γ ⧸ M.Yideal i γ) :
    M.restChartEquiv J i γ (algebraMap (M.cov.obj γ ⧸ M.Yideal i γ)
      (Ring (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J) a) =
      algebraMap ((M.restCenterScheme J i).cov.obj γ)
        (Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ)) a :=
  (Multicenter.spanEquiv
    (restCenter (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J)
    (fun j => ((M.restCenterScheme J i).Dprin j γ).generator)
    (fun j => M.restCenterScheme_local_Dideal_span J i γ j)).commutes a

end PreMultiCenter

end SchemeDilatation
