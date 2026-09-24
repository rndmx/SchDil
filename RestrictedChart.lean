import RestrictedPanelHom
import PolyptychRestricted
import PolyptychPanelChart

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

theorem restCenterScheme_localMulticenter_ideal (j : (M.defSpace J).indnumb) :
    ((M.restCenterScheme J i).localMulticenter γ).ideal j =
      (restCenter (resM (M.chartM γ) i) (resd (M.chartM γ) (M.chartd γ) i) J).ideal j :=
  rfl

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
