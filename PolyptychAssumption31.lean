import PolyptychPaperForm
import SchemeFact51
import SchemeProp52
import IteratedSchemeMultiCore

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X)

section Factor

variable (i₀ : M.indnumb)
  (γβ : (pull_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X)).J)

def centerChartMap :
    Spec ((pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2) ⟶
      Spec (CommRingCat.of (M.cov.obj γβ.1 ⧸ M.Yideal i₀ γβ.1)) :=
  (pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).map γβ.2 ≫
    (M.YcondIso i₀ γβ.1).inv

def centerChartRing :
    CommRingCat.of (M.cov.obj γβ.1 ⧸ M.Yideal i₀ γβ.1) ⟶
      (pull_loc_cov X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ.1).obj γβ.2 :=
  Spec.preimage (M.centerChartMap i₀ γβ)

theorem pull_mor_ring_factor :
    pull_mor_ring X M.Drep (M.Ysub i₀) (M.Ysub i₀ ↘ X) γβ =
      CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1)) ≫
        M.centerChartRing i₀ γβ := by
  have hover := M.YcondOver i₀ γβ.1
  rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq] at hover
  have hsnd : pullback.snd (M.Ysub i₀ ↘ X) (M.Drep.cov.map γβ.1) =
      (M.YcondIso i₀ γβ.1).inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))) := by
    show pullback.snd (M.Ysub i₀ ↘ X) (M.cov.map γβ.1) = _
    rw [← hover, Iso.inv_hom_id_assoc]
  apply Spec.map_injective
  rw [spec_map_pull_mor_ring, Spec.map_comp, centerChartRing, Spec.map_preimage,
    centerChartMap, hsnd, Category.assoc]

instance : AlgebraicGeometry.Flat (M.centerChartMap i₀ γβ) := by
  unfold centerChartMap
  infer_instance

theorem centerChartRing_flat : RingHom.Flat (M.centerChartRing i₀ γβ).hom := by
  rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
  rw [centerChartRing, Spec.map_preimage]
  infer_instance

end Factor

section Single

theorem carsOnCenter_of_elemNzdOnCenter (i₀ : M.indnumb)
    (hSt : M.ElemNzdOnCenter i₀) : M.CarsOnCenter i₀ := by
  intro i γβ
  refine ⟨(M.centerChartRing i₀ γβ).hom
    (Ideal.Quotient.mk (M.Yideal i₀ γβ.1) (M.chartd γβ.1 i)), ?_, ?_⟩
  · letI : Submodule.IsPrincipal (M.Dideal i γβ.1) := M.Dprin i γβ.1
    rw [M.pull_mor_ring_factor i₀ γβ, CommRingCat.hom_comp, ← Ideal.map_map,
      show (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i₀ γβ.1))).hom =
        Ideal.Quotient.mk (M.Yideal i₀ γβ.1) from rfl,
      ← Ideal.span_singleton_generator (M.Dideal i γβ.1),
      Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  · exact RingHom.Flat.preserves_nonzeroDivisors
      (M.centerChartRing_flat i₀ γβ) (hSt i γβ.1)

theorem carsOnCenterAll_of_cartierDatum (hC : M.CartierDatum) : M.CarsOnCenterAll :=
  fun i₀ => M.carsOnCenter_of_elemNzdOnCenter i₀ (fun i γ => hC γ i₀ i)

end Single

section Redundant

variable (i₀ : M.indnumb) (s : M.indnumb → ℕ)

theorem presentIdeal_Y0lift_of_elemNzd (hY : M.CentersOver i₀)
    (hSt : M.ElemNzdOnCenter i₀) (γ : M.cov.J) :
    presentIdeal (M.Y0lift i₀ s hY (M.carsOnCenter_of_elemNzdOnCenter i₀ hSt))
        ((M.multiple s).dilatationCover) γ =
      ((M.multiple s).localMulticenter γ).genFracIdeal :=
  M.presentIdeal_Y0lift i₀ s hY (M.carsOnCenter_of_elemNzdOnCenter i₀ hSt) hSt γ

noncomputable def stage2SchemeIso_of_elemNzd (t : ℕ) (hY : M.CentersOver i₀)
    (hSt : M.ElemNzdOnCenter i₀) (hconst : M.ConstDivisor i₀) :
    (M.multiple (M.bump s t)).dilatation ≅
      (M.stage2 i₀ s t hY (M.carsOnCenter_of_elemNzdOnCenter i₀ hSt)).dilatation :=
  M.stage2SchemeIso i₀ s t hY (M.carsOnCenter_of_elemNzdOnCenter i₀ hSt) hSt hconst

theorem carsOnY_of_elemNzdOnQuot [Unique M.indnumb] (hSt : M.ElemNzdOnQuot) :
    M.CarsOnY :=
  M.carsOnCenter_of_elemNzdOnCenter default
    (fun i γ => by rw [Unique.eq_default i]; exact hSt γ)

theorem carsOnYAll_of_elemNzdOnQuotAll (hSt : M.ElemNzdOnQuotAll) : M.CarsOnYAll :=
  fun j => (M.restrict (fun _ : PUnit => j)).carsOnY_of_elemNzdOnQuot (hSt j)

noncomputable def iterateSchemeIso_of_elemNzd [Unique M.indnumb]
    (nu n : M.indnumb -> Nat) (hSt : M.ElemNzdOnQuot) :
    (M.multiple (nu + n)).dilatation ≅
      (M.secondStage nu n (M.carsOnY_of_elemNzdOnQuot hSt)).dilatation :=
  M.iterateSchemeIso nu n (M.carsOnY_of_elemNzdOnQuot hSt) hSt

theorem presentIdeal_strictTransform_of_elemNzd (θ : M.indnumb → ℕ)
    (i : M.indnumb) (hSt : M.ElemNzdOnQuotAll) (γ : M.cov.J) :
    presentIdeal (M.strictTransformTo θ i (M.carsOnYAll_of_elemNzdOnQuotAll hSt))
        ((M.multiple θ).dilatationCover) γ =
      Ideal.map (M.projChartRho θ i γ).hom (M.monoExceptIdeal θ i γ) :=
  M.presentIdeal_strictTransform θ i (M.carsOnYAll_of_elemNzdOnQuotAll hSt) hSt γ

end Redundant

end PreMultiCenter
end SchemeDilatation
