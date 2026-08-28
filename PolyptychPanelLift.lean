import PolyptychPanelChart

/-!
# The panel `(𝔻_J)ᵢ` as a closed subscheme, and its chart ideals on `𝔻_J`

All centers of `panelBase M J i` lie in `Xᵢ` (`panelBase_centersOver`), so `SchemeFact51`
lifts `Xᵢ` to a closed immersion

`panelLift : Xᵢ ⟶ 𝔻(panelInt M J i)`

whose chart ideals are the Fact 5.1 ideal `genFracIdeal` — which, by the kernel formula,
is exactly `ker(F_J(i)^*)`.  Pulling this back along `panelProj : 𝔻_J → 𝔻(panelInt)` gives
the panel `(𝔻_J)ᵢ`; its chart ideals on `𝔻_J` are
`Ideal.map (panelChartRho) genFracIdeal`, and their `ChartDatum.compat` obligation is
inherited from `chartIdeal_agree` for the globally defined `panelLift`, exactly as in
`IteratedSchemeMultiCore.strictYChartDatum`.

The two hypotheses of `SchemeFact51` are Assumption 3.1 in its two chart forms:
`CarsOnCenter` (on the canonical covering of `Xᵢ ×_X U_γ`) and `CartierDatum`
(on the charts of `X`); both transfer to `panelBase` because its divisors are *products*
of the `Dₛ`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

section Hypotheses

/-- Assumption 3.1 in the form of `SchemeFact51.CarsOnCenter`, for every center. -/
def CarsOnCenterAll : Prop := ∀ i : M.indnumb, M.CarsOnCenter i

variable (J : Finset M.indnumb) (i : M.indnumb)

/-- The divisors of `panelBase M J i` — products of the `Dₛ` — restrict to Cartier
divisors on `Xᵢ`. -/
theorem panelBase_carsOnCenter (hb : M.CarsOnCenterAll) :
    (M.panelBase J i).CarsOnCenter (M.panelIdx J i) := by
  classical
  intro k γβ
  choose g hg hgnzd using fun s => hb i s γβ
  refine ⟨∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), g s, ?_, ?_⟩
  · show Ideal.map _
      (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γβ.1) = _
    rw [Ideal.map_finset_prod, Ideal.span_singleton_finset_prod]
    exact Finset.prod_congr rfl fun s _ => hg s
  · exact prod_mem fun s _ => hgnzd s

/-- The distinguished elements of `panelBase M J i` stay non-zero-divisors modulo the
ideal of `Xᵢ`. -/
theorem panelBase_elemNzdOnCenter (hC : M.CartierDatum) :
    (M.panelBase J i).ElemNzdOnCenter (M.panelIdx J i) := by
  classical
  intro k γ
  have hspan : Ideal.span {((M.panelBase J i).localMulticenter γ).elem k} =
      Ideal.span {∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s),
        (M.localMulticenter γ).elem s} := by
    letI : Submodule.IsPrincipal ((M.panelBase J i).Dideal k γ) :=
      (M.panelBase J i).Dprin k γ
    have h1 : Ideal.span {((M.panelBase J i).localMulticenter γ).elem k} =
        (M.panelBase J i).Dideal k γ :=
      Ideal.span_singleton_generator ((M.panelBase J i).Dideal k γ)
    rw [h1]
    show (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s), M.Dideal s γ) = _
    rw [Ideal.span_singleton_finset_prod]
    exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s
  have hprod : Ideal.Quotient.mk (M.Yideal i γ)
      (∏ s ∈ J.filter (fun s => M.panelKey J i k ≤ s),
        (M.localMulticenter γ).elem s) ∈
      nonZeroDivisors ((M.cov.obj γ) ⧸ M.Yideal i γ) := by
    rw [map_prod]
    exact prod_mem fun s _ => hC γ i s
  refine nonZeroDivisors_of_span_singleton_eq ?_ hprod
  have h0 := congrArg
    (Ideal.map (Ideal.Quotient.mk (M.Yideal i γ) : _ →+* _)) hspan
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at h0
  exact h0

end Hypotheses

section Lift

/-- **The panel `(𝔻_J)ᵢ` on the intermediate space**: the lift of `Xᵢ` to
`𝔻(panelInt M J i)`, a closed immersion by [Ma24, §5 preamble]. -/
def panelLift (J : Finset M.indnumb) (i : M.indnumb) (hb : M.CarsOnCenterAll)
    (hM : M.MonoDatum) : M.Ysub i ⟶ (M.panelInt J i).dilatation :=
  (M.panelBase J i).Y0lift (M.panelIdx J i) (fun _ => 1)
    (M.panelBase_centersOver hM J i) (M.panelBase_carsOnCenter J i hb)

instance panelLift_isClosedImmersion (J : Finset M.indnumb) (i : M.indnumb)
    (hb : M.CarsOnCenterAll) (hM : M.MonoDatum) :
    IsClosedImmersion (M.panelLift J i hb hM) :=
  (M.panelBase J i).Y0lift_isClosedImmersion (M.panelIdx J i) (fun _ => 1)
    (M.panelBase_centersOver hM J i) (M.panelBase_carsOnCenter J i hb)

/-- **The chart ideal of the panel on the intermediate space** is the Fact 5.1 ideal. -/
theorem panelLift_presentIdeal (J : Finset M.indnumb) (i : M.indnumb)
    (hC : M.CartierDatum) (hb : M.CarsOnCenterAll) (hM : M.MonoDatum)
    (γ : M.cov.J) :
    presentIdeal (M.panelLift J i hb hM) ((M.panelInt J i).dilatationCover) γ =
      ((M.panelInt J i).localMulticenter γ).genFracIdeal :=
  (M.panelBase J i).presentIdeal_Y0lift (M.panelIdx J i) (fun _ => 1)
    (M.panelBase_centersOver hM J i) (M.panelBase_carsOnCenter J i hb)
    (M.panelBase_elemNzdOnCenter J i hC) γ

/-- **The chart datum of the panel `(𝔻_J)ᵢ` on `𝔻_J`**: the Fact 5.1 ideal of the
intermediate space, extended along the chart comparison.  Compatibility is inherited from
the globally defined `panelLift`. -/
def panelYChartDatum (J : Finset M.indnumb) (i : M.indnumb)
    (hC : M.CartierDatum) (hb : M.CarsOnCenterAll) (hM : M.MonoDatum) :
    ChartDatum (M.defSpace J).dilatation where
  cov := (M.defSpace J).dilatationCover
  idl γ := Ideal.map (M.panelChartRho J i γ hM).toRingHom
    (((M.panelInt J i).localMulticenter γ).genFracIdeal)
  compat {W} _ {γ γ'} a b hab := by
    haveI : IsClosedImmersion (M.panelLift J i hb hM) := inferInstance
    have hab' : (a ≫ M.panelRhoSch J i γ hM) ≫
        (M.panelInt J i).dilatationCover.map γ =
        (b ≫ M.panelRhoSch J i γ' hM) ≫
        (M.panelInt J i).dilatationCover.map γ' := by
      show (a ≫ M.panelRhoSch J i γ hM) ≫ (M.panelInt J i).chartTo γ =
        (b ≫ M.panelRhoSch J i γ' hM) ≫ (M.panelInt J i).chartTo γ'
      rw [Category.assoc, Category.assoc, ← M.panel_chart_cone J i hM γ,
        ← M.panel_chart_cone J i hM γ', ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ M.panelProj J i hM) hab
    have h := chartIdeal_agree
      (presentPreClos (M.panelLift J i hb hM) ((M.panelInt J i).dilatationCover))
      (a ≫ M.panelRhoSch J i γ hM) (b ≫ M.panelRhoSch J i γ' hM) hab' PUnit.unit
    rw [presentPreClos_ideal, presentPreClos_ideal,
      M.panelLift_presentIdeal J i hC hb hM γ,
      M.panelLift_presentIdeal J i hC hb hM γ'] at h
    have hpa : Spec.preimage (W.isoSpec.inv ≫ a ≫ M.panelRhoSch J i γ hM) =
        CommRingCat.ofHom (M.panelChartRho J i γ hM).toRingHom ≫
          Spec.preimage (W.isoSpec.inv ≫ a) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ a ≫ M.panelRhoSch J i γ hM =
        (W.isoSpec.inv ≫ a) ≫ M.panelRhoSch J i γ hM
      rw [Category.assoc]
    have hpb : Spec.preimage (W.isoSpec.inv ≫ b ≫ M.panelRhoSch J i γ' hM) =
        CommRingCat.ofHom (M.panelChartRho J i γ' hM).toRingHom ≫
          Spec.preimage (W.isoSpec.inv ≫ b) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ b ≫ M.panelRhoSch J i γ' hM =
        (W.isoSpec.inv ≫ b) ≫ M.panelRhoSch J i γ' hM
      rw [Category.assoc]
    rw [hpa, hpb, CommRingCat.hom_comp, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← Ideal.map_map,
      ← Ideal.map_map] at h
    exact h

@[simp] theorem panelYChartDatum_idl (J : Finset M.indnumb) (i : M.indnumb)
    (hC : M.CartierDatum) (hb : M.CarsOnCenterAll) (hM : M.MonoDatum)
    (γ : M.cov.J) :
    (M.panelYChartDatum J i hC hb hM).idl γ =
      Ideal.map (M.panelChartRho J i γ hM).toRingHom
        (((M.panelInt J i).localMulticenter γ).genFracIdeal) := rfl

end Lift

end PreMultiCenter
end SchemeDilatation
