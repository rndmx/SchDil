import RestrictedChart

/-!
# The chart comparison for `(𝔻_J)_i ⟶ 𝔻_J`

On the chart `γ`, the comparison morphism `panelHomScheme` is `Spec` of the ring map
`F_J(i)^*` -- transported through the two chart bridges `chartEquiv` and `restChartEquiv`
and the ring-level identification `panelCodomEquiv` of `PolyptychRestricted`.

Consequently the chart map is **surjective** with kernel the panel ideal
`panelChartIdeal = ker(F_J(i)^*)`, which is what makes `panelHomScheme` a closed immersion
with the expected chart ideal.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

/-- Membership in the image of an ideal under a ring isomorphism. -/
theorem RingEquiv.mem_ideal_map_iff {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K : Ideal R) (x : S) :
    x ∈ Ideal.map (e : R →+* S) K ↔ e.symm x ∈ K := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).mp hx
    simpa using hy
  · intro hx
    simpa using Ideal.mem_map_of_mem (e : R →+* S) hx

namespace SchemeDilatation

namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb] (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J)

section RestRho

variable (hC : M.CartierDatum)

/-- **The chart comparison ring map** `chart_γ(𝔻_J) → chart_γ((𝔻_J)_i)`: it is
`F_J(i)^*` read through the chart bridges. -/
def restChartRho :
    Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) →+*
      Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ) :=
  RingHom.comp (M.restChartEquiv J i γ).toRingHom
    (RingHom.comp
      (Polyptych.panelCodomEquiv (M := M.chartM γ) (d := M.chartd γ) J i).toRingEquiv.toRingHom
      (RingHom.comp
        (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i).toRingHom
        (M.chartEquiv J γ).symm.toRingHom))

theorem restChartRho_apply (x : Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) :
    M.restChartRho J i γ hC x =
      M.restChartEquiv J i γ
        (Polyptych.panelCodomEquiv J i
          (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i
            ((M.chartEquiv J γ).symm x))) := rfl

theorem restChartRho_surjective : Function.Surjective (M.restChartRho J i γ hC) := by
  intro y
  obtain ⟨z, hz⟩ := (M.restChartEquiv J i γ).surjective y
  obtain ⟨w, hw⟩ := (Polyptych.panelCodomEquiv
    (M := M.chartM γ) (d := M.chartd γ) J i).surjective z
  obtain ⟨v, hv⟩ := Polyptych.panelHom_surjective
    (M.chartM γ) (M.chartd γ) (hC γ) J i w
  exact ⟨M.chartEquiv J γ v, by
    rw [M.restChartRho_apply J i γ hC, RingEquiv.symm_apply_apply, hv, hw, hz]⟩

/-- **The kernel of the chart comparison is the panel ideal** `ker(F_J(i)^*)`. -/
theorem ker_restChartRho :
    RingHom.ker (M.restChartRho J i γ hC) = M.panelChartIdeal hC J i γ := by
  ext x
  rw [RingHom.mem_ker, M.restChartRho_apply J i γ hC, panelChartIdeal]
  rw [show (Ideal.map (M.chartEquiv J γ).toRingHom
      (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i)) :
      Ideal (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))) =
      Ideal.map ((M.chartEquiv J γ) : _ →+* _)
        (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i)) from rfl]
  rw [RingEquiv.mem_ideal_map_iff, RingHom.mem_ker]
  constructor
  · intro h
    have h1 := (M.restChartEquiv J i γ).injective (by
      rw [h, map_zero] :
      M.restChartEquiv J i γ (Polyptych.panelCodomEquiv J i
        (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i
          ((M.chartEquiv J γ).symm x))) = M.restChartEquiv J i γ 0)
    exact (Polyptych.panelCodomEquiv (M := M.chartM γ) (d := M.chartd γ) J i).injective
      (by rw [h1, map_zero])
  · intro h
    rw [h, map_zero, map_zero]

/-- The chart comparison is compatible with the base rings: on `𝔻_J` it is induced by
`A_γ ↠ A_γ ⧸ M_i`. -/
theorem restChartRho_algebraMap (a : M.cov.obj γ) :
    M.restChartRho J i γ hC (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) a) =
      algebraMap ((M.restCenterScheme J i).cov.obj γ)
        (Multicenter.Dilatation ((M.restCenterScheme J i).localMulticenter γ))
        (Ideal.Quotient.mk (M.Yideal i γ) a) := by
  rw [M.restChartRho_apply J i γ hC]
  rw [show (M.chartEquiv J γ).symm (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) a) =
      algebraMap (M.cov.obj γ)
        (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) a from
    (M.chartEquiv J γ).symm_apply_eq.mpr (M.chartEquiv_algebraMap J γ a).symm]
  rw [AlgHom.commutes]
  rw [show (algebraMap (M.cov.obj γ)
        ((M.cov.obj γ ⧸ M.Yideal i γ)[(Polyptych.restCenter
          (M.chartM γ) (M.chartd γ) J).quotCenter (M.chartM γ i)]) a) =
      algebraMap (M.cov.obj γ ⧸ M.Yideal i γ) _
        (Ideal.Quotient.mk (M.Yideal i γ) a) from rfl]
  rw [AlgEquiv.commutes]
  exact M.restChartEquiv_algebraMap J i γ (Ideal.Quotient.mk (M.Yideal i γ) a)

/-- The scheme-level chart comparison `chart_γ((𝔻_J)_i) ⟶ chart_γ(𝔻_J)`. -/
def restRhoSch : (M.restCenterScheme J i).chart γ ⟶ (M.defSpace J).chart γ :=
  Spec.map (CommRingCat.ofHom (M.restChartRho J i γ hC))

theorem restRhoSch_chartHom :
    M.restRhoSch J i γ hC ≫ (M.defSpace J).chartHom γ =
      (M.restCenterScheme J i).chartHom γ ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (M.Yideal i γ))) := by
  rw [restRhoSch]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact M.restChartRho_algebraMap J i γ hC a

end RestRho

end PreMultiCenter

end SchemeDilatation
