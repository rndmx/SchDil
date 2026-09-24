import IteratedMultiple
import DilatationCover
import MulticenterSpanEquiv
import PolyptychPanel

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

section IdealLemmas

variable {A : Type*} [CommRing A]

theorem Ideal.span_singleton_finset_prod {ι : Type*} (S : Finset ι) (g : ι → A) :
    Ideal.span {∏ s ∈ S, g s} = ∏ s ∈ S, Ideal.span {g s} := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Ideal.one_eq_top]
    exact Ideal.span_singleton_one
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih,
      Ideal.span_singleton_mul_span_singleton]

end IdealLemmas

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

def defDChartDatum (J : Finset M.indnumb) (j : M.indnumb) :
    ChartDatum X where
  cov := M.cov
  idl γ := ∏ s ∈ J.filter (fun s => j ≤ s), M.Dideal s γ
  compat a b hab := by
    rw [Ideal.map_finset_prod, Ideal.map_finset_prod]
    exact Finset.prod_congr rfl fun s _ => chartIdeal_agree M.Drep a b hab s

def defSpace (J : Finset M.indnumb) : PreMultiCenter X where
  indnumb := {j // j ∈ J}
  cov := M.cov
  Ysub j := M.Ysub j.1
  Dsub j := (M.defDChartDatum J j.1).glued
  Yover j := M.Yover j.1
  Dover j := ⟨(M.defDChartDatum J j.1).structureMap⟩
  Yideal j γ := M.Yideal j.1 γ
  Dideal j γ := ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ
  YcondIso j γ := M.YcondIso j.1 γ
  YcondOver j γ := M.YcondOver j.1 γ
  DcondIso j γ := asIso ((M.defDChartDatum J j.1).chartCompare γ)
  DcondOver j γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (M.defDChartDatum J j.1).chartCompare γ ≫
        pullback.snd ((M.defDChartDatum J j.1).structureMap) (M.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ)))
    exact (M.defDChartDatum J j.1).chartCompare_snd γ
  Dprin j γ := by
    classical
    refine ⟨⟨∏ s ∈ J.filter (fun s => j.1 ≤ s),
      (M.Dprin s γ).generator, ?_⟩⟩
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_finset_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      letI : Submodule.IsPrincipal (M.Dideal s γ) := M.Dprin s γ
      exact (Ideal.span_singleton_generator (M.Dideal s γ)).symm

@[simp] theorem defSpace_Yideal (J : Finset M.indnumb) (j : (M.defSpace J).indnumb)
    (γ : M.cov.J) : (M.defSpace J).Yideal j γ = M.Yideal j.1 γ := rfl

@[simp] theorem defSpace_Dideal (J : Finset M.indnumb) (j : (M.defSpace J).indnumb)
    (γ : M.cov.J) :
    (M.defSpace J).Dideal j γ = ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ := rfl

@[simp] theorem defSpace_cov (J : Finset M.indnumb) : (M.defSpace J).cov = M.cov := rfl

theorem defSpace_localMulticenter_ideal (J : Finset M.indnumb) (γ : M.cov.J)
    (j : (M.defSpace J).indnumb) :
    ((M.defSpace J).localMulticenter γ).ideal j =
      (Polyptych.restCenter (fun i => M.Yideal i γ)
        (fun i => (M.Dprin i γ).generator)
        J).ideal j := rfl

theorem defSpace_local_Dideal_span (J : Finset M.indnumb) (γ : M.cov.J)
    (j : (M.defSpace J).indnumb) :
    Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
      Ideal.span {Polyptych.elemOf
        (fun i => (M.Dprin i γ).generator)
        J j.1} := by
  classical
  letI : Submodule.IsPrincipal ((M.defSpace J).Dideal j γ) := (M.defSpace J).Dprin j γ
  have h1 : Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
      (M.defSpace J).Dideal j γ :=
    Ideal.span_singleton_generator ((M.defSpace J).Dideal j γ)
  rw [h1, defSpace_Dideal]
  simp only [Polyptych.elemOf]
  rw [Ideal.span_singleton_finset_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  letI : Submodule.IsPrincipal (M.Dideal s γ) := M.Dprin s γ
  exact (Ideal.span_singleton_generator (M.Dideal s γ)).symm

abbrev chartM (γ : M.cov.J) : M.indnumb → Ideal (M.cov.obj γ) :=
  fun i => M.Yideal i γ

abbrev chartd (γ : M.cov.J) : M.indnumb → M.cov.obj γ :=
  fun i => (M.Dprin i γ).generator

theorem defSpace_chart_agree (J : Finset M.indnumb) (γ : M.cov.J)
    (j : (M.defSpace J).indnumb) :
    ((M.defSpace J).localMulticenter γ).ideal j =
        (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).ideal j ∧
      Ideal.span {((M.defSpace J).localMulticenter γ).elem j} =
        Ideal.span {(Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j} :=
  ⟨rfl, M.defSpace_local_Dideal_span J γ j⟩

section ChartBridge

variable [Fintype M.indnumb]

def chartEquiv (J : Finset M.indnumb) (γ : M.cov.J) :
    Polyptych.Ring (M.chartM γ) (M.chartd γ) J ≃+*
      Multicenter.Dilatation ((M.defSpace J).localMulticenter γ) :=
  (Multicenter.spanEquiv (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J)
    (fun j => ((M.defSpace J).Dprin j γ).generator)
    (fun j => M.defSpace_local_Dideal_span J γ j)).toRingEquiv

@[simp] theorem chartEquiv_algebraMap (J : Finset M.indnumb) (γ : M.cov.J)
    (a : M.cov.obj γ) :
    M.chartEquiv J γ (algebraMap (M.cov.obj γ)
      (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) a) =
      algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) a :=
  (Multicenter.spanEquiv (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J)
    (fun j => ((M.defSpace J).Dprin j γ).generator)
    (fun j => M.defSpace_local_Dideal_span J γ j)).commutes a

def CartierDatum : Prop :=
  ∀ γ : M.cov.J, Polyptych.Cartier (M.chartM γ) (M.chartd γ)

def MonoDatum : Prop := ∀ γ : M.cov.J, Polyptych.Mono (M.chartM γ)

def DilRegular (J : Finset M.indnumb) : Prop :=
  ∀ (γ : M.cov.J) (i : M.indnumb), i ∉ J →
    Polyptych.CondR1 (M.chartM γ) J i ∧
      Polyptych.CondR2 (M.chartM γ) (M.chartd γ) J i

def panelChartIdeal (J : Finset M.indnumb)
    (i : M.indnumb)
    (γ : M.cov.J) : Ideal ((M.defSpace J).dilatationCover.obj γ) :=
  Ideal.map (M.chartEquiv J γ).toRingHom
    (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) J i))

theorem panelChartIdeal_eq (hC : M.CartierDatum) (hM : M.MonoDatum)
    (J : Finset M.indnumb) (i : M.indnumb) (hiJ : i ∉ J)
    (hreg : M.DilRegular J) (γ : M.cov.J) :
    M.panelChartIdeal J i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i) := by
  rw [panelChartIdeal, Polyptych.ker_panelHom_eq J i ((hC γ).at J i) (hM γ) hiJ
    (hreg γ i hiJ).1 (hreg γ i hiJ).2]

theorem panelChart_surjective (J : Finset M.indnumb)
    (i : M.indnumb) (γ : M.cov.J) :
    Function.Surjective (fun x => Polyptych.panelHom (M.chartM γ) (M.chartd γ) J i
      ((M.chartEquiv J γ).symm x)) :=
  (Polyptych.panelHom_surjective (M.chartM γ) (M.chartd γ) J i).comp
    (M.chartEquiv J γ).symm.surjective

end ChartBridge

end PreMultiCenter
end SchemeDilatation
