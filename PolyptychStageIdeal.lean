import PolyptychStage

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)
  (e : F.index → A)
  (hspan : ∀ i, Ideal.span {e i} = Ideal.span {F.elem i})

include hspan in
theorem toElemReplace_frac (ν : F.index →₀ ℕ) (m : F.LargeIdeal ^ ν) :
    algebraMap A A[F.elemReplace e] (F.elem ^ ν) *
        F.toElemReplace e hspan (Dilatation.frac ν m) =
      algebraMap A A[F.elemReplace e] (m : A) :=
  dsc_spec F ν m (F.elemReplace_elem_nzd e hspan)
    (fun i => (gen_iff_le F i).mpr
      (le_trans (Multicenter.self_le (F.elemReplace e) i)
        (le_of_eq (F.span_algebraMap_eq e hspan i))))

end Multicenter

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

section FracTransfer

variable (J : Finset M.indnumb) (i : M.indnumb) (γ : M.cov.J) (hM : M.MonoDatum)

theorem panelChartRho_frac (ν : ((M.panelInt J i).localMulticenter γ).index →₀ ℕ)
    (m : ((M.panelInt J i).localMulticenter γ).LargeIdeal ^ ν) :
    algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        (((M.panelInt J i).localMulticenter γ).elem ^ ν) *
        M.panelChartRho J i γ hM (Dilatation.frac ν m) =
      algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m.1 :=
  dsc_spec ((M.panelInt J i).localMulticenter γ) ν m (M.panelChartRho_nzd J i γ)
    (fun k => (gen_iff_le ((M.panelInt J i).localMulticenter γ) k).mpr
      (M.panelChartRho_gen J i γ hM k))

theorem chartEquiv_frac
    (ν : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index →₀ ℕ)
    (m : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).LargeIdeal ^ ν) :
    algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem ^ ν) *
        M.chartEquiv J γ (Dilatation.frac ν m) =
      algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m.1 :=
  Multicenter.toElemReplace_frac (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J)
    (fun j => ((M.defSpace J).Dprin j γ).generator)
    (fun j => M.defSpace_local_Dideal_span J γ j) ν m

theorem restCenter_elem_span (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    Ideal.span {(Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j} =
      ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ := by
  classical
  show Ideal.span {Polyptych.elemOf (M.chartd γ) J j.1} = _
  simp only [Polyptych.elemOf]
  rw [Ideal.span_singleton_finset_prod]
  exact Finset.prod_congr rfl fun s _ => (M.local_Dideal_span' γ s).symm

theorem restCenter_elem_nzd
    (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) :=
  M.defSpace_chart_prod_nzd J γ j.1

theorem panelFrac_span_eq (k : ((M.panelInt J i).localMulticenter γ).index)
    (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) (m : M.cov.obj γ)
    (hmk : m ∈ ((M.panelInt J i).localMulticenter γ).ideal k)
    (hmj : m ∈ (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).ideal j)
    (hfil : J.filter (fun s => M.panelKey J i k ≤ s) =
      J.filter (fun s => j.1 ≤ s)) :
    Ideal.span {M.panelChartRho J i γ hM (Dilatation.frac (Finsupp.single k 1)
        ⟨m, ((M.panelInt J i).localMulticenter γ).mem_largeIdealPow_single k hmk⟩)} =
      Ideal.span {M.chartEquiv J γ (Dilatation.frac (Finsupp.single j 1)
        ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).mem_largeIdealPow_single
          j hmj⟩)} := by
  classical
  have hden : Ideal.span {((M.panelInt J i).localMulticenter γ).elem k} =
      Ideal.span {(Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j} := by
    rw [M.panelInt_chart_span J i γ k, hfil, M.restCenter_elem_span J γ j]
  have hdenC : Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        (((M.panelInt J i).localMulticenter γ).elem k)} =
      Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j)} := by
    rw [Ideal.span_singleton_map, Ideal.span_singleton_map, hden]
  have hnzdR := M.restCenter_elem_nzd J γ j
  have hG := M.panelChartRho_frac J i γ hM (Finsupp.single k 1)
    ⟨m, ((M.panelInt J i).localMulticenter γ).mem_largeIdealPow_single k hmk⟩
  have hR := M.chartEquiv_frac J γ (Finsupp.single j 1)
    ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).mem_largeIdealPow_single
      j hmj⟩
  rw [familyPow_single] at hG hR
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp
    (hdenC ▸ Ideal.mem_span_singleton_self (algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
      (((M.panelInt J i).localMulticenter γ).elem k)))
  obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp
    (hdenC.symm ▸ Ideal.mem_span_singleton_self (algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
      ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j)))
  refine le_antisymm ?_ ?_ <;>
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.mem_span_singleton']
  · refine ⟨w', ?_⟩
    refine (mul_cancel_left_mem_nonZeroDivisors hnzdR).mp ?_
    rw [← mul_assoc, mul_comm _ w', mul_assoc, hR, ← hw', mul_assoc, hG]
  · refine ⟨w, ?_⟩
    refine (mul_cancel_left_mem_nonZeroDivisors hnzdR).mp ?_
    rw [← mul_assoc, mul_comm _ w, hw, hG, hR]

end FracTransfer

section Identification

variable (J : Finset M.indnumb)

theorem panelStage_Yideal_eq (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    (M.panelStage J).Yideal i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) J i.1)) := rfl

end Identification

end PreMultiCenter
end SchemeDilatation
