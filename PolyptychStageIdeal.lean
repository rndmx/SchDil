import PolyptychStage

/-!
# The panel chart ideal is `ker (F_J(i)^*)`

The second-stage centers of `panelStage` are defined by the chart ideals
`Ideal.map (panelChartRho) genFracIdeal`.  This file identifies them, through the chart
bridge `chartEquiv`, with the kernels `ker (F_J(i)^*)` of the ring-level theory — that is,
it verifies that `panelStage` really is the panel datum of Dubouloz-Mayeux.

The comparison is term by term.  Writing `E_k = ∏_{s ∈ J≥k} d_s`, the generators of
`genFracIdeal ((panelInt M J i).localMulticenter γ)` are the fractions `m / E_k` with
`m ∈ M_{min(i,k)}`, indexed by `k ∈ J ∪ {i}`; the generators of `panelSubIdeal` are the
`m / E_j` with `m ∈ M_j ∩ M_i`, `j ∈ J`, together with `σ_J^*(M_i)`.  Since the index set
is totally ordered, `M_{min(i,k)} = M_k ∩ M_i`, so:

* the `k ∈ J` terms match on the nose;
* the `k = i` term matches the `j₀`-term for `j₀ = min J≥i` when `J≥i ≠ ∅` (because then
  `E_{j₀} = E_i` and `M_i ⊆ M_{j₀}`), and equals `σ_J^*(M_i)` when `J≥i = ∅` (because then
  `E_i = 1` is a unit).

`panelFrac_span_eq` is the transfer lemma: two fractions with the same numerator and with
denominators generating the same ideal span the same ideal of the chart ring.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) (e : F.index → A)
  (hspan : ∀ i, Ideal.span {e i} = Ideal.span {F.elem i})

include hspan in
/-- The defining identity of `toElemReplace` on fractions. -/
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

/-- The defining identity of `panelChartRho` on fractions. -/
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

/-- The defining identity of `chartEquiv` on fractions. -/
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

/-- The `J`-part of a divisor of `restCenter` spans the corresponding product of the
divisor ideals. -/
theorem restCenter_elem_span (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    Ideal.span {(Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j} =
      ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γ := by
  classical
  show Ideal.span {Polyptych.elemOf (M.chartd γ) J j.1} = _
  simp only [Polyptych.elemOf]
  rw [Ideal.span_singleton_finset_prod]
  exact Finset.prod_congr rfl fun s _ => (M.local_Dideal_span' γ s).symm

/-- The image of `restCenter`'s divisor is a non-zero-divisor on the chart. -/
theorem restCenter_elem_nzd
    (j : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) :
    algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        ((Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).elem j) ∈
      nonZeroDivisors (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) :=
  M.defSpace_chart_prod_nzd J γ j.1

/-- **The fraction transfer lemma**: fractions with the same numerator and with
denominators generating the same ideal span the same ideal of the chart ring. -/
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

variable (J : Finset M.indnumb) (hC : M.CartierDatum) (hb : M.CarsOnCenterAll)
  (hM : M.MonoDatum)

/-- **The chart ideals of `panelStage` are the kernels `ker (F_J(i)^*)`** — that is,
`panelStage` is the panel datum of Dubouloz-Mayeux. -/
theorem panelStage_Yideal_eq (hreg : M.DilRegular J)
    (i : (M.panelStage J hC hb hM).indnumb) (γ : M.cov.J) :
    (M.panelStage J hC hb hM).Yideal i γ =
      Ideal.map (M.chartEquiv J γ).toRingHom
        (RingHom.ker (Polyptych.panelHom (M.chartM γ) (M.chartd γ) (hC γ) J i.1)) := by
  classical
  have hiJ : i.1 ∉ J := (Finset.mem_sdiff.mp i.2).2
  rw [Polyptych.ker_panelHom_eq (hC γ) (hM γ) J i.1 hiJ
    (hreg γ i.1 hiJ).1 (hreg γ i.1 hiJ).2]
  show Ideal.map (M.panelChartRho J i.1 γ hM).toRingHom
      (((M.panelInt J i.1).localMulticenter γ).genFracIdeal) = _
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Multicenter.genFracIdeal]
    refine iSup_le fun k => ?_
    rw [Ideal.span_le]
    rintro x ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    cases k with
    | some j =>
      have hmj : m ∈ M.Yideal j.1 γ := hM γ (min_le_right i.1 j.1) hm
      have hmi : m ∈ M.Yideal i.1 γ := hM γ (min_le_left i.1 j.1) hm
      have hspan := M.panelFrac_span_eq J i.1 γ hM (some j) j m hm hmj rfl
      have hmem : M.chartEquiv J γ (Dilatation.frac (Finsupp.single j 1)
          ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ)
            J).mem_largeIdealPow_single j hmj⟩) ∈
          Ideal.map (M.chartEquiv J γ).toRingHom
            (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) :=
        Ideal.mem_map_of_mem _ (Submodule.mem_sup_right
          (Submodule.mem_iSup_of_mem j (Ideal.subset_span ⟨m, hmj, hmi, rfl⟩)))
      refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
      rw [← hspan]
      exact Ideal.mem_span_singleton_self _
    | none =>
      by_cases hne : (J.filter (fun s => i.1 ≤ s)).Nonempty
      · obtain ⟨j₀, hj₀J, hij₀, hfil⟩ := M.panelKey_filter_eq J i.1 hne
        have hmj : m ∈ M.Yideal j₀ γ := hM γ hij₀ hm
        have hspan := M.panelFrac_span_eq J i.1 γ hM none ⟨j₀, hj₀J⟩ m hm hmj hfil.symm
        have hmem : M.chartEquiv J γ (Dilatation.frac (Finsupp.single
            (⟨j₀, hj₀J⟩ : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) 1)
            ⟨m, (Polyptych.restCenter (M.chartM γ) (M.chartd γ)
              J).mem_largeIdealPow_single ⟨j₀, hj₀J⟩ hmj⟩) ∈
            Ideal.map (M.chartEquiv J γ).toRingHom
              (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) :=
          Ideal.mem_map_of_mem _ (Submodule.mem_sup_right
            (Submodule.mem_iSup_of_mem ⟨j₀, hj₀J⟩
              (Ideal.subset_span ⟨m, hmj, hm, rfl⟩)))
        refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
        rw [← hspan]
        exact Ideal.mem_span_singleton_self _
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hunit : IsUnit (((M.panelInt J i.1).localMulticenter γ).elem none) := by
          rw [← Ideal.span_singleton_eq_top, M.panelInt_chart_span J i.1 γ none,
            show J.filter (fun s => M.panelKey J i.1 none ≤ s) = ∅ from hne,
            Finset.prod_empty, Ideal.one_eq_top]
        have hunitC : IsUnit (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
            (((M.panelInt J i.1).localMulticenter γ).elem none)) :=
          hunit.map (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        obtain ⟨v, hv⟩ := hunitC
        have hG := M.panelChartRho_frac J i.1 γ hM (Finsupp.single none 1)
          ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single none hm⟩
        rw [familyPow_single] at hG
        have hmemC : algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m ∈
            Ideal.map (M.chartEquiv J γ).toRingHom
              (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) := by
          have hkey : (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
              (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
              algebraMap ((M.defSpace J).cov.obj γ)
                (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m :=
            M.chartEquiv_algebraMap J γ m
          rw [← hkey]
          exact Ideal.mem_map_of_mem _
            (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hm))
        refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemC)) ?_
        refine Ideal.mem_span_singleton'.mpr ⟨↑v⁻¹, ?_⟩
        rw [← hG, ← hv, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
        rfl
  · rw [Ideal.map_le_iff_le_comap, Polyptych.panelSubIdeal]
    refine sup_le ?_ (iSup_le fun j => ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hkey : (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
          (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
          algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m :=
        M.chartEquiv_algebraMap J γ m
      have hG := M.panelChartRho_frac J i.1 γ hM (Finsupp.single none 1)
        ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single none hm⟩
      rw [familyPow_single] at hG
      rw [hkey, ← hG]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
        (((M.panelInt J i.1).localMulticenter γ).frac_mem_genFracIdeal none hm))
    · rw [Ideal.span_le]
      rintro x ⟨m, hmj, hmi, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      have hmk : m ∈ M.Yideal (min i.1 j.1) γ := by
        rcases le_total i.1 j.1 with h | h
        · rw [min_eq_left h]; exact hmi
        · rw [min_eq_right h]; exact hmj
      have hspan := M.panelFrac_span_eq J i.1 γ hM (some j) j m hmk hmj rfl
      have hmem : M.panelChartRho J i.1 γ hM (Dilatation.frac
          (Finsupp.single (some j) 1)
          ⟨m, ((M.panelInt J i.1).localMulticenter γ).mem_largeIdealPow_single
            (some j) hmk⟩) ∈
          Ideal.map (M.panelChartRho J i.1 γ hM).toRingHom
            (((M.panelInt J i.1).localMulticenter γ).genFracIdeal) :=
        Ideal.mem_map_of_mem _
          (((M.panelInt J i.1).localMulticenter γ).frac_mem_genFracIdeal (some j) hmk)
      refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
      rw [hspan]
      exact Ideal.mem_span_singleton_self _

end Identification

end PreMultiCenter
end SchemeDilatation
