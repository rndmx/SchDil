import PolyptychFwd

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter Family
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]
  [Fintype M.indnumb]

theorem pullback_PreClos_ideal_eq {X T : Scheme.{u+1}} (f : T ⟶ X) (Z : PreClos X)
    (i : Z.indnumb) (γβ : (pull_cov X Z T f).J) :
    (pullback_PreClos X T f Z).ideal i γβ =
      Ideal.map (pull_mor_ring X Z T f γβ).hom (Z.ideal i γβ.1) := rfl

theorem defSpace_Drep_ideal (K : Finset M.indnumb) (k : (M.defSpace K).indnumb)
    (γ : M.cov.J) :
    (M.defSpace K).Drep.ideal k γ =
      ∏ s ∈ K.filter (fun s => k.1 ≤ s), M.Dideal s γ := rfl

theorem filter_min_eq (S : Finset M.indnumb) (k : M.indnumb)
    (hne : (S.filter (fun s => k ≤ s)).Nonempty) :
    ∃ j₀ ∈ S, k ≤ j₀ ∧
      S.filter (fun s => j₀ ≤ s) = S.filter (fun s => k ≤ s) := by
  classical
  refine ⟨(S.filter (fun s => k ≤ s)).min' hne,
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1,
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, ?_⟩
  ext s
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, le_trans (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2 h.2⟩,
    fun h => ⟨h.1, Finset.min'_le _ s (Finset.mem_filter.mpr ⟨h.1, h.2⟩)⟩⟩

section PanelSubIdeal

variable (J : Finset M.indnumb)

theorem panelSubIdeal_le_panelStage_Yideal (hC : M.CartierDatum)
    (i : (M.panelStage J).indnumb) (γ : M.cov.J) :
    Ideal.map (M.chartEquiv J γ).toRingHom
        (Polyptych.panelSubIdeal (M.chartM γ) (M.chartd γ) J i.1) ≤
      (M.panelStage J).Yideal i γ := by
  rw [M.panelStage_Yideal_eq J i γ]
  exact Ideal.map_mono (Polyptych.panelSubIdeal_le_ker (M.chartM γ) (M.chartd γ) (hC γ) J i.1)

end PanelSubIdeal

section BwdChart

variable (J : Finset M.indnumb) (hC : M.CartierDatum)
  (hM : M.MonoDatum) (γ : M.cov.J)

theorem panelStage_chart_span (i : (M.panelStage J).indnumb) :
    Ideal.span {((M.panelStage J).localMulticenter γ).elem i} =
      Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ (Polyptych.Comp J).filter (fun s => i.1 ≤ s), M.Dideal s γ) := by
  letI : Submodule.IsPrincipal ((M.panelStage J).Dideal i γ) :=
    (M.panelStage J).Dprin i γ
  have h1 : Ideal.span {((M.panelStage J).localMulticenter γ).elem i} =
      (M.panelStage J).Dideal i γ :=
    Ideal.span_singleton_generator ((M.panelStage J).Dideal i γ)
  rw [h1]
  rfl

theorem panelStage_chart_gen_nzd (s : M.indnumb) :
    algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
        (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          ((M.localMulticenter γ).elem s)) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.panelStage J).localMulticenter γ)) := by
  classical
  by_cases hsJ : s ∈ J
  · exact Dilatation.nonzerodiv_of_nonzerodiv
      (F := (M.panelStage J).localMulticenter γ)
      (M.defSpace_chart_gen_nzd J γ s hsJ)
  · have hsC : s ∈ Polyptych.Comp J :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, hsJ⟩
    have h := nonzerodiv_image_single
      ((M.panelStage J).localMulticenter γ) ⟨s, hsC⟩
    have hB : Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        (∏ t ∈ (Polyptych.Comp J).filter (fun t => s ≤ t),
          (M.localMulticenter γ).elem t)} =
        Ideal.span {((M.panelStage J).localMulticenter γ).elem ⟨s, hsC⟩} := by
      rw [M.panelStage_chart_span J γ ⟨s, hsC⟩, Ideal.span_singleton_map]
      congr 1
      rw [Ideal.span_singleton_finset_prod]
      exact Finset.prod_congr rfl fun t _ => (M.local_Dideal_span' γ t).symm
    have hspan := congrArg (Ideal.map
      (algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation
          ((M.panelStage J).localMulticenter γ)) : _ →+* _)) hB
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span,
      Set.image_singleton] at hspan
    have hprod := nonZeroDivisors_of_span_singleton_eq hspan h
    rw [map_prod, map_prod] at hprod
    have hmem : s ∈ (Polyptych.Comp J).filter (fun t => s ≤ t) :=
      Finset.mem_filter.mpr ⟨hsC, le_rfl⟩
    rw [← Finset.mul_prod_erase _ _ hmem] at hprod
    exact (mul_mem_nonZeroDivisors.mp hprod).1

theorem panelStage_chart_prod_nzd (S : Finset M.indnumb) (k : M.indnumb) :
    algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
        (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) S k)) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((M.panelStage J).localMulticenter γ)) := by
  classical
  have hE : Polyptych.elemOf (M.chartd γ) S k =
      ∏ s ∈ S.filter (fun s => k ≤ s), (M.localMulticenter γ).elem s := rfl
  rw [hE, map_prod, map_prod]
  exact prod_mem fun s _ => M.panelStage_chart_gen_nzd J γ s

include hC in
theorem panelStage_chart_anchor (i : M.indnumb)
    (hi : i ∈ Polyptych.Comp J)
    (j₀ : (Polyptych.restCenter (M.chartM γ) (M.chartd γ) J).index) {m : M.cov.obj γ}
    (hmj : m ∈ M.Yideal j₀.1 γ) (hmi : m ∈ M.Yideal i γ) :
    algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m ∈
      (Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) J j₀.1)} :
        Ideal ((M.panelStage J).cov.obj γ)) *
        (M.panelStage J).Yideal ⟨i, hi⟩ γ := by
  have hring := Polyptych.algebraMap_mem_mul_ker (hC γ) J i j₀ hmj hmi
  have himg := Ideal.mem_map_of_mem (M.chartEquiv J γ).toRingHom hring
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    show (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
        (Polyptych.Ring (M.chartM γ) (M.chartd γ) J)
        (Polyptych.elemOf (M.chartd γ) J j₀.1)) =
        algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) J j₀.1) from
      M.chartEquiv_algebraMap J γ _] at himg
  rw [M.panelStage_Yideal_eq J ⟨i, hi⟩ γ]
  rw [show (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
      (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
      algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m from
    M.chartEquiv_algebraMap J γ m] at himg
  exact himg

theorem defSpace_chart_prod_span (S : Finset M.indnumb) (k : M.indnumb) :
    Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
        (∏ s ∈ S.filter (fun s => k ≤ s), M.Dideal s γ) =
      Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        (Polyptych.elemOf (M.chartd γ) S k)} := by
  classical
  rw [show (∏ s ∈ S.filter (fun s => k ≤ s), M.Dideal s γ) =
      Ideal.span {∏ s ∈ S.filter (fun s => k ≤ s),
        (M.localMulticenter γ).elem s} from by
    rw [Ideal.span_singleton_finset_prod]
    exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem panelStage_chart_elem_span (i : (M.panelStage J).indnumb) :
    Ideal.span {algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
        (((M.panelStage J).localMulticenter γ).elem i)} =
      Ideal.span {algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
        (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i.1))} := by
  have hB : Ideal.span {((M.panelStage J).localMulticenter γ).elem i} =
      Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
        (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i.1)} := by
    rw [M.panelStage_chart_span J γ i,
      M.defSpace_chart_prod_span J γ (Polyptych.Comp J) i.1]
  have h := congrArg (Ideal.map (algebraMap
    ((M.panelStage J).cov.obj γ)
    (Multicenter.Dilatation
      ((M.panelStage J).localMulticenter γ)) : _ →+* _)) hB
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at h
  exact h

include hC hM in
theorem panelStage_chart_M_le (k : M.indnumb) :
    Ideal.map ((algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation
          ((M.panelStage J).localMulticenter γ))).comp
      (algebraMap ((M.defSpace J).cov.obj γ)
        (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))))
        (M.Yideal k γ) ≤
      Ideal.span {algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
        (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) Finset.univ k))} := by
  classical
  have step : ∀ N : Ideal (Multicenter.Dilatation
      ((M.defSpace J).localMulticenter γ)),
      Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
          (M.Yideal k γ) ≤
        Ideal.span {algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) J k)} * N →
      Ideal.map (algebraMap ((M.panelStage J).cov.obj γ)
          (Multicenter.Dilatation
            ((M.panelStage J).localMulticenter γ))) N ≤
        Ideal.span {algebraMap ((M.panelStage J).cov.obj γ)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
          (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
            (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) k))} →
      Ideal.map ((algebraMap ((M.panelStage J).cov.obj γ)
          (Multicenter.Dilatation
            ((M.panelStage J).localMulticenter γ))).comp
        (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))))
          (M.Yideal k γ) ≤
        Ideal.span {algebraMap ((M.panelStage J).cov.obj γ)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ))
          (algebraMap ((M.defSpace J).cov.obj γ)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
            (Polyptych.elemOf (M.chartd γ) Finset.univ k))} := by
    intro N h1 h2
    rw [← Ideal.map_map]
    refine le_trans (Ideal.map_mono h1) ?_
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    have hmul : algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ)) (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) Finset.univ k)) =
        algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ)) (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) J k)) *
        algebraMap ((M.panelStage J).cov.obj γ)
        (Multicenter.Dilatation ((M.panelStage J).localMulticenter γ)) (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))
          (Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) k)) := by
      rw [Polyptych.elemOf_mul_of_subset (M.chartd γ) (Finset.subset_univ J) k,
        map_mul, map_mul]
    rw [hmul, ← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mono le_rfl h2
  by_cases hkJ : k ∈ J
  · by_cases hne : ((Polyptych.Comp J).filter (fun s => k ≤ s)).Nonempty
    · obtain ⟨i₀, hi₀C, hki₀, hfil⟩ := M.filter_min_eq (Polyptych.Comp J) k hne
      have helem : Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) i₀ =
          Polyptych.elemOf (M.chartd γ) (Polyptych.Comp J) k := by
        show (∏ s ∈ (Polyptych.Comp J).filter (fun s => i₀ ≤ s), M.chartd γ s) = _
        rw [hfil]
        rfl
      refine step ((M.panelStage J).Yideal
        (⟨i₀, hi₀C⟩ : (M.panelStage J).indnumb) γ) ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [Ideal.mem_comap]
        exact M.panelStage_chart_anchor J hC γ i₀ hi₀C ⟨k, hkJ⟩ hm
          (hM γ hki₀ hm)
      · refine le_trans (Multicenter.self_le
          ((M.panelStage J).localMulticenter γ)
          (⟨i₀, hi₀C⟩ : (M.panelStage J).indnumb)) ?_
        rw [M.panelStage_chart_elem_span J γ
          (⟨i₀, hi₀C⟩ : (M.panelStage J).indnumb), helem]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine step ⊤ ?_ ?_
      · rw [Ideal.mul_top]
        refine le_trans (M.defSpace_chart_self_le J γ k hkJ) (le_of_eq ?_)
        exact M.defSpace_chart_prod_span J γ J k
      · rw [Polyptych.elemOf_eq_one (M.chartd γ) (Polyptych.Comp J) k hne,
          map_one, map_one, Ideal.span_singleton_one]
        exact le_top
  · have hkC : k ∈ Polyptych.Comp J :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkJ⟩
    refine step ((M.panelStage J).Yideal ⟨k, hkC⟩ γ) ?_ ?_
    · by_cases hne : (J.filter (fun s => k ≤ s)).Nonempty
      · obtain ⟨j₀, hj₀J, hkj₀, hfil⟩ := M.filter_min_eq J k hne
        have helem : Polyptych.elemOf (M.chartd γ) J k =
            Polyptych.elemOf (M.chartd γ) J j₀ := by
          show (∏ s ∈ J.filter (fun s => k ≤ s), M.chartd γ s) = _
          rw [← hfil]
          rfl
        rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [Ideal.mem_comap, helem]
        exact M.panelStage_chart_anchor J hC γ k hkC ⟨j₀, hj₀J⟩
          (hM γ hkj₀ hm) hm
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [Polyptych.elemOf_eq_one (M.chartd γ) J k hne, map_one,
          Ideal.span_singleton_one, Ideal.top_mul,
          M.panelStage_Yideal_eq J ⟨k, hkC⟩ γ]
        rw [Ideal.map_le_iff_le_comap]
        intro m hm
        refine Ideal.mem_comap.mpr ?_
        have hmem := Ideal.mem_map_of_mem (M.chartEquiv J γ).toRingHom
          (Polyptych.panelSubIdeal_le_ker (M.chartM γ) (M.chartd γ) (hC γ) J k
            (Polyptych.algebraMap_mem_panelSubIdeal (M.chartM γ) (M.chartd γ) J k hm))
        rw [show (M.chartEquiv J γ).toRingHom (algebraMap (M.cov.obj γ)
            (Polyptych.Ring (M.chartM γ) (M.chartd γ) J) m) =
            algebraMap ((M.defSpace J).cov.obj γ)
              (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)) m from
          M.chartEquiv_algebraMap J γ m] at hmem
        exact hmem
    · refine le_trans (Multicenter.self_le
        ((M.panelStage J).localMulticenter γ) ⟨k, hkC⟩) ?_
      rw [M.panelStage_chart_elem_span J γ ⟨k, hkC⟩]

end BwdChart

section BwdPiece

variable (J : Finset M.indnumb) (hC : M.CartierDatum)
  (hM : M.MonoDatum)

theorem panelBackward_piece_factor (K : Finset M.indnumb)
    (γβ : (pull_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)).J) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation
        ((M.panelStage J).localMulticenter γβ.1)) ⟶
        (pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ.1).obj γβ.2,
      pull_mor_ring X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ =
        CommRingCat.ofHom ((algebraMap ((M.panelStage J).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γβ.1))).comp
          (algebraMap ((M.defSpace J).cov.obj γβ.1)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γβ.1)))) ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ.1).map γβ.2 ≫
      pullback.snd ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) ((M.defSpace K).Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcwB : (((pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) ((M.defSpace K).Drep.cov.map γβ.1)) ≫
      (M.panelStage J).structureMap) ≫ (M.defSpace J).structureMap =
      Spec.map (pull_mor_ring X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ) ≫
        (M.defSpace K).Drep.cov.map γβ.1 := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, hsnd]
  obtain ⟨sB, hsB1, hsB2⟩ := (M.defSpace J).exists_chart_factorisation' γβ.1 _ _ hcwB
  have hcwN : ((pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) ((M.defSpace K).Drep.cov.map γβ.1)) ≫
      (M.panelStage J).structureMap =
      Spec.map (Spec.preimage sB) ≫ (M.panelStage J).cov.map γβ.1 := by
    rw [Spec.map_preimage]
    exact hsB1.symm
  obtain ⟨sN, hsN1, hsN2⟩ := (M.panelStage J).exists_chart_factorisation' γβ.1 _ _ hcwN
  refine ⟨Spec.preimage sN, ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_comp, Spec.map_comp]
    have hsN2' : sN ≫ (M.panelStage J).chartHom γβ.1 = sB := by
      rw [hsN2, Spec.map_preimage]
    rw [← hsB2, ← hsN2']
    simp only [Category.assoc]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)
        γβ.1).map γβ.2 ≫ pullback.fst ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) ((M.defSpace K).Drep.cov.map γβ.1)) :=
      (pull_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)).map_prop γβ
    haveI hsc : IsOpenImmersion (sN ≫ (M.panelStage J).chartTo γβ.1) := by
      rw [hsN1]
      exact hc
    haveI hsn : IsOpenImmersion sN :=
      IsOpenImmersion.of_comp sN ((M.panelStage J).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sN := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sN)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

include hC hM in
theorem panelBackward_pullSubset_chart
    (k : (M.defSpace Finset.univ).indnumb)
    (γβ : (pull_cov X (M.defSpace Finset.univ).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)).J) :
    Ideal.map (pull_mor_ring X (M.defSpace Finset.univ).Drep (M.panelStage J).dilatation
        ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ).hom (M.Yideal k.1 γβ.1) ≤
      Ideal.map (pull_mor_ring X (M.defSpace Finset.univ).Drep (M.panelStage J).dilatation
        ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ).hom ((M.defSpace Finset.univ).Dideal k γβ.1) := by
  obtain ⟨ψ, hψ, -⟩ := M.panelBackward_piece_factor J Finset.univ γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (M.cov.obj γβ.1)),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp ((algebraMap ((M.panelStage J).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γβ.1))).comp
        (algebraMap ((M.defSpace J).cov.obj γβ.1)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γβ.1))))) I =
      Ideal.map (CommRingCat.Hom.hom ψ) (Ideal.map ((algebraMap ((M.panelStage J).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γβ.1))).comp
        (algebraMap ((M.defSpace J).cov.obj γβ.1)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γβ.1)))) I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  refine le_trans (M.panelStage_chart_M_le J hC hM γβ.1 k.1) (le_of_eq ?_)
  show _ = Ideal.map _ (∏ s ∈ Finset.univ.filter (fun s => k.1 ≤ s), M.Dideal s γβ.1)
  rw [← Ideal.map_map, M.defSpace_chart_prod_span J γβ.1 Finset.univ k.1,
    Ideal.map_span, Set.image_singleton]

include hC hM in
theorem panelBackward_pullSubset :
    (M.defSpace Finset.univ).pullSubset ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) :=
  ((M.defSpace Finset.univ).pullSubset_iff _).mpr
    (fun k γβ => M.panelBackward_pullSubset_chart J hC hM k γβ)

theorem panelBackward_isCars_chart (K : Finset M.indnumb)
    (k : (M.defSpace K).indnumb)
    (γβ : (pull_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)).J) :
    ∃ g : (pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)
        γβ.1).obj γβ.2,
      (pullback_PreClos X (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)
          (M.defSpace K).Drep).ideal k γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X (M.defSpace K).Drep (M.panelStage J).dilatation
        ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := M.panelBackward_piece_factor J K γβ
  refine ⟨ψ.hom ((algebraMap ((M.panelStage J).cov.obj γβ.1)
          (Multicenter.Dilatation ((M.panelStage J).localMulticenter γβ.1)))
      ((algebraMap ((M.defSpace J).cov.obj γβ.1)
            (Multicenter.Dilatation ((M.defSpace J).localMulticenter γβ.1)))
        (Polyptych.elemOf (M.chartd γβ.1) K k.1))), ?_, ?_⟩
  · rw [pullback_PreClos_ideal_eq, hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      ← Ideal.map_map, ← Ideal.map_map, M.defSpace_Drep_ideal K k γβ.1,
      M.defSpace_chart_prod_span J γβ.1 K k.1, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton]
  · exact hflat.preserves_nonzeroDivisors
      (M.panelStage_chart_prod_nzd J γβ.1 K k.1)

theorem panelBackward_isCars (K : Finset M.indnumb) :
    IsCars (M.panelStage J).dilatation (Clos.pullback ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) (M.defSpace K).D) :=
  ⟨pullback_PreClos X (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap) (M.defSpace K).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun k γβ => M.panelBackward_isCars_chart J K k γβ), rfl⟩

include hC hM in
theorem existsUnique_thetaJ :
    ∃! g : M.panelSpace J ⟶ (M.defSpace Finset.univ).dilatation,
      g ≫ (M.defSpace Finset.univ).structureMap = M.panelSpaceToX J :=
  (M.defSpace Finset.univ).universal_property (M.panelStage J).dilatation ((M.panelStage J).structureMap ≫ (M.defSpace J).structureMap)
    (M.panelBackward_isCars J Finset.univ)
    (M.panelBackward_pullSubset J hC hM)

def thetaJ :
    M.panelSpace J ⟶ (M.defSpace Finset.univ).dilatation :=
  (M.existsUnique_thetaJ J hC hM).choose

@[simp] theorem thetaJ_over :
    M.thetaJ J hC hM ≫ (M.defSpace Finset.univ).structureMap =
      M.panelSpaceToX J :=
  (M.existsUnique_thetaJ J hC hM).choose_spec.1

theorem thetaJ_unique
    (g : M.panelSpace J ⟶ (M.defSpace Finset.univ).dilatation)
    (hg : g ≫ (M.defSpace Finset.univ).structureMap = M.panelSpaceToX J) :
    g = M.thetaJ J hC hM :=
  (M.existsUnique_thetaJ J hC hM).choose_spec.2 g hg

end BwdPiece

section Theorem37

variable (J : Finset M.indnumb) (hC : M.CartierDatum)
  (hM : M.MonoDatum)

theorem thetaJ_comp_upsilonScheme :
    M.thetaJ J hC hM ≫ M.upsilonScheme (Finset.subset_univ J) =
      M.tauJ J := by
  refine ((M.defSpace J).universal_property (M.panelSpace J)
    (M.panelSpaceToX J)
    (M.panelBackward_isCars J J)
    ((M.defSpace J).pullSubset_of_over_dilatation'
      (M.tauJ J))).unique ?_ ?_
  · rw [Category.assoc, M.upsilonScheme_over (Finset.subset_univ J),
      M.thetaJ_over J hC hM]
  · exact rfl

theorem upsilonPanelSch_comp_thetaJ (hreg : M.DilRegular J) :
    M.upsilonPanelSch J hC hM hreg ≫ M.thetaJ J hC hM = 𝟙 _ := by
  refine ((M.defSpace Finset.univ).universal_property
    ((M.defSpace Finset.univ).dilatation) (M.defSpace Finset.univ).structureMap
    (M.defSpace Finset.univ).structureMap_isCars
    (M.defSpace Finset.univ).structureMap_pullSubset).unique ?_ (Category.id_comp _)
  rw [Category.assoc, M.thetaJ_over J hC hM]
  show M.upsilonPanelSch J hC hM hreg ≫ M.tauJ J ≫
    (M.defSpace J).structureMap = _
  rw [← Category.assoc, M.upsilonPanelSch_over J hC hM hreg,
    M.upsilonScheme_over (Finset.subset_univ J)]

theorem thetaJ_comp_upsilonPanelSch (hreg : M.DilRegular J) :
    M.thetaJ J hC hM ≫ M.upsilonPanelSch J hC hM hreg = 𝟙 _ := by
  refine ((M.panelStage J).universal_property ((M.panelStage J).dilatation)
    (M.panelStage J).structureMap (M.panelStage J).structureMap_isCars
    (M.panelStage J).structureMap_pullSubset).unique ?_ (Category.id_comp _)
  rw [Category.assoc]
  show M.thetaJ J hC hM ≫ M.upsilonPanelSch J hC hM hreg ≫
    M.tauJ J = _
  rw [M.upsilonPanelSch_over J hC hM hreg,
    M.thetaJ_comp_upsilonScheme J hC hM]
  rfl

def panelizationIso (hreg : M.DilRegular J) :
    M.panelSpace J ≅ (M.defSpace Finset.univ).dilatation where
  hom := M.thetaJ J hC hM
  inv := M.upsilonPanelSch J hC hM hreg
  hom_inv_id := M.thetaJ_comp_upsilonPanelSch J hC hM hreg
  inv_hom_id := M.upsilonPanelSch_comp_thetaJ J hC hM hreg

@[simp] theorem panelizationIso_hom_over (hreg : M.DilRegular J) :
    (M.panelizationIso J hC hM hreg).hom ≫ (M.defSpace Finset.univ).structureMap =
      M.panelSpaceToX J :=
  M.thetaJ_over J hC hM

theorem panelizationIso_unique (hreg : M.DilRegular J)
    (g : M.panelSpace J ⟶ (M.defSpace Finset.univ).dilatation)
    (hg : g ≫ (M.defSpace Finset.univ).structureMap = M.panelSpaceToX J) :
    g = (M.panelizationIso J hC hM hreg).hom :=
  M.thetaJ_unique J hC hM g hg

theorem dilRegular_of_gt (hgt : ∀ i ∈ Polyptych.Comp J, ∀ j ∈ J, j < i) :
    M.DilRegular J := by
  intro γ i hiJ
  have hi : i ∈ Polyptych.Comp J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiJ⟩
  exact ⟨Polyptych.condR1_of_gt J i (hgt i hi),
    Polyptych.condR2_of_gt J i (hgt i hi)⟩

def panelizationIsoOfGt (hgt : ∀ i ∈ Polyptych.Comp J, ∀ j ∈ J, j < i) :
    M.panelSpace J ≅ (M.defSpace Finset.univ).dilatation :=
  M.panelizationIso J hC hM (M.dilRegular_of_gt J hgt)

end Theorem37

end PreMultiCenter
end SchemeDilatation
