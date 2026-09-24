import PolyptychSchemeDatum
import IteratedSchemeMultiCore

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

section FinsetLemmas

theorem Finset.prod_filter_split {ι : Type*} [DecidableEq ι] {α : Type*} [CommMonoid α]
    {J K : Finset ι} (hJK : J ⊆ K) (p : ι → Prop) [DecidablePred p] (g : ι → α) :
    ∏ s ∈ K.filter p, g s =
      (∏ s ∈ J.filter p, g s) * (∏ s ∈ (K \ J).filter p, g s) := by
  have hsplit : K.filter p = J.filter p ∪ (K \ J).filter p := by
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset hJK]
  have hdisj : Disjoint (J.filter p) ((K \ J).filter p) := by
    refine Finset.disjoint_left.mpr fun a ha ha' => ?_
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha').1).2 (Finset.mem_filter.mp ha).1
  rw [hsplit]
  exact Finset.prod_union hdisj

end FinsetLemmas

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

section ChartSpan

variable (J : Finset M.indnumb)

theorem defSpace_Dideal_span (γ : M.cov.J) (j : M.indnumb) :
    (∏ s ∈ J.filter (fun s => j ≤ s), M.Dideal s γ) =
      Ideal.span {∏ s ∈ J.filter (fun s => j ≤ s),
        ((M.localMulticenter γ).elem s)} := by
  rw [Ideal.span_singleton_finset_prod]
  exact Finset.prod_congr rfl fun s _ => M.local_Dideal_span' γ s

theorem defSpace_Dideal_map_span {B : Type (u+1)} [CommRing B]
    (γ : M.cov.J) (f : M.cov.obj γ →+* B) (j : M.indnumb) :
    Ideal.map f (∏ s ∈ J.filter (fun s => j ≤ s), M.Dideal s γ) =
      Ideal.span {f (∏ s ∈ J.filter (fun s => j ≤ s),
        ((M.localMulticenter γ).elem s))} := by
  rw [M.defSpace_Dideal_span J γ j, Ideal.map_span, Set.image_singleton]

end ChartSpan

section Nzd

variable (K : Finset M.indnumb)

theorem defSpace_gen_nzd (s : M.indnumb) (hs : s ∈ K)
    (γβ : (pull_cov X M.Drep (M.defSpace K).dilatation
      (M.defSpace K).structureMap).J) :
    (pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom ((M.localMulticenter γβ.1).elem s) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ.1).obj γβ.2) := by
  classical
  obtain ⟨g, hg, hgnzd⟩ := (M.defSpace K).structureMap_isCars_chart ⟨s, hs⟩ γβ
  have hprod : (pull_mor_ring X M.Drep (M.defSpace K).dilatation
      (M.defSpace K).structureMap γβ).hom
      (∏ t ∈ K.filter (fun t => s ≤ t), ((M.localMulticenter γβ.1).elem t)) ∈
      nonZeroDivisors ((pull_loc_cov X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ.1).obj γβ.2) := by
    refine nonZeroDivisors_of_span_singleton_eq ?_ hgnzd
    rw [← hg]
    show Ideal.span {(pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom
        (∏ t ∈ K.filter (fun t => s ≤ t), ((M.localMulticenter γβ.1).elem t))} =
      Ideal.map (pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom
        (∏ t ∈ K.filter (fun t => s ≤ t), M.Dideal t γβ.1)
    rw [M.defSpace_Dideal_map_span K γβ.1 _ s]
    rfl
  have hmem : s ∈ K.filter (fun t => s ≤ t) :=
    Finset.mem_filter.mpr ⟨hs, le_rfl⟩
  rw [← Finset.mul_prod_erase _ _ hmem, map_mul] at hprod
  exact (mul_mem_nonZeroDivisors.mp hprod).1

end Nzd

section Upsilon

variable {J K : Finset M.indnumb} (hJK : J ⊆ K)

include hJK in
theorem defSpace_isCars_chart (j : (M.defSpace J).indnumb)
    (γβ : (pull_cov X M.Drep (M.defSpace K).dilatation
      (M.defSpace K).structureMap).J) :
    ∃ g : (pull_loc_cov X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ.1).obj γβ.2,
      (pullback_PreClos X (M.defSpace K).dilatation
          (M.defSpace K).structureMap (M.defSpace J).Drep).ideal j γβ =
        Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ.1).obj γβ.2) := by
  classical
  refine ⟨(pull_mor_ring X M.Drep (M.defSpace K).dilatation
      (M.defSpace K).structureMap γβ).hom
      (∏ s ∈ J.filter (fun s => j.1 ≤ s), ((M.localMulticenter γβ.1).elem s)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom
        (∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γβ.1) = _
    rw [M.defSpace_Dideal_map_span J γβ.1 _ j.1]
    rfl
  · rw [map_prod]
    exact prod_mem fun s hs =>
      M.defSpace_gen_nzd K s (hJK (Finset.mem_filter.mp hs).1) γβ

include hJK in
theorem defSpace_isCars :
    IsCars (M.defSpace K).dilatation
      (Clos.pullback (M.defSpace K).structureMap (M.defSpace J).D) :=
  ⟨pullback_PreClos X (M.defSpace K).dilatation
      (M.defSpace K).structureMap (M.defSpace J).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun j γβ => M.defSpace_isCars_chart hJK j γβ),
    rfl⟩

include hJK in
theorem defSpace_pullSubset_chart (j : (M.defSpace J).indnumb)
    (γβ : (pull_cov X M.Drep (M.defSpace K).dilatation
      (M.defSpace K).structureMap).J) :
    Ideal.map (pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom (M.Yideal j.1 γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep (M.defSpace K).dilatation
        (M.defSpace K).structureMap γβ).hom
        (∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γβ.1) := by
  classical
  have h1 := (M.defSpace K).structureMap_pullSubset ⟨j.1, hJK j.2⟩ γβ
  refine le_trans h1 (Ideal.map_mono ?_)
  show (∏ s ∈ K.filter (fun s => j.1 ≤ s), M.Dideal s γβ.1) ≤
    ∏ s ∈ J.filter (fun s => j.1 ≤ s), M.Dideal s γβ.1
  rw [Finset.prod_filter_split hJK (fun s => j.1 ≤ s) (fun s => M.Dideal s γβ.1)]
  exact Ideal.mul_le_right

include hJK in
theorem defSpace_pullSubset :
    (M.defSpace J).pullSubset (M.defSpace K).structureMap :=
  ((M.defSpace J).pullSubset_iff (M.defSpace K).structureMap).mpr
    (fun j γβ => M.defSpace_pullSubset_chart hJK j γβ)

include hJK in
theorem existsUnique_upsilonScheme :
    ∃! φ : (M.defSpace K).dilatation ⟶ (M.defSpace J).dilatation,
      φ ≫ (M.defSpace J).structureMap = (M.defSpace K).structureMap :=
  (M.defSpace J).universal_property (M.defSpace K).dilatation
    (M.defSpace K).structureMap (M.defSpace_isCars hJK) (M.defSpace_pullSubset hJK)

include hJK in
def upsilonScheme : (M.defSpace K).dilatation ⟶ (M.defSpace J).dilatation :=
  (M.existsUnique_upsilonScheme hJK).choose

include hJK in
@[simp] theorem upsilonScheme_over :
    M.upsilonScheme hJK ≫ (M.defSpace J).structureMap = (M.defSpace K).structureMap :=
  (M.existsUnique_upsilonScheme hJK).choose_spec.1

include hJK in
theorem upsilonScheme_unique
    (g : (M.defSpace K).dilatation ⟶ (M.defSpace J).dilatation)
    (hg : g ≫ (M.defSpace J).structureMap = (M.defSpace K).structureMap) :
    g = M.upsilonScheme hJK :=
  (M.existsUnique_upsilonScheme hJK).choose_spec.2 g hg

end Upsilon

end PreMultiCenter
end SchemeDilatation
