import PolyptychPanelBase
import PolyptychStage
import SchemeDefSpaceSum

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Multicenter
open Polyptych

namespace SchemeDilatation
namespace PreMultiCenter

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) [LinearOrder M.indnumb]

theorem Dprod_insert (K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K)
    (c : M.indnumb) (γ : M.cov.J) :
    ∏ s ∈ (insert a K).filter (fun s => c ≤ s), M.Dideal s γ =
      (∏ s ∈ K.filter (fun s => c ≤ s), M.Dideal s γ) *
        ∏ s ∈ ({a} : Finset M.indnumb).filter (fun s => c ≤ s), M.Dideal s γ := by
  classical
  by_cases hp : c ≤ a
  · rw [Finset.filter_insert, if_pos hp,
      Finset.prod_insert (fun hc => ha (Finset.mem_filter.mp hc).1),
      Finset.filter_singleton, if_pos hp, Finset.prod_singleton, mul_comm]
  · rw [Finset.filter_insert, if_neg hp, Finset.filter_singleton, if_neg hp,
      Finset.prod_empty, mul_one]

noncomputable def keyDrep {ι : Type} (key : ι → M.indnumb)
    (K : Finset M.indnumb) : PreClosF X ι :=
  ⟨{ indnumb := ι
     subscheme := fun k => (M.defDChartDatum K (key k)).glued
     over := fun k => ⟨(M.defDChartDatum K (key k)).structureMap⟩
     cov := M.cov
     ideal := fun k γ => ∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ
     condiso := fun k γ => asIso ((M.defDChartDatum K (key k)).chartCompare γ)
     condover := fun k γ => by
       rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
       show (M.defDChartDatum K (key k)).chartCompare γ ≫
           pullback.snd ((M.defDChartDatum K (key k)).structureMap) (M.cov.map γ) =
         Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
           (∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ)))
       exact (M.defDChartDatum K (key k)).chartCompare_snd γ }, rfl⟩

noncomputable def keyDfam {ι : Type} (key : ι → M.indnumb)
    (K : Finset M.indnumb) : ClosF X ι :=
  Quotient.mk'' (M.keyDrep key K)

theorem keyDrep_ideal_empty {ι : Type} (key : ι → M.indnumb) (k : ι)
    (γ : M.cov.J) : (M.keyDrep key ∅).1.ideal k γ = ⊤ := by
  show ∏ s ∈ (∅ : Finset M.indnumb).filter (fun s => key k ≤ s),
    M.Dideal s γ = ⊤
  rw [Finset.filter_empty, Finset.prod_empty, Ideal.one_eq_top]

set_option maxHeartbeats 400000 in
theorem keyDrep_ideal_insert {ι : Type} (key : ι → M.indnumb)
    (K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K) (k : ι)
    (γ : M.cov.J) :
    (M.keyDrep key (insert a K)).1.ideal k γ =
      (PreClosF.sum (M.keyDrep key K) (M.keyDrep key {a})).1.reindexIdeal
        M.cov k γ := by
  classical
  have hsum : (PreClosF.sum (M.keyDrep key K) (M.keyDrep key {a})).1.reindexIdeal
      M.cov k γ =
      (PreClosF.sum (M.keyDrep key K) (M.keyDrep key {a})).1.ideal k γ :=
    PreClos.reindexIdeal_self (PreClosF.sum (M.keyDrep key K) (M.keyDrep key {a})).1 k γ
  have hin : (M.keyDrep key {a}).1.reindexIdeal M.cov k γ =
      (M.keyDrep key {a}).1.ideal k γ :=
    PreClos.reindexIdeal_self (M.keyDrep key {a}).1 k γ
  rw [hsum]
  show ∏ s ∈ (insert a K).filter (fun s => key k ≤ s), M.Dideal s γ =
    (∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ) *
      (M.keyDrep key {a}).1.reindexIdeal M.cov k γ
  rw [hin]
  show ∏ s ∈ (insert a K).filter (fun s => key k ≤ s), M.Dideal s γ =
    (∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ) *
      ∏ s ∈ ({a} : Finset M.indnumb).filter (fun s => key k ≤ s), M.Dideal s γ
  exact M.Dprod_insert K a ha (key k) γ

set_option maxHeartbeats 400000 in
theorem keyDfam_insert {ι : Type} (key : ι → M.indnumb)
    (K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K) :
    M.keyDfam key (insert a K) =
      (M.keyDfam key K).sum (M.keyDfam key {a}) :=
  closF_eq_of_ideal_eq (M.keyDrep key (insert a K))
    (PreClosF.sum (M.keyDrep key K) (M.keyDrep key {a}))
    (fun k γ => M.keyDrep_ideal_insert key K a ha k γ)

theorem keyDfam_empty {ι : Type} (key : ι → M.indnumb) :
    M.keyDfam key ∅ = 0 :=
  closF_eq_of_ideal_eq (M.keyDrep key ∅)
    ⟨PreClos.zero ι (Scheme.affineOpenCover X), rfl⟩
    (fun k γ => (M.keyDrep_ideal_empty key k γ).trans
      (PreClos.zero_reindexIdeal ι (Scheme.affineOpenCover X) M.cov _ γ).symm)

theorem keyDfam_eq_sum {ι : Type} (key : ι → M.indnumb)
    (K : Finset M.indnumb) :
    M.keyDfam key K = ∑ k ∈ K, M.keyDfam key {k} := by
  induction K using Finset.induction_on with
  | empty => rw [M.keyDfam_empty key, Finset.sum_empty]
  | insert a K ha ih =>
    rw [M.keyDfam_insert key K a ha, Finset.sum_insert ha, ← ih,
      ← ClosF.add_eq_sum, add_comm]

theorem defDfam_eq_keyDfam (J K : Finset M.indnumb) :
    M.defDfam J K =
      M.keyDfam (Subtype.val : {j // j ∈ J} → M.indnumb) K := rfl

theorem panelBase_Dfam (J : Finset M.indnumb) (i : M.indnumb) :
    (M.panelBase J i).Dfam = M.keyDfam (M.panelKey J i) J := rfl

variable [Fintype M.indnumb]

def stageDChartDatum (J K : Finset M.indnumb) (i : M.indnumb) :
    ChartDatum (M.defSpace J).dilatation where
  cov := (M.defSpace J).dilatationCover
  idl γ := Ideal.map (algebraMap ((M.defSpace J).cov.obj γ)
      (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ)))
      (∏ s ∈ K.filter (fun s => i ≤ s), M.Dideal s γ)
  compat {W} _ {γ γ'} a b hab := by
    classical
    have hab' : (a ≫ (M.defSpace J).chartHom γ) ≫ M.cov.map γ =
        (b ≫ (M.defSpace J).chartHom γ') ≫ M.cov.map γ' := by
      simp only [Category.assoc]
      show a ≫ (M.defSpace J).chartToX γ = b ≫ (M.defSpace J).chartToX γ'
      rw [← (M.defSpace J).structureMap_chart γ,
        ← (M.defSpace J).structureMap_chart γ', ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ (M.defSpace J).structureMap) hab
    have hpa : Spec.preimage (W.isoSpec.inv ≫ a ≫ (M.defSpace J).chartHom γ) =
        CommRingCat.ofHom (algebraMap ((M.defSpace J).cov.obj γ)
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ))) ≫
          Spec.preimage (W.isoSpec.inv ≫ a) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ a ≫ (M.defSpace J).chartHom γ =
        (W.isoSpec.inv ≫ a) ≫ (M.defSpace J).chartHom γ
      rw [Category.assoc]
    have hpb : Spec.preimage (W.isoSpec.inv ≫ b ≫ (M.defSpace J).chartHom γ') =
        CommRingCat.ofHom (algebraMap ((M.defSpace J).cov.obj γ')
          (Multicenter.Dilatation ((M.defSpace J).localMulticenter γ'))) ≫
          Spec.preimage (W.isoSpec.inv ≫ b) := by
      apply Spec.map_injective
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
      show W.isoSpec.inv ≫ b ≫ (M.defSpace J).chartHom γ' =
        (W.isoSpec.inv ≫ b) ≫ (M.defSpace J).chartHom γ'
      rw [Category.assoc]
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_finset_prod, Ideal.map_finset_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h := chartIdeal_agree M.Drep (a ≫ (M.defSpace J).chartHom γ)
      (b ≫ (M.defSpace J).chartHom γ') hab' s
    rw [hpa, hpb, CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    exact h


theorem panelDChartDatum_eq (J : Finset M.indnumb) (i : M.indnumb) :
    M.panelDChartDatum J i =
      M.stageDChartDatum J (Polyptych.Comp J) i := rfl

noncomputable def stageDrep (J K : Finset M.indnumb) {ι : Type}
    (key : ι → M.indnumb) : PreClosF (M.defSpace J).dilatation ι :=
  ⟨{ indnumb := ι
     subscheme := fun k => (M.stageDChartDatum J K (key k)).glued
     over := fun k => ⟨(M.stageDChartDatum J K (key k)).structureMap⟩
     cov := (M.defSpace J).dilatationCover
     ideal := fun k γ => (M.stageDChartDatum J K (key k)).idl γ
     condiso := fun k γ => asIso ((M.stageDChartDatum J K (key k)).chartCompare γ)
     condover := fun k γ => by
       rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
       show (M.stageDChartDatum J K (key k)).chartCompare γ ≫
           pullback.snd ((M.stageDChartDatum J K (key k)).structureMap)
             ((M.defSpace J).dilatationCover.map γ) =
         Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
           ((M.stageDChartDatum J K (key k)).idl γ)))
       exact (M.stageDChartDatum J K (key k)).chartCompare_snd γ }, rfl⟩

noncomputable def stageDfam (J K : Finset M.indnumb) {ι : Type}
    (key : ι → M.indnumb) : ClosF (M.defSpace J).dilatation ι :=
  Quotient.mk'' (M.stageDrep J K key)

theorem stageDrep_ideal_empty (J : Finset M.indnumb) {ι : Type}
    (key : ι → M.indnumb) (k : ι) (γ : (M.defSpace J).dilatationCover.J) :
    (M.stageDrep J ∅ key).1.ideal k γ = ⊤ := by
  show Ideal.map _ (∏ s ∈ (∅ : Finset M.indnumb).filter
    (fun s => key k ≤ s), M.Dideal s γ) = ⊤
  rw [Finset.filter_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.map_top]

set_option maxHeartbeats 800000 in
theorem stageDrep_ideal_insert (J K : Finset M.indnumb) (a : M.indnumb)
    (ha : a ∉ K) {ι : Type} (key : ι → M.indnumb) (k : ι)
    (γ : (M.defSpace J).dilatationCover.J) :
    (M.stageDrep J (insert a K) key).1.ideal k γ =
      (PreClosF.sum (M.stageDrep J K key) (M.stageDrep J {a} key)).1.reindexIdeal
        (M.defSpace J).dilatationCover k γ := by
  classical
  have hsum : (PreClosF.sum (M.stageDrep J K key) (M.stageDrep J {a} key)).1.reindexIdeal
      (M.defSpace J).dilatationCover k γ =
      (PreClosF.sum (M.stageDrep J K key) (M.stageDrep J {a} key)).1.ideal k γ :=
    PreClos.reindexIdeal_self
      (PreClosF.sum (M.stageDrep J K key) (M.stageDrep J {a} key)).1 k γ
  have hin : (M.stageDrep J {a} key).1.reindexIdeal
      (M.stageDrep J K key).1.cov k γ =
      (M.stageDrep J {a} key).1.ideal k γ :=
    PreClos.reindexIdeal_self (M.stageDrep J {a} key).1 k γ
  rw [hsum]
  show Ideal.map _ (∏ s ∈ (insert a K).filter (fun s => key k ≤ s), M.Dideal s γ) =
    Ideal.map _ (∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ) *
      (M.stageDrep J {a} key).1.reindexIdeal (M.stageDrep J K key).1.cov k γ
  rw [hin]
  show Ideal.map _ (∏ s ∈ (insert a K).filter (fun s => key k ≤ s), M.Dideal s γ) =
    Ideal.map _ (∏ s ∈ K.filter (fun s => key k ≤ s), M.Dideal s γ) *
      Ideal.map _ (∏ s ∈ ({a} : Finset M.indnumb).filter
        (fun s => key k ≤ s), M.Dideal s γ)
  rw [← Ideal.map_mul, M.Dprod_insert K a ha (key k) γ]

set_option maxHeartbeats 800000 in
theorem stageDfam_insert (J K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K)
    {ι : Type} (key : ι → M.indnumb) :
    M.stageDfam J (insert a K) key =
      (M.stageDfam J K key).sum (M.stageDfam J {a} key) :=
  closF_eq_of_ideal_eq (M.stageDrep J (insert a K) key)
    (PreClosF.sum (M.stageDrep J K key) (M.stageDrep J {a} key))
    (fun k γ => M.stageDrep_ideal_insert J K a ha key k γ)

theorem stageDfam_empty (J : Finset M.indnumb) {ι : Type}
    (key : ι → M.indnumb) : M.stageDfam J ∅ key = 0 :=
  closF_eq_of_ideal_eq (M.stageDrep J ∅ key)
    ⟨PreClos.zero ι (Scheme.affineOpenCover (M.defSpace J).dilatation), rfl⟩
    (fun k γ => (M.stageDrep_ideal_empty J key k γ).trans
      (PreClos.zero_reindexIdeal ι
        (Scheme.affineOpenCover (M.defSpace J).dilatation)
        (M.defSpace J).dilatationCover _ γ).symm)

theorem stageDfam_eq_sum (J K : Finset M.indnumb) {ι : Type}
    (key : ι → M.indnumb) :
    M.stageDfam J K key = ∑ k ∈ K, M.stageDfam J {k} key := by
  induction K using Finset.induction_on with
  | empty => rw [M.stageDfam_empty J key, Finset.sum_empty]
  | insert a K ha ih =>
    rw [M.stageDfam_insert J K a ha key, Finset.sum_insert ha, ← ih,
      ← ClosF.add_eq_sum, add_comm]

theorem panelStage_Dfam (J : Finset M.indnumb) :
    (M.panelStage J).Dfam =
      M.stageDfam J (Polyptych.Comp J) (Subtype.val) := rfl

end PreMultiCenter
end SchemeDilatation
