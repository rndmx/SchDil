import PolyptychSchemeDatum
import ClosSumSche
import PreClosReindex

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

theorem closF_eq_of_ideal_eq {ι : Type} (Z₁ Z₂ : PreClosF X ι)
    (h : ∀ (i : Z₁.1.indnumb) (γ : Z₁.1.cov.J),
      Z₁.1.ideal i γ =
        Z₂.1.reindexIdeal Z₁.1.cov (Equiv.cast (Z₁.2.trans Z₂.2.symm) i) γ) :
    (Quotient.mk'' Z₁ : ClosF X ι) = Quotient.mk'' Z₂ :=
  Quotient.sound ⟨⟨PreClos.relStructure_of_ideal_eq Z₁.1 Z₂.1
    (Equiv.cast (Z₁.2.trans Z₂.2.symm)) h, fun _ => rfl⟩⟩

namespace PreMultiCenter

variable (M : PreMultiCenter X)

def Yfam : ClosF X M.indnumb := Quotient.mk'' ⟨M.Yrep, rfl⟩

def Dfam : ClosF X M.indnumb := Quotient.mk'' ⟨M.Drep, rfl⟩

variable [LinearOrder M.indnumb]

noncomputable def defDrep (J K : Finset M.indnumb) : PreClosF X {j // j ∈ J} :=
  ⟨{ indnumb := {j // j ∈ J}
     subscheme := fun j => (M.defDChartDatum K j.1).glued
     over := fun j => ⟨(M.defDChartDatum K j.1).structureMap⟩
     cov := M.cov
     ideal := fun j γ => ∏ s ∈ K.filter (fun s => j.1 ≤ s), M.Dideal s γ
     condiso := fun j γ => asIso ((M.defDChartDatum K j.1).chartCompare γ)
     condover := fun j γ => by
       rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
       show (M.defDChartDatum K j.1).chartCompare γ ≫
           pullback.snd ((M.defDChartDatum K j.1).structureMap) (M.cov.map γ) =
         Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
           (∏ s ∈ K.filter (fun s => j.1 ≤ s), M.Dideal s γ)))
       exact (M.defDChartDatum K j.1).chartCompare_snd γ }, rfl⟩

noncomputable def defDfam (J K : Finset M.indnumb) : ClosF X {j // j ∈ J} :=
  Quotient.mk'' (M.defDrep J K)

theorem defSpace_Dfam (J : Finset M.indnumb) :
    (M.defSpace J).Dfam = M.defDfam J J := rfl

theorem defDrep_ideal_empty (J : Finset M.indnumb) (j : {j // j ∈ J}) (γ : M.cov.J) :
    (M.defDrep J ∅).1.ideal j γ = ⊤ := by
  show ∏ s ∈ (∅ : Finset M.indnumb).filter (fun s => j.1 ≤ s), M.Dideal s γ = ⊤
  rw [Finset.filter_empty, Finset.prod_empty, Ideal.one_eq_top]

set_option maxHeartbeats 400000 in
theorem defDrep_ideal_insert (J K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K)
    (j : {j // j ∈ J}) (γ : M.cov.J) :
    (M.defDrep J (insert a K)).1.ideal j γ =
      (PreClosF.sum (M.defDrep J K) (M.defDrep J {a})).1.reindexIdeal M.cov j γ := by
  classical
  have hsum : (PreClosF.sum (M.defDrep J K) (M.defDrep J {a})).1.reindexIdeal M.cov j γ =
      (PreClosF.sum (M.defDrep J K) (M.defDrep J {a})).1.ideal j γ :=
    PreClos.reindexIdeal_self (PreClosF.sum (M.defDrep J K) (M.defDrep J {a})).1 j γ
  have hin : (M.defDrep J {a}).1.reindexIdeal M.cov j γ =
      (M.defDrep J {a}).1.ideal j γ :=
    PreClos.reindexIdeal_self (M.defDrep J {a}).1 j γ
  rw [hsum]
  show ∏ s ∈ (insert a K).filter (fun s => j.1 ≤ s), M.Dideal s γ =
    (∏ s ∈ K.filter (fun s => j.1 ≤ s), M.Dideal s γ) *
      (M.defDrep J {a}).1.reindexIdeal M.cov j γ
  rw [hin]
  show ∏ s ∈ (insert a K).filter (fun s => j.1 ≤ s), M.Dideal s γ =
    (∏ s ∈ K.filter (fun s => j.1 ≤ s), M.Dideal s γ) *
      ∏ s ∈ ({a} : Finset M.indnumb).filter (fun s => j.1 ≤ s), M.Dideal s γ
  by_cases hp : j.1 ≤ a
  · rw [Finset.filter_insert, if_pos hp,
      Finset.prod_insert (fun hc => ha (Finset.mem_filter.mp hc).1),
      Finset.filter_singleton, if_pos hp, Finset.prod_singleton, mul_comm]
  · rw [Finset.filter_insert, if_neg hp, Finset.filter_singleton, if_neg hp,
      Finset.prod_empty, mul_one]

set_option maxHeartbeats 400000 in
theorem defDfam_insert (J K : Finset M.indnumb) (a : M.indnumb) (ha : a ∉ K) :
    M.defDfam J (insert a K) = (M.defDfam J K).sum (M.defDfam J {a}) :=
  closF_eq_of_ideal_eq (M.defDrep J (insert a K))
    (PreClosF.sum (M.defDrep J K) (M.defDrep J {a}))
    (fun j γ => M.defDrep_ideal_insert J K a ha j γ)

theorem defDfam_empty (J : Finset M.indnumb) :
    M.defDfam J ∅ = 0 :=
  closF_eq_of_ideal_eq (M.defDrep J ∅)
    ⟨PreClos.zero {j // j ∈ J} (Scheme.affineOpenCover X), rfl⟩
    (fun j γ => (M.defDrep_ideal_empty J j γ).trans
      (PreClos.zero_reindexIdeal {j // j ∈ J} (Scheme.affineOpenCover X)
        M.cov _ γ).symm)

theorem defDfam_eq_sum (J K : Finset M.indnumb) :
    M.defDfam J K = ∑ k ∈ K, M.defDfam J {k} := by
  induction K using Finset.induction_on with
  | empty => rw [M.defDfam_empty J, Finset.sum_empty]
  | insert a K ha ih =>
    rw [M.defDfam_insert J K a ha, Finset.sum_insert ha, ← ih,
      ← ClosF.add_eq_sum, add_comm]

end PreMultiCenter

end SchemeDilatation
