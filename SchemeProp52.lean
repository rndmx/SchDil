import SchemeFact51
import MulticenterShift

suppress_compilation
universe u
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

section SingleDivisor

variable {X : Scheme.{u+1}} (M : PreMultiCenter X) (i₀ : M.indnumb)

def withDivisor : PreMultiCenter X where
  indnumb := M.indnumb
  cov := M.cov
  Ysub := M.Ysub
  Dsub _ := M.Dsub i₀
  Yover := M.Yover
  Dover _ := M.Dover i₀
  Yideal := M.Yideal
  Dideal _ := M.Dideal i₀
  YcondIso := M.YcondIso
  YcondOver := M.YcondOver
  DcondIso _ := M.DcondIso i₀
  DcondOver _ := M.DcondOver i₀
  Dprin _ := M.Dprin i₀

@[simp] theorem withDivisor_cov : (M.withDivisor i₀).cov = M.cov := rfl

@[simp] theorem withDivisor_Yideal (i : M.indnumb) (γ : M.cov.J) :
    (M.withDivisor i₀).Yideal i γ = M.Yideal i γ := rfl

@[simp] theorem withDivisor_Dideal (i : M.indnumb) (γ : M.cov.J) :
    (M.withDivisor i₀).Dideal i γ = M.Dideal i₀ γ := rfl

@[simp] theorem withDivisor_Ysub (i : M.indnumb) :
    (M.withDivisor i₀).Ysub i = M.Ysub i := rfl

theorem withDivisor_localElem (i j : M.indnumb) (γ : M.cov.J) :
    ((M.withDivisor i₀).localMulticenter γ).elem i =
      ((M.withDivisor i₀).localMulticenter γ).elem j := rfl

abbrev localDivElem (γ : M.cov.J) : (M.cov.obj γ) :=
  ((M.withDivisor i₀).localMulticenter γ).elem i₀

@[simp] theorem withDivisor_localElem_eq (i : M.indnumb) (γ : M.cov.J) :
    ((M.withDivisor i₀).localMulticenter γ).elem i = M.localDivElem i₀ γ := rfl

def ConstDivisor : Prop :=
  ∀ (γ : M.cov.J) (i : M.indnumb),
    (M.localMulticenter γ).elem i = (M.localMulticenter γ).elem i₀

theorem withDivisor_constDivisor :
    (M.withDivisor i₀).ConstDivisor i₀ := fun _ _ => rfl

theorem withDivisor_multiple_span (s : M.indnumb → ℕ) (i : M.indnumb)
    (γ : M.cov.J) :
    Ideal.span {(((M.withDivisor i₀).multiple s).localMulticenter γ).elem i} =
      Ideal.span {(M.localDivElem i₀ γ) ^ (s i)} := by
  rw [(M.withDivisor i₀).multiple_localGen_span' γ s i,
    (M.withDivisor i₀).local_Dideal_span' γ i, ← Ideal.span_singleton_pow]
  rfl

end SingleDivisor

section Stage2

variable {X : Scheme.{u+1}} (N : PreMultiCenter X) (i₀ : N.indnumb)
  (s : N.indnumb → ℕ) (t : ℕ)

def stage2 (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀) :
    PreMultiCenter (N.multiple s).dilatation where
  indnumb := PUnit
  cov := (N.multiple s).dilatationCover
  Ysub _ := N.Ysub i₀
  Dsub _ := (N.transformDChartDatum s (fun _ => t) i₀).glued
  Yover _ := ⟨N.Y0lift i₀ s hY hb⟩
  Dover _ := ⟨(N.transformDChartDatum s (fun _ => t) i₀).structureMap⟩
  Yideal _ γ :=
    presentIdeal (N.Y0lift i₀ s hY hb) ((N.multiple s).dilatationCover) γ
  Dideal _ γ := (Ideal.map (algebraMap ((N.multiple s).cov.obj γ)
    (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)))
      (N.Dideal i₀ γ)) ^ t
  YcondIso _ γ :=
    (presentIso (N.Y0lift i₀ s hY hb)
      ((N.multiple s).dilatationCover) γ).symm
  YcondOver _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (presentIso (N.Y0lift i₀ s hY hb)
        ((N.multiple s).dilatationCover) γ).inv ≫
        pullback.snd (N.Y0lift i₀ s hY hb)
          ((N.multiple s).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (presentIdeal (N.Y0lift i₀ s hY hb)
          ((N.multiple s).dilatationCover) γ)))
    rw [presentIso_eq (N.Y0lift i₀ s hY hb) ((N.multiple s).dilatationCover) γ,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  DcondIso _ γ :=
    asIso ((N.transformDChartDatum s (fun _ => t) i₀).chartCompare γ)
  DcondOver _ γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right,
      spec_quotient_ideal_over_eq]
    show (N.transformDChartDatum s (fun _ => t) i₀).chartCompare γ ≫
        pullback.snd ((N.transformDChartDatum s (fun _ => t) i₀).structureMap)
          ((N.multiple s).dilatationCover.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.map (algebraMap ((N.multiple s).cov.obj γ)
          (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)))
            (N.Dideal i₀ γ)) ^ t)))
    exact (N.transformDChartDatum s (fun _ => t) i₀).chartCompare_snd γ
  Dprin _ γ := by
    letI : Submodule.IsPrincipal (N.Dideal i₀ γ) := N.Dprin i₀ γ
    refine ⟨⟨(algebraMap ((N.multiple s).cov.obj γ)
      (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)))
        ((N.localMulticenter γ).elem i₀) ^ t, ?_⟩⟩
    rw [Ideal.submodule_span_eq, ← Ideal.span_singleton_pow]
    congr 1
    conv_lhs => rw [show N.Dideal i₀ γ =
      Ideal.span {(N.localMulticenter γ).elem i₀} from N.local_Dideal_span' γ i₀]
    rw [Ideal.map_span, Set.image_singleton]
    rfl

@[simp] theorem stage2_Yideal (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀)
    (u : PUnit) (γ : N.cov.J) :
    (N.stage2 i₀ s t hY hb).Yideal u γ =
      presentIdeal (N.Y0lift i₀ s hY hb) ((N.multiple s).dilatationCover) γ := rfl

@[simp] theorem stage2_Dideal (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀)
    (u : PUnit) (γ : N.cov.J) :
    (N.stage2 i₀ s t hY hb).Dideal u γ =
      (Ideal.map (algebraMap ((N.multiple s).cov.obj γ)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)))
          (N.Dideal i₀ γ)) ^ t := rfl

theorem stage2_Yideal_eq_genFrac (hY : N.CentersOver i₀)
    (hb : N.CarsOnCenter i₀) (hSt : N.ElemNzdOnCenter i₀) (u : PUnit)
    (γ : N.cov.J) :
    (N.stage2 i₀ s t hY hb).Yideal u γ =
      ((N.multiple s).localMulticenter γ).genFracIdeal :=
  N.presentIdeal_Y0lift i₀ s hY hb hSt γ

end Stage2

section ForwardChart

variable {X : Scheme.{u+1}} (N : PreMultiCenter X) (i₀ : N.indnumb)
  (s : N.indnumb → ℕ) (t : ℕ)

abbrev bump : N.indnumb → ℕ := fun j => s j + t

theorem le_bump : ∀ i, s i ≤ N.bump s t i := fun i => Nat.le_add_right _ _

theorem multiRho_genFrac_le (γ : N.cov.J)
    (hconst : ∀ i, (N.localMulticenter γ).elem i =
      (N.localMulticenter γ).elem i₀) :
    Ideal.map (N.multiRho (N.bump s t) s (N.le_bump s t) γ).toRingHom
        (((N.multiple s).localMulticenter γ).genFracIdeal) ≤
      Ideal.span {(algebraMap ((N.multiple (N.bump s t)).cov.obj γ)
        (Multicenter.Dilatation
          ((N.multiple (N.bump s t)).localMulticenter γ)))
          ((N.localMulticenter γ).elem i₀) ^ t} := by
  set f : (N.cov.obj γ) →+*
      (Multicenter.Dilatation ((N.multiple (N.bump s t)).localMulticenter γ)) :=
    (algebraMap ((N.multiple (N.bump s t)).cov.obj γ)
      (Multicenter.Dilatation
        ((N.multiple (N.bump s t)).localMulticenter γ)) : _ →+* _) with hf
  rw [Ideal.map_le_iff_le_comap]
  refine ((N.multiple s).localMulticenter γ).genFracIdeal_le (fun i m hm => ?_)
  rw [Ideal.mem_comap]
  show (N.multiRho (N.bump s t) s (N.le_bump s t) γ)
      (Dilatation.frac (F := (N.multiple s).localMulticenter γ)
        (Finsupp.single i 1)
        ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩) ∈
    Ideal.span {f ((N.localMulticenter γ).elem i₀) ^ t}
  have hspec : f (((N.multiple s).localMulticenter γ).elem i) *
      (N.multiRho (N.bump s t) s (N.le_bump s t) γ)
        (Dilatation.frac (F := (N.multiple s).localMulticenter γ)
          (Finsupp.single i 1)
          ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩) =
      f m := by
    have h := dsc_spec ((N.multiple s).localMulticenter γ)
      (Finsupp.single i 1)
      ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩
      (N.multiRho_nzd (N.bump s t) s (N.le_bump s t) γ)
      (N.multiRho_gen (N.bump s t) s (N.le_bump s t) γ)
    rw [familyPow_single] at h
    exact h
  have hm2 : f m ∈
      Ideal.span {f ((N.localMulticenter γ).elem i) ^ (N.bump s t i)} :=
    N.chart_M_le_alpha_pow' γ (N.bump s t) i (Ideal.mem_map_of_mem _ hm)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hm2
  obtain ⟨v, hv⟩ := N.hom_multipleGen_mem_at' γ s i f
  have hnzd : f (((N.multiple s).localMulticenter γ).elem i) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((N.multiple (N.bump s t)).localMulticenter γ)) :=
    N.chart_gen_nzd' γ (N.bump s t) s i (N.le_bump s t i)
  have hcalc : f (((N.multiple s).localMulticenter γ).elem i) *
      ((N.multiRho (N.bump s t) s (N.le_bump s t) γ)
        (Dilatation.frac (F := (N.multiple s).localMulticenter γ)
          (Finsupp.single i 1)
          ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩) -
        z * v * f ((N.localMulticenter γ).elem i) ^ t) = 0 := by
    rw [mul_sub, hspec, ← hz, show N.bump s t i = s i + t from rfl, pow_add, ← hv]
    ring
  have hxeq := sub_eq_zero.mp
    ((mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd).mp hcalc)
  rw [hxeq, hconst i]
  exact Ideal.mem_span_singleton'.mpr ⟨z * v, rfl⟩

end ForwardChart

section ForwardStage2

variable {X : Scheme.{u+1}} (N : PreMultiCenter X) (i₀ : N.indnumb)
  (s : N.indnumb → ℕ) (t : ℕ)
  (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀) (hSt : N.ElemNzdOnCenter i₀)

theorem stage2_piece_factor
    (γβ : (pull_cov (N.multiple s).dilatation
      (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t))).J) :
    ∃ ψ : CommRingCat.of
        (Multicenter.Dilatation ((N.multiple (N.bump s t)).localMulticenter γβ.1)) ⟶
        (pull_loc_cov (N.multiple s).dilatation
          (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
          (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).obj γβ.2,
      pull_mor_ring (N.multiple s).dilatation
          (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
          (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ =
        CommRingCat.ofHom
          (N.multiRho (N.bump s t) s (N.le_bump s t) γβ.1).toRingHom ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov (N.multiple s).dilatation
      (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).map γβ.2 ≫
      pullback.snd (N.multipleHom (N.bump s t) s (N.le_bump s t))
        ((N.stage2 i₀ s t hY hb).Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcφ : ((pull_loc_cov (N.multiple s).dilatation
      (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).map γβ.2 ≫
      pullback.fst (N.multipleHom (N.bump s t) s (N.le_bump s t))
        ((N.stage2 i₀ s t hY hb).Drep.cov.map γβ.1)) ≫
      N.multipleHom (N.bump s t) s (N.le_bump s t) =
      Spec.map (pull_mor_ring (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ) ≫
      (N.multiple s).chartTo γβ.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd]
    rfl
  have hcw : ((pull_loc_cov (N.multiple s).dilatation
      (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).map γβ.2 ≫
      pullback.fst (N.multipleHom (N.bump s t) s (N.le_bump s t))
        ((N.stage2 i₀ s t hY hb).Drep.cov.map γβ.1)) ≫
      (N.multiple (N.bump s t)).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ((N.multiple s).cov.obj γβ.1)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γβ.1))) ≫
        pull_mor_ring (N.multiple s).dilatation
          (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
          (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ) ≫
      N.cov.map γβ.1 := by
    rw [← N.multipleHom_over (N.bump s t) s (N.le_bump s t), ← Category.assoc,
      hcφ, Spec.map_comp]
    rw [Category.assoc, Category.assoc, (N.multiple s).structureMap_chart γβ.1]
    rfl
  obtain ⟨sT, hsT1, hsT2⟩ := (N.multiple (N.bump s t)).exists_chart_factorisation' γβ.1
    _ _ hcw
  haveI : IsOpenImmersion ((N.multiple s).chartTo γβ.1) :=
    (N.multiple s).chartTo_isOpenImmersion γβ.1
  haveI : Mono ((N.multiple s).chartTo γβ.1) := inferInstance
  have hkey : Spec.map (pull_mor_ring (N.multiple s).dilatation
      (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ) =
      sT ≫ N.multiRhoSch (N.bump s t) s (N.le_bump s t) γβ.1 := by
    apply Mono.right_cancellation (f := (N.multiple s).chartTo γβ.1)
    rw [← hcφ]
    simp only [Category.assoc]
    rw [← N.multi_chart_cone (N.bump s t) s (N.le_bump s t) γβ.1,
      reassoc_of% hsT1]
  refine ⟨Spec.preimage sT, ?_, ?_⟩
  · apply Spec.map_injective
    rw [hkey, Spec.map_comp, Spec.map_preimage]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).map γβ.2 ≫
        pullback.fst (N.multipleHom (N.bump s t) s (N.le_bump s t))
          ((N.stage2 i₀ s t hY hb).Drep.cov.map γβ.1)) :=
      (pull_cov (N.multiple s).dilatation (N.stage2 i₀ s t hY hb).Drep
        (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t))).map_prop γβ
    haveI hsc : IsOpenImmersion (sT ≫ (N.multiple (N.bump s t)).chartTo γβ.1) := by
      rw [hsT1]
      exact hc
    haveI hs : IsOpenImmersion sT :=
      IsOpenImmersion.of_comp sT ((N.multiple (N.bump s t)).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sT := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sT)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

theorem stage2_Dideal_map (u : PUnit) (γ : N.cov.J) :
    Ideal.map (N.multiRho (N.bump s t) s (N.le_bump s t) γ).toRingHom
        ((N.stage2 i₀ s t hY hb).Dideal u γ) =
      Ideal.span {(algebraMap ((N.multiple (N.bump s t)).cov.obj γ)
        (Multicenter.Dilatation
          ((N.multiple (N.bump s t)).localMulticenter γ)))
          ((N.localMulticenter γ).elem i₀) ^ t} := by
  rw [stage2_Dideal, Ideal.map_pow, Ideal.map_map,
    show ((N.multiRho (N.bump s t) s (N.le_bump s t) γ).toRingHom).comp
        (algebraMap ((N.multiple s).cov.obj γ)
          (Multicenter.Dilatation ((N.multiple s).localMulticenter γ))) =
      (algebraMap ((N.multiple (N.bump s t)).cov.obj γ)
        (Multicenter.Dilatation
          ((N.multiple (N.bump s t)).localMulticenter γ)) : _ →+* _) from
      RingHom.ext fun a => N.multiRho_algebraMap (N.bump s t) s (N.le_bump s t) γ a,
    N.local_Dideal_span' γ i₀, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow]
  rfl

include hSt in
theorem stage2_pullSubset_chart (hconst : N.ConstDivisor i₀) (u : PUnit)
    (γβ : (pull_cov (N.multiple s).dilatation (N.stage2 i₀ s t hY hb).Drep
      (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t))).J) :
    Ideal.map (pull_mor_ring (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ).hom
        ((N.stage2 i₀ s t hY hb).Yideal u γβ.1) ≤
      Ideal.map (pull_mor_ring (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ).hom
        ((N.stage2 i₀ s t hY hb).Dideal u γβ.1) := by
  obtain ⟨ψ, hψ, -⟩ := N.stage2_piece_factor i₀ s t hY hb γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (Multicenter.Dilatation
      ((N.multiple s).localMulticenter γβ.1))),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        (N.multiRho (N.bump s t) s (N.le_bump s t) γβ.1).toRingHom) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map (N.multiRho (N.bump s t) s (N.le_bump s t) γβ.1).toRingHom I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  rw [N.stage2_Yideal_eq_genFrac i₀ s t hY hb hSt u γβ.1,
    N.stage2_Dideal_map i₀ s t hY hb u γβ.1]
  exact N.multiRho_genFrac_le i₀ s t γβ.1 (hconst γβ.1)

include hSt in
theorem stage2_pullSubset (hconst : N.ConstDivisor i₀) :
    (N.stage2 i₀ s t hY hb).pullSubset
      (N.multipleHom (N.bump s t) s (N.le_bump s t)) :=
  ((N.stage2 i₀ s t hY hb).pullSubset_iff _).mpr
    (fun u γβ => N.stage2_pullSubset_chart i₀ s t hY hb hSt hconst u γβ)

theorem stage2_isCars_chart (u : PUnit)
    (γβ : (pull_cov (N.multiple s).dilatation (N.stage2 i₀ s t hY hb).Drep
      (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t))).J) :
    ∃ g : (pull_loc_cov (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).obj γβ.2,
      (pullback_PreClos (N.multiple s).dilatation
          (N.multiple (N.bump s t)).dilatation
          (N.multipleHom (N.bump s t) s (N.le_bump s t))
          (N.stage2 i₀ s t hY hb).Drep).ideal u γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := N.stage2_piece_factor i₀ s t hY hb γβ
  refine ⟨ψ.hom ((algebraMap ((N.multiple (N.bump s t)).cov.obj γβ.1)
    (Multicenter.Dilatation
      ((N.multiple (N.bump s t)).localMulticenter γβ.1)))
      ((N.localMulticenter γβ.1).elem i₀)) ^ t, ?_, ?_⟩
  · show Ideal.map (pull_mor_ring (N.multiple s).dilatation
        (N.stage2 i₀ s t hY hb).Drep (N.multiple (N.bump s t)).dilatation
        (N.multipleHom (N.bump s t) s (N.le_bump s t)) γβ).hom
        ((N.stage2 i₀ s t hY hb).Dideal u γβ.1) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom, ← Ideal.map_map,
      N.stage2_Dideal_map i₀ s t hY hb u γβ.1, Ideal.map_span,
      Set.image_singleton, map_pow]
  · rw [← map_pow]
    exact hflat.preserves_nonzeroDivisors
      (N.chart_alpha_pow_nzd' γβ.1 (N.bump s t) (fun _ => t) i₀
        (Nat.le_add_left t (s i₀)))

theorem stage2_isCars :
    IsCars (N.multiple (N.bump s t)).dilatation
      (Clos.pullback (N.multipleHom (N.bump s t) s (N.le_bump s t))
        (N.stage2 i₀ s t hY hb).D) :=
  ⟨pullback_PreClos (N.multiple s).dilatation
      (N.multiple (N.bump s t)).dilatation
      (N.multipleHom (N.bump s t) s (N.le_bump s t))
      (N.stage2 i₀ s t hY hb).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun u γβ => N.stage2_isCars_chart i₀ s t hY hb u γβ), rfl⟩

include hSt in
theorem existsUnique_stage2Fwd (hconst : N.ConstDivisor i₀) :
    ∃! g : (N.multiple (N.bump s t)).dilatation ⟶
        (N.stage2 i₀ s t hY hb).dilatation,
      g ≫ (N.stage2 i₀ s t hY hb).structureMap =
        N.multipleHom (N.bump s t) s (N.le_bump s t) :=
  (N.stage2 i₀ s t hY hb).universal_property _
    (N.multipleHom (N.bump s t) s (N.le_bump s t))
    (N.stage2_isCars i₀ s t hY hb)
    (N.stage2_pullSubset i₀ s t hY hb hSt hconst)

end ForwardStage2

section BackwardChart

variable {X : Scheme.{u+1}} (N : PreMultiCenter X) (i₀ : N.indnumb)
  (s : N.indnumb → ℕ) (t : ℕ)
  (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀) (hSt : N.ElemNzdOnCenter i₀)

theorem stage2_elem_span (γ : N.cov.J) :
    Ideal.span {((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit} =
      Ideal.span {(algebraMap ((N.multiple s).cov.obj γ)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)))
          ((N.localMulticenter γ).elem i₀) ^ t} := by
  letI : Submodule.IsPrincipal ((N.stage2 i₀ s t hY hb).Dideal PUnit.unit γ) :=
    (N.stage2 i₀ s t hY hb).Dprin PUnit.unit γ
  rw [show Ideal.span {((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit} =
      (N.stage2 i₀ s t hY hb).Dideal PUnit.unit γ from
    Ideal.span_singleton_generator _, stage2_Dideal,
    N.local_Dideal_span' γ i₀, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow]
  rfl

include hSt in
theorem stage2Chart_alpha_nzd (hconst : N.ConstDivisor i₀) (i : N.indnumb)
    (γ : N.cov.J) :
    ((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γ)
        (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ))).comp
      (algebraMap ((N.multiple s).cov.obj γ)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γ))))
      ((N.localMulticenter γ).elem i₀) ^ (s i + t) ∈
      nonZeroDivisors (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γ)) := by
  set g2 : (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((N.stage2 i₀ s t hY hb).localMulticenter γ)) :=
    (algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γ)
      (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γ)) : _ →+* _) with hg2
  set f : (N.cov.obj γ) →+*
      (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) :=
    (algebraMap ((N.multiple s).cov.obj γ)
      (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) :
        _ →+* _) with hf
  show (g2.comp f) ((N.localMulticenter γ).elem i₀) ^ (s i + t) ∈ _
  simp only [RingHom.comp_apply]
  rw [pow_add]
  refine mul_mem ?_ ?_
  ·
    have hgen : f (((N.multiple s).localMulticenter γ).elem i) ∈
        nonZeroDivisors (Multicenter.Dilatation
          ((N.multiple s).localMulticenter γ)) :=
      nonzerodiv_image_single ((N.multiple s).localMulticenter γ) i
    have hgen' : g2 (f (((N.multiple s).localMulticenter γ).elem i)) ∈
        nonZeroDivisors (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ)) :=
      Multicenter.Dilatation.nonzerodiv_of_nonzerodiv
        (F := (N.stage2 i₀ s t hY hb).localMulticenter γ) hgen
    obtain ⟨u, hu⟩ := N.hom_multipleGen_mem_at γ s i f
    have h2 : g2 u * (g2 (f ((N.localMulticenter γ).elem i₀))) ^ (s i) ∈
        nonZeroDivisors (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ)) := by
      rw [← map_pow, ← map_mul, ← hconst γ i, hu]
      exact hgen'
    exact (mul_mem_nonZeroDivisors.mp h2).2
  ·
    have hgenH : g2 (((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit) ∈
        nonZeroDivisors (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ)) :=
      nonzerodiv_image_single ((N.stage2 i₀ s t hY hb).localMulticenter γ)
        PUnit.unit
    have hmem : ((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit ∈
        Ideal.span {f ((N.localMulticenter γ).elem i₀) ^ t} :=
      (N.stage2_elem_span i₀ s t hY hb γ) ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    have h4 : g2 c * (g2 (f ((N.localMulticenter γ).elem i₀))) ^ t ∈
        nonZeroDivisors (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ)) := by
      rw [← map_pow, ← map_mul, hc]
      exact hgenH
    exact (mul_mem_nonZeroDivisors.mp h4).2

include hSt in
theorem stage2Chart_M_le (hconst : N.ConstDivisor i₀) (i : N.indnumb)
    (γ : N.cov.J) :
    Ideal.map ((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γ)
        (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ))).comp
      (algebraMap ((N.multiple s).cov.obj γ)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γ))))
        (N.Yideal i γ) ≤
      Ideal.span {((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γ)
        (Multicenter.Dilatation
          ((N.stage2 i₀ s t hY hb).localMulticenter γ))).comp
      (algebraMap ((N.multiple s).cov.obj γ)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γ))))
        ((N.localMulticenter γ).elem i₀) ^ (s i + t)} := by
  set g2 : (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) →+*
      (Multicenter.Dilatation ((N.stage2 i₀ s t hY hb).localMulticenter γ)) :=
    (algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γ)
      (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γ)) : _ →+* _) with hg2
  set f : (N.cov.obj γ) →+*
      (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) :=
    (algebraMap ((N.multiple s).cov.obj γ)
      (Multicenter.Dilatation ((N.multiple s).localMulticenter γ)) :
        _ →+* _) with hf
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap]
  show (g2.comp f) m ∈ Ideal.span
    {(g2.comp f) ((N.localMulticenter γ).elem i₀) ^ (s i + t)}
  simp only [RingHom.comp_apply]
  have hA : f m = f (((N.multiple s).localMulticenter γ).elem i) *
      Dilatation.frac (F := (N.multiple s).localMulticenter γ)
        (Finsupp.single i 1)
        ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩ := by
    have h := ((N.multiple s).localMulticenter γ).algebraMap_eq_pow_mul_frac
      (Finsupp.single i 1) m
      (((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm)
    rw [familyPow_single] at h
    exact h
  have hidH : ((N.stage2 i₀ s t hY hb).localMulticenter γ).ideal PUnit.unit =
      ((N.multiple s).localMulticenter γ).genFracIdeal :=
    N.stage2_Yideal_eq_genFrac i₀ s t hY hb hSt PUnit.unit γ
  have hfracH : Dilatation.frac (F := (N.multiple s).localMulticenter γ)
      (Finsupp.single i 1)
      ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩ ∈
      ((N.stage2 i₀ s t hY hb).localMulticenter γ).ideal PUnit.unit := by
    rw [hidH]
    exact ((N.multiple s).localMulticenter γ).frac_mem_genFracIdeal i hm
  have hQ : g2 (Dilatation.frac (F := (N.multiple s).localMulticenter γ)
      (Finsupp.single i 1)
      ⟨m, ((N.multiple s).localMulticenter γ).mem_largeIdealPow_single i hm⟩) ∈
      Ideal.span
        {g2 (((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit)} :=
    Multicenter.self_le ((N.stage2 i₀ s t hY hb).localMulticenter γ) PUnit.unit
      (Ideal.mem_map_of_mem _ hfracH)
  have hmemH : ((N.stage2 i₀ s t hY hb).localMulticenter γ).elem PUnit.unit ∈
      Ideal.span {f ((N.localMulticenter γ).elem i₀) ^ t} :=
    (N.stage2_elem_span i₀ s t hY hb γ) ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmemH
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hQ
  obtain ⟨u, hu⟩ := N.hom_multipleGen_mem_at γ s i f
  rw [hconst γ i] at hu
  refine Ideal.mem_span_singleton'.mpr ⟨w * g2 c * g2 u, ?_⟩
  rw [hA, map_mul, ← hu, ← hw, ← hc, map_mul, map_pow, map_mul, map_pow, pow_add]
  ring

theorem stage2Backward_piece_factor
    (γβ : (pull_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap)).J) :
    ∃ ψ : CommRingCat.of (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1)) ⟶
        (pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
          ((N.stage2 i₀ s t hY hb).structureMap ≫
            (N.multiple s).structureMap) γβ.1).obj γβ.2,
      pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
          ((N.stage2 i₀ s t hY hb).structureMap ≫
            (N.multiple s).structureMap) γβ =
        CommRingCat.ofHom ((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1))).comp
          (algebraMap ((N.multiple s).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((N.multiple s).localMulticenter γβ.1)))) ≫ ψ ∧
      RingHom.Flat ψ.hom := by
  have hsnd : (pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) γβ.1).map γβ.2 ≫
      pullback.snd ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) (N.Drep.cov.map γβ.1) =
      Spec.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ) :=
    (spec_map_pull_mor_ring _ _ γβ).symm
  have hcwB : (((pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) (N.Drep.cov.map γβ.1)) ≫
      (N.stage2 i₀ s t hY hb).structureMap) ≫ (N.multiple s).structureMap =
      Spec.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ) ≫ N.cov.map γβ.1 := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, hsnd]
    rfl
  obtain ⟨sB, hsB1, hsB2⟩ := (N.multiple s).exists_chart_factorisation' γβ.1
    _ _ hcwB
  have hcwN : ((pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) γβ.1).map γβ.2 ≫
      pullback.fst ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) (N.Drep.cov.map γβ.1)) ≫
      (N.stage2 i₀ s t hY hb).structureMap =
      Spec.map (Spec.preimage sB) ≫ (N.stage2 i₀ s t hY hb).cov.map γβ.1 := by
    rw [Spec.map_preimage]
    exact hsB1.symm
  obtain ⟨sN, hsN1, hsN2⟩ := (N.stage2 i₀ s t hY hb).exists_chart_factorisation'
    γβ.1 _ _ hcwN
  refine ⟨Spec.preimage sN, ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, CommRingCat.ofHom_comp, Spec.map_comp]
    have hsN2' : sN ≫ (N.stage2 i₀ s t hY hb).chartHom γβ.1 = sB := by
      rw [hsN2, Spec.map_preimage]
    rw [← hsB2, ← hsN2']
    simp only [Category.assoc]
    rfl
  · haveI hc : IsOpenImmersion ((pull_loc_cov X N.Drep
        (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ.1).map γβ.2 ≫
        pullback.fst ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) (N.Drep.cov.map γβ.1)) :=
      (pull_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap)).map_prop γβ
    haveI hsc : IsOpenImmersion (sN ≫
        (N.stage2 i₀ s t hY hb).chartTo γβ.1) := by
      rw [hsN1]
      exact hc
    haveI hsn : IsOpenImmersion sN :=
      IsOpenImmersion.of_comp sN ((N.stage2 i₀ s t hY hb).chartTo γβ.1)
    haveI hflat : AlgebraicGeometry.Flat sN := inferInstance
    haveI hflat2 : AlgebraicGeometry.Flat (Spec.map (Spec.preimage sN)) := by
      rw [Spec.map_preimage]
      exact hflat
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Flat)).mp hflat2

include hSt in
theorem stage2Backward_pullSubset_chart (hconst : N.ConstDivisor i₀)
    (i : N.indnumb)
    (γβ : (pull_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap)).J) :
    Ideal.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ).hom (N.Yideal i γβ.1) ≤
      Ideal.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ).hom
        ((N.Dideal i γβ.1) ^ (N.bump s t i)) := by
  obtain ⟨ψ, hψ, -⟩ := N.stage2Backward_piece_factor i₀ s t hY hb γβ
  rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hstep : ∀ (I : Ideal (N.cov.obj γβ.1)),
      Ideal.map ((CommRingCat.Hom.hom ψ).comp
        ((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1))).comp
          (algebraMap ((N.multiple s).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((N.multiple s).localMulticenter γβ.1))))) I =
      Ideal.map (CommRingCat.Hom.hom ψ)
        (Ideal.map ((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γβ.1)
          (Multicenter.Dilatation
            ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1))).comp
          (algebraMap ((N.multiple s).cov.obj γβ.1)
            (Multicenter.Dilatation
              ((N.multiple s).localMulticenter γβ.1)))) I) :=
    fun I => (Ideal.map_map _ _).symm
  rw [hstep, hstep]
  refine Ideal.map_mono ?_
  refine le_trans (N.stage2Chart_M_le i₀ s t hY hb hSt hconst i γβ.1) ?_
  rw [Ideal.map_pow, N.local_Dideal_span' γβ.1 i, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow, hconst γβ.1 i]
  exact le_rfl

include hSt in
theorem stage2Backward_pullSubset (hconst : N.ConstDivisor i₀) :
    (N.multiple (N.bump s t)).pullSubset
      ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap) :=
  ((N.multiple (N.bump s t)).pullSubset_iff _).mpr
    (fun i γβ => N.stage2Backward_pullSubset_chart i₀ s t hY hb hSt hconst i γβ)

include hSt in
theorem stage2Backward_isCars_chart (hconst : N.ConstDivisor i₀) (i : N.indnumb)
    (γβ : (pull_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap)).J) :
    ∃ g : (pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (N.stage2 i₀ s t hY hb).dilatation
          ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
          (N.multiple (N.bump s t)).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X N.Drep
        (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := N.stage2Backward_piece_factor i₀ s t hY hb γβ
  refine ⟨ψ.hom (((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1))).comp
      (algebraMap ((N.multiple s).cov.obj γβ.1)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γβ.1))))
      ((N.localMulticenter γβ.1).elem i₀) ^ (N.bump s t i)), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ).hom
        ((N.Dideal i γβ.1) ^ (N.bump s t i)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      N.local_Dideal_span' γβ.1 i, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, map_pow, hconst γβ.1 i]
    rfl
  · exact hflat.preserves_nonzeroDivisors
      (N.stage2Chart_alpha_nzd i₀ s t hY hb hSt hconst i γβ.1)

include hSt in
theorem stage2Backward_isCars (hconst : N.ConstDivisor i₀) :
    IsCars (N.stage2 i₀ s t hY hb).dilatation
      (Clos.pullback ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) (N.multiple (N.bump s t)).D) :=
  ⟨pullback_PreClos X (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
      (N.multiple (N.bump s t)).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => N.stage2Backward_isCars_chart i₀ s t hY hb hSt hconst i γβ),
    rfl⟩

include hSt in
theorem existsUnique_stage2Bwd (hconst : N.ConstDivisor i₀) :
    ∃! g : (N.stage2 i₀ s t hY hb).dilatation ⟶
        (N.multiple (N.bump s t)).dilatation,
      g ≫ (N.multiple (N.bump s t)).structureMap =
        (N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap :=
  (N.multiple (N.bump s t)).universal_property _
    ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
    (N.stage2Backward_isCars i₀ s t hY hb hSt hconst)
    (N.stage2Backward_pullSubset i₀ s t hY hb hSt hconst)

include hSt in
theorem stage2Backward_isCars_s_chart (hconst : N.ConstDivisor i₀) (i : N.indnumb)
    (γβ : (pull_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap)).J) :
    ∃ g : (pull_loc_cov X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ.1).obj γβ.2,
      (pullback_PreClos X (N.stage2 i₀ s t hY hb).dilatation
          ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
          (N.multiple s).Drep).ideal i γβ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors ((pull_loc_cov X N.Drep
        (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ.1).obj γβ.2) := by
  obtain ⟨ψ, hψ, hflat⟩ := N.stage2Backward_piece_factor i₀ s t hY hb γβ
  refine ⟨ψ.hom (((algebraMap ((N.stage2 i₀ s t hY hb).cov.obj γβ.1)
      (Multicenter.Dilatation
        ((N.stage2 i₀ s t hY hb).localMulticenter γβ.1))).comp
      (algebraMap ((N.multiple s).cov.obj γβ.1)
        (Multicenter.Dilatation ((N.multiple s).localMulticenter γβ.1))))
      ((N.localMulticenter γβ.1).elem i₀ ^ (s i))), ?_, ?_⟩
  · show Ideal.map (pull_mor_ring X N.Drep (N.stage2 i₀ s t hY hb).dilatation
        ((N.stage2 i₀ s t hY hb).structureMap ≫
          (N.multiple s).structureMap) γβ).hom
        ((N.Dideal i γβ.1) ^ (s i)) = _
    rw [hψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      N.local_Dideal_span' γβ.1 i, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply, hconst γβ.1 i]
    rfl
  · refine hflat.preserves_nonzeroDivisors ?_
    rw [map_pow]
    have h := N.stage2Chart_alpha_nzd i₀ s t hY hb hSt hconst i γβ.1
    rw [pow_add] at h
    exact (mul_mem_nonZeroDivisors.mp h).1

include hSt in
theorem stage2Backward_isCars_s (hconst : N.ConstDivisor i₀) :
    IsCars (N.stage2 i₀ s t hY hb).dilatation
      (Clos.pullback ((N.stage2 i₀ s t hY hb).structureMap ≫
        (N.multiple s).structureMap) (N.multiple s).D) :=
  ⟨pullback_PreClos X (N.stage2 i₀ s t hY hb).dilatation
      ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
      (N.multiple s).Drep,
    pullback_IsPreCars_of_charts _ _ _
      (fun i γβ => N.stage2Backward_isCars_s_chart i₀ s t hY hb hSt hconst i γβ),
    rfl⟩

end BackwardChart

section MainIso52

variable {X : Scheme.{u+1}} (N : PreMultiCenter X) (i₀ : N.indnumb)
  (s : N.indnumb → ℕ) (t : ℕ)
  (hY : N.CentersOver i₀) (hb : N.CarsOnCenter i₀) (hSt : N.ElemNzdOnCenter i₀)
  (hconst : N.ConstDivisor i₀)

include hSt hconst in
def stage2Fwd :
    (N.multiple (N.bump s t)).dilatation ⟶ (N.stage2 i₀ s t hY hb).dilatation :=
  (N.existsUnique_stage2Fwd i₀ s t hY hb hSt hconst).choose

include hSt hconst in
@[simp] theorem stage2Fwd_over :
    N.stage2Fwd i₀ s t hY hb hSt hconst ≫ (N.stage2 i₀ s t hY hb).structureMap =
      N.multipleHom (N.bump s t) s (N.le_bump s t) :=
  (N.existsUnique_stage2Fwd i₀ s t hY hb hSt hconst).choose_spec.1

include hSt hconst in
def stage2Bwd :
    (N.stage2 i₀ s t hY hb).dilatation ⟶ (N.multiple (N.bump s t)).dilatation :=
  (N.existsUnique_stage2Bwd i₀ s t hY hb hSt hconst).choose

include hSt hconst in
@[simp] theorem stage2Bwd_over :
    N.stage2Bwd i₀ s t hY hb hSt hconst ≫
        (N.multiple (N.bump s t)).structureMap =
      (N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap :=
  (N.existsUnique_stage2Bwd i₀ s t hY hb hSt hconst).choose_spec.1

include hSt hconst in
theorem stage2Fwd_comp_stage2Bwd :
    N.stage2Fwd i₀ s t hY hb hSt hconst ≫ N.stage2Bwd i₀ s t hY hb hSt hconst =
      𝟙 _ := by
  have e₁ : (N.stage2Fwd i₀ s t hY hb hSt hconst ≫
      N.stage2Bwd i₀ s t hY hb hSt hconst) ≫
      (N.multiple (N.bump s t)).structureMap =
      (N.multiple (N.bump s t)).structureMap := by
    rw [Category.assoc, N.stage2Bwd_over i₀ s t hY hb hSt hconst,
      ← Category.assoc, N.stage2Fwd_over i₀ s t hY hb hSt hconst,
      N.multipleHom_over (N.bump s t) s (N.le_bump s t)]
  exact ((N.multiple (N.bump s t)).universal_property
    (N.multiple (N.bump s t)).dilatation (N.multiple (N.bump s t)).structureMap
    (N.multiple (N.bump s t)).structureMap_isCars
    (N.multiple (N.bump s t)).structureMap_pullSubset).unique e₁
    (Category.id_comp _)

include hSt hconst in
theorem stage2Bwd_over_base :
    N.stage2Bwd i₀ s t hY hb hSt hconst ≫
        N.multipleHom (N.bump s t) s (N.le_bump s t) =
      (N.stage2 i₀ s t hY hb).structureMap := by
  have e₁ : (N.stage2Bwd i₀ s t hY hb hSt hconst ≫
      N.multipleHom (N.bump s t) s (N.le_bump s t)) ≫
      (N.multiple s).structureMap =
      (N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap := by
    rw [Category.assoc, N.multipleHom_over (N.bump s t) s (N.le_bump s t),
      N.stage2Bwd_over i₀ s t hY hb hSt hconst]
  exact ((N.multiple s).universal_property (N.stage2 i₀ s t hY hb).dilatation
    ((N.stage2 i₀ s t hY hb).structureMap ≫ (N.multiple s).structureMap)
    (N.stage2Backward_isCars_s i₀ s t hY hb hSt hconst)
    (N.pullSubset_of_over_dilatation s
      ((N.stage2 i₀ s t hY hb).structureMap))).unique e₁ rfl

include hSt hconst in
theorem stage2Bwd_comp_stage2Fwd :
    N.stage2Bwd i₀ s t hY hb hSt hconst ≫ N.stage2Fwd i₀ s t hY hb hSt hconst =
      𝟙 _ := by
  have e₁ : (N.stage2Bwd i₀ s t hY hb hSt hconst ≫
      N.stage2Fwd i₀ s t hY hb hSt hconst) ≫
      (N.stage2 i₀ s t hY hb).structureMap =
      (N.stage2 i₀ s t hY hb).structureMap := by
    rw [Category.assoc, N.stage2Fwd_over i₀ s t hY hb hSt hconst,
      N.stage2Bwd_over_base i₀ s t hY hb hSt hconst]
  exact ((N.stage2 i₀ s t hY hb).universal_property
    (N.stage2 i₀ s t hY hb).dilatation (N.stage2 i₀ s t hY hb).structureMap
    (N.stage2 i₀ s t hY hb).structureMap_isCars
    (N.stage2 i₀ s t hY hb).structureMap_pullSubset).unique e₁
    (Category.id_comp _)

include hSt hconst in

def stage2SchemeIso :
    (N.multiple (N.bump s t)).dilatation ≅ (N.stage2 i₀ s t hY hb).dilatation where
  hom := N.stage2Fwd i₀ s t hY hb hSt hconst
  inv := N.stage2Bwd i₀ s t hY hb hSt hconst
  hom_inv_id := N.stage2Fwd_comp_stage2Bwd i₀ s t hY hb hSt hconst
  inv_hom_id := N.stage2Bwd_comp_stage2Fwd i₀ s t hY hb hSt hconst

include hSt hconst in
@[simp] theorem stage2SchemeIso_hom_over :
    (N.stage2SchemeIso i₀ s t hY hb hSt hconst).hom ≫
      (N.stage2 i₀ s t hY hb).structureMap =
      N.multipleHom (N.bump s t) s (N.le_bump s t) :=
  N.stage2Fwd_over i₀ s t hY hb hSt hconst

include hSt hconst in
theorem stage2SchemeIso_unique
    (g : (N.multiple (N.bump s t)).dilatation ⟶ (N.stage2 i₀ s t hY hb).dilatation)
    (hg : g ≫ (N.stage2 i₀ s t hY hb).structureMap =
      N.multipleHom (N.bump s t) s (N.le_bump s t)) :
    g = (N.stage2SchemeIso i₀ s t hY hb hSt hconst).hom :=
  ((N.existsUnique_stage2Fwd i₀ s t hY hb hSt hconst).unique hg
    (N.stage2Fwd_over i₀ s t hY hb hSt hconst)).trans rfl

end MainIso52

end PreMultiCenter

end SchemeDilatation
