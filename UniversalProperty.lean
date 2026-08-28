import InclusionClos
import GlobalDilatation

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

noncomputable def Clos.pullback {T : Scheme.{u+1}} (f : T ⟶ X) (D : Clos X) : Clos T :=
  Quotient.lift (fun Z => (Quotient.mk'' (pullback_PreClos X T f Z) : Clos T))
    (fun Z Z' h => by
      obtain ⟨R⟩ := h
      exact Quotient.sound ⟨pullback_lem X Z Z' T f R⟩) D

@[simp] theorem Clos.pullback_mk {T : Scheme.{u+1}} (f : T ⟶ X) (Z : PreClos X) :
    Clos.pullback f (Quotient.mk'' Z) = Quotient.mk'' (pullback_PreClos X T f Z) := rfl

theorem Spec_pull_mor_ring (Z : PreClos X) {T : Scheme.{u+1}} (f : T ⟶ X)
    (γβ : (pull_cov X Z T f).J) :
    Spec.map (pull_mor_ring X Z T f γβ) =
      (pull_loc_cov X Z T f γβ.1).map γβ.2 ≫ pullback.snd f (Z.cov.map γβ.1) := by
  change Spec.map (_ ≫ _ ≫ _) = _
  simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
    Spec.toLocallyRingedSpace_obj, Scheme.Γ_map, Quiver.Hom.unop_op']
  rw [← Scheme.toSpecΓ_naturality_assoc]
  show ((pull_loc_cov X Z T f γβ.1).map γβ.2 ≫ pullback.snd f (Z.cov.map γβ.1)) ≫
      (Spec (Z.cov.obj γβ.1)).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (Z.cov.obj γβ.1)).inv = _
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  simp

theorem pull_cov_map_comp (Z : PreClos X) {T : Scheme.{u+1}} (f : T ⟶ X)
    (γβ : (pull_cov X Z T f).J) :
    (pull_cov X Z T f).map γβ ≫ f =
      Spec.map (pull_mor_ring X Z T f γβ) ≫ Z.cov.map γβ.1 := by
  rw [Spec_pull_mor_ring]
  show ((pull_loc_cov X Z T f γβ.1).map γβ.2 ≫ pullback.fst f (Z.cov.map γβ.1)) ≫ f = _
  rw [Category.assoc, pullback.condition, Category.assoc]

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X)

def pullSubset {T : Scheme.{u+1}} (f : T ⟶ X) : Prop :=
  PreClos.subset (pullback_PreClos X T f M.Drep) (pullback_PreClos X T f M.Yrep)
    (Equiv.refl M.indnumb) (pull_cov X M.Drep T f) rfl rfl

theorem largeIdeal_collapse (γ : M.cov.J) {B : CommRingCat.{u+1}} (w : M.cov.obj γ ⟶ B)
    (hY : ∀ i, Ideal.map w.hom (M.Yideal i γ) ≤
      Ideal.span {w.hom ((M.localMulticenter γ).elem i)}) (i : M.indnumb) :
    Ideal.span {w.hom ((M.localMulticenter γ).elem i)} =
      Ideal.map w.hom ((M.localMulticenter γ).LargeIdeal i) := by
  show _ = Ideal.map w.hom ((M.localMulticenter γ).ideal i +
    Ideal.span {(M.localMulticenter γ).elem i})
  rw [Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact (sup_eq_right.mpr (hY i)).symm

theorem elem_nonzerodiv {T : Scheme.{u+1}} (f : T ⟶ X) (C : PreClos T)
    (hC : IsPreCars T C) (R : _root_.relStructure C (pullback_PreClos X T f M.Drep))
    {V : Scheme.{u+1}} [IsAffine V]
    (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
    (p : V ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
    (b : V ⟶ Spec (C.cov.obj c)) [IsOpenImmersion b]
    (hpb : b ≫ C.cov.map c = p ≫ (pull_cov X M.Drep T f).map γβ) (i : M.indnumb) :
    ((Spec.preimage (V.isoSpec.inv ≫ p)).hom.comp
        (pull_mor_ring X M.Drep T f γβ).hom) ((M.localMulticenter γβ.1).elem i) ∈
      nonZeroDivisors Γ(V, ⊤) := by
  classical
  set j := R.indnumb_equiv.symm i with hj
  letI := hC.prin j c
  letI := M.Dprin i γβ.1
  letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1

  letI : Algebra (C.cov.obj c) Γ(V, ⊤) :=
    (Spec.preimage (V.isoSpec.inv ≫ b)).hom.toAlgebra
  have hmb : Spec.map (CommRingCat.ofHom (algebraMap (C.cov.obj c) Γ(V, ⊤))) =
      V.isoSpec.inv ≫ b := Spec.map_preimage _
  haveI : IsOpenImmersion (Spec Γ(V, ⊤) ↘ Spec (C.cov.obj c)) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (C.cov.obj c) Γ(V, ⊤))))
    rw [hmb]; infer_instance
  have hflat : RingHom.Flat (algebraMap (C.cov.obj c) Γ(V, ⊤)) := open_flat_ring _ _
  have hCnzd : (algebraMap (C.cov.obj c) Γ(V, ⊤))
      (Submodule.IsPrincipal.generator (C.ideal j c)) ∈ nonZeroDivisors Γ(V, ⊤) :=
    hflat.preserves_nonzeroDivisors (hC.nonzerodiv j c)

  have hagree := chartIdeal_agree_rel C (pullback_PreClos X T f M.Drep) R b p hpb j
  rw [show R.indnumb_equiv j = i from by rw [hj, Equiv.apply_symm_apply]] at hagree

  have hleft : Ideal.map (Spec.preimage (V.isoSpec.inv ≫ b)).hom (C.ideal j c) =
      Ideal.span {(algebraMap (C.cov.obj c) Γ(V, ⊤))
        (Submodule.IsPrincipal.generator (C.ideal j c))} := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.span_singleton_generator]
    rfl
  have hright : Ideal.map (Spec.preimage (V.isoSpec.inv ≫ p)).hom
      ((pullback_PreClos X T f M.Drep).ideal i γβ) =
      Ideal.span {((Spec.preimage (V.isoSpec.inv ≫ p)).hom.comp
        (pull_mor_ring X M.Drep T f γβ).hom) ((M.localMulticenter γβ.1).elem i)} := by
    show Ideal.map (Spec.preimage (V.isoSpec.inv ≫ p)).hom
      (Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Drep.ideal i γβ.1)) = _
    rw [Ideal.map_map, ← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1),
      Ideal.map_span, Set.image_singleton]
    rfl
  rw [hleft, hright] at hagree
  exact nonZeroDivisors_of_span_singleton_eq hagree.symm hCnzd

theorem local_unique {T : Scheme.{u+1}} (f : T ⟶ X) {V : Scheme.{u+1}} [IsAffine V]
    (v : V ⟶ T) (γ : M.cov.J) (a : V ⟶ Spec (M.cov.obj γ))
    (hva : v ≫ f = a ≫ M.cov.map γ)
    (hnzd : ∀ i, (Spec.preimage (V.isoSpec.inv ≫ a)).hom
      ((M.localMulticenter γ).elem i) ∈ nonZeroDivisors Γ(V, ⊤))
    (hgen : ∀ i, Ideal.span {(Spec.preimage (V.isoSpec.inv ≫ a)).hom
        ((M.localMulticenter γ).elem i)} =
      Ideal.map (Spec.preimage (V.isoSpec.inv ≫ a)).hom
        ((M.localMulticenter γ).LargeIdeal i))
    (u u' : V ⟶ M.dilatation)
    (hu : u ≫ M.structureMap = v ≫ f) (hu' : u' ≫ M.structureMap = v ≫ f) :
    u = u' := by
  haveI := M.cov.map_prop γ
  haveI : Mono (M.cov.map γ) := inferInstance

  have hrange : ∀ t : V ⟶ M.dilatation, t ≫ M.structureMap = v ≫ f →
      Set.range t.base ⊆ Set.range (M.chartTo γ).base := by
    intro t ht
    rintro _ ⟨x, rfl⟩
    refine M.structureMap_range γ _ ?_
    have h := congrArg (fun s : V ⟶ X => s.base x) ht
    have hv := congrArg (fun s : V ⟶ X => s.base x) hva
    simp only [Scheme.comp_base_apply] at h hv
    rw [h, hv]
    exact ⟨a.base x, rfl⟩
  set ū := IsOpenImmersion.lift (M.chartTo γ) u (hrange u hu) with hūdef
  set ū' := IsOpenImmersion.lift (M.chartTo γ) u' (hrange u' hu') with hū'def
  have hfac : ū ≫ M.chartTo γ = u := IsOpenImmersion.lift_fac _ _ _
  have hfac' : ū' ≫ M.chartTo γ = u' := IsOpenImmersion.lift_fac _ _ _

  have hover : ∀ t : V ⟶ M.chart γ, t ≫ M.chartTo γ ≫ M.structureMap = v ≫ f →
      t ≫ M.chartHom γ = a := by
    intro t ht
    rw [M.structureMap_chart γ] at ht
    rw [← cancel_mono (M.cov.map γ), Category.assoc]
    show t ≫ M.chartToX γ = a ≫ M.cov.map γ
    rw [ht, hva]
  have h1 : ū ≫ M.chartHom γ = a := hover ū (by rw [← Category.assoc, hfac]; exact hu)
  have h2 : ū' ≫ M.chartHom γ = a := hover ū' (by rw [← Category.assoc, hfac']; exact hu')
  have hbase : V.isoSpec.hom ≫ Spec.map (Spec.preimage (V.isoSpec.inv ≫ a)) = a := by
    rw [Spec.map_preimage, Iso.hom_inv_id_assoc]
  have hkey : ū = ū' := by
    refine dilaUniqueAffine (M.cov.obj γ) (M.localMulticenter γ) _ hnzd hgen ū ū' ?_ ?_
    · show ū ≫ M.chartHom γ = _
      rw [h1]; exact hbase.symm
    · show ū' ≫ M.chartHom γ = _
      rw [h2]; exact hbase.symm
  rw [← hfac, ← hfac', hkey]

section Refine

variable {T : Scheme.{u+1}} (f : T ⟶ X) (C : PreClos T)

def dbl (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J) : Scheme.{u+1} :=
  pullback ((pull_cov X M.Drep T f).map γβ) (C.cov.map c)

theorem exists_dbl_point (t : T) :
    ∃ q : M.dbl f C ((pull_cov X M.Drep T f).f t) (C.cov.f t),
      (pullback.fst ((pull_cov X M.Drep T f).map ((pull_cov X M.Drep T f).f t))
        (C.cov.map (C.cov.f t)) ≫
        (pull_cov X M.Drep T f).map ((pull_cov X M.Drep T f).f t)).base q = t := by
  obtain ⟨s, hs⟩ := (pull_cov X M.Drep T f).covers t
  have hmem : s ∈ ((pull_cov X M.Drep T f).map ((pull_cov X M.Drep T f).f t)).base ⁻¹'
      Set.range (C.cov.map (C.cov.f t)).base := by
    rw [Set.mem_preimage, hs]
    exact C.cov.covers t
  rw [← Scheme.Pullback.range_fst] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_⟩
  rw [Scheme.comp_base_apply, hq, hs]

noncomputable def refineCover : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) T where
  J := (γβ : (pull_cov X M.Drep T f).J) × (c : C.cov.J) ×
    (Scheme.affineOpenCover (M.dbl f C γβ c)).J
  obj p := (Scheme.affineOpenCover (M.dbl f C p.1 p.2.1)).obj p.2.2
  map p := (Scheme.affineOpenCover (M.dbl f C p.1 p.2.1)).map p.2.2 ≫
    pullback.fst _ _ ≫ (pull_cov X M.Drep T f).map p.1
  f t := ⟨(pull_cov X M.Drep T f).f t, C.cov.f t,
    (Scheme.affineOpenCover (M.dbl f C _ _)).f (M.exists_dbl_point f C t).choose⟩
  covers t := by
    obtain ⟨y, hy⟩ := (Scheme.affineOpenCover (M.dbl f C ((pull_cov X M.Drep T f).f t)
      (C.cov.f t))).covers (M.exists_dbl_point f C t).choose
    refine ⟨y, ?_⟩
    simp only [Scheme.comp_base_apply]
    rw [hy]
    have := (M.exists_dbl_point f C t).choose_spec
    rw [Scheme.comp_base_apply] at this
    exact this
  map_prop p := by
    haveI : IsOpenImmersion ((pull_cov X M.Drep T f).map p.1) :=
      (pull_cov X M.Drep T f).map_prop p.1
    haveI : IsOpenImmersion ((Scheme.affineOpenCover (M.dbl f C p.1 p.2.1)).map p.2.2) :=
      inferInstance
    infer_instance

noncomputable def refineChartMap (j : (M.refineCover f C).J) :
    Spec ((M.refineCover f C).obj j) ⟶ Spec (M.cov.obj j.1.1) :=
  (Scheme.affineOpenCover (M.dbl f C j.1 j.2.1)).map j.2.2 ≫
    pullback.fst ((pull_cov X M.Drep T f).map j.1) (C.cov.map j.2.1) ≫
    Spec.map (pull_mor_ring X M.Drep T f j.1)

theorem refineCover_map_comp (j : (M.refineCover f C).J) :
    (M.refineCover f C).map j ≫ f = M.refineChartMap f C j ≫ M.cov.map j.1.1 := by
  show ((Scheme.affineOpenCover (M.dbl f C j.1 j.2.1)).map j.2.2 ≫
    pullback.fst _ _ ≫ (pull_cov X M.Drep T f).map j.1) ≫ f = _
  unfold refineChartMap
  simp only [Category.assoc]
  rw [pull_cov_map_comp]
  rfl

noncomputable def refineCarsMap (j : (M.refineCover f C).J) :
    Spec ((M.refineCover f C).obj j) ⟶ Spec (C.cov.obj j.2.1) :=
  (Scheme.affineOpenCover (M.dbl f C j.1 j.2.1)).map j.2.2 ≫
    pullback.snd ((pull_cov X M.Drep T f).map j.1) (C.cov.map j.2.1)

instance refineCarsMap_isOpenImmersion (j : (M.refineCover f C).J) :
    IsOpenImmersion (M.refineCarsMap f C j) := by
  unfold refineCarsMap
  haveI : IsOpenImmersion ((pull_cov X M.Drep T f).map j.1) :=
    (pull_cov X M.Drep T f).map_prop j.1
  infer_instance

theorem refine_legs_comm (j : (M.refineCover f C).J) :
    M.refineCarsMap f C j ≫ C.cov.map j.2.1 =
      (Scheme.affineOpenCover (M.dbl f C j.1 j.2.1)).map j.2.2 ≫
        pullback.fst ((pull_cov X M.Drep T f).map j.1) (C.cov.map j.2.1) ≫
        (pull_cov X M.Drep T f).map j.1 := by
  unfold refineCarsMap
  rw [Category.assoc, ← pullback.condition]

noncomputable def refinePullMap (j : (M.refineCover f C).J) :
    Spec ((M.refineCover f C).obj j) ⟶ Spec ((pull_cov X M.Drep T f).obj j.1) :=
  (Scheme.affineOpenCover (M.dbl f C j.1 j.2.1)).map j.2.2 ≫
    pullback.fst ((pull_cov X M.Drep T f).map j.1) (C.cov.map j.2.1)

theorem refineChartMap_preimage (j : (M.refineCover f C).J) :
    Spec.preimage ((Spec ((M.refineCover f C).obj j)).isoSpec.inv ≫
        M.refineChartMap f C j) =
      pull_mor_ring X M.Drep T f j.1 ≫
        Spec.preimage ((Spec ((M.refineCover f C).obj j)).isoSpec.inv ≫
          M.refinePullMap f C j) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
  unfold refineChartMap refinePullMap
  simp only [Category.assoc]

theorem exists_piece (x : T) :
    x ∈ Set.range ((M.refineCover f C).map ((M.refineCover f C).f x)).base :=
  (M.refineCover f C).covers x

end Refine

theorem universal_property_exists (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) :
    ∃ g : T ⟶ M.dilatation, g ≫ M.structureMap = f := by

  obtain ⟨C, hCpre, hCeq⟩ := hCars
  rw [show Clos.pullback f M.D =
      Quotient.mk'' (pullback_PreClos X T f M.Drep) from by
    first
      | rfl
      | simp [PreMultiCenter.D]
      | rw [PreMultiCenter.D]] at hCeq
  obtain ⟨R⟩ := Quotient.exact' hCeq

  have key : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧
      ∃ (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
        (p : Spec Rr ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
        (b : Spec Rr ⟶ Spec (C.cov.obj c)),
        IsOpenImmersion b ∧
        p ≫ (pull_cov X M.Drep T f).map γβ = emb ∧
        b ≫ C.cov.map c = emb := by
    intro x
    haveI hp1 : IsOpenImmersion ((pull_cov X M.Drep T f).map
      ((pull_cov X M.Drep T f).f x)) := (pull_cov X M.Drep T f).map_prop _
    haveI hp2 : IsOpenImmersion (C.cov.map (C.cov.f x)) := C.cov.map_prop _
    set U : T.Opens :=
      ⟨Set.range ((pull_cov X M.Drep T f).map ((pull_cov X M.Drep T f).f x)).base ∩
        Set.range (C.cov.map (C.cov.f x)).base,
        (hp1.base_open.isOpen_range).inter (hp2.base_open.isOpen_range)⟩ with hU
    have hxU : x ∈ U :=
      ⟨(pull_cov X M.Drep T f).covers x, C.cov.covers x⟩
    obtain ⟨Rr, emb, hemb, hxe, hrange⟩ :=
      AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
    haveI := hemb
    refine ⟨Rr, emb, hemb, hxe, (pull_cov X M.Drep T f).f x, C.cov.f x,
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).1),
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).2), ?_,
      IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩
    haveI : IsOpenImmersion (IsOpenImmersion.lift (C.cov.map (C.cov.f x)) emb
        (fun _ hy => (hrange hy).2) ≫ C.cov.map (C.cov.f x)) := by
      rw [IsOpenImmersion.lift_fac]
      exact hemb
    exact IsOpenImmersion.of_comp _ (C.cov.map (C.cov.f x))
  have cond : ∀ (V : Scheme.{u+1}) (_ : IsAffine V)
      (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
      (p : V ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
      (b : V ⟶ Spec (C.cov.obj c)) (_ : IsOpenImmersion b)
      (_ : b ≫ C.cov.map c = p ≫ (pull_cov X M.Drep T f).map γβ),
      (∀ i, (Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
          ((M.localMulticenter γβ.1).elem i) ∈ nonZeroDivisors Γ(V, ⊤)) ∧
      (∀ i, Ideal.span {(Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
            ((M.localMulticenter γβ.1).elem i)} =
          Ideal.map (Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
            ((M.localMulticenter γβ.1).LargeIdeal i)) := by
    intro V hV γβ c p b hb hpb
    haveI := hV
    haveI := hb
    have hbridge : Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ))) =
        pull_mor_ring X M.Drep T f γβ ≫
          Spec.preimage (V.isoSpec.inv ≫ p) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
    letI : Algebra (M.cov.obj γβ.1) Γ(V, ⊤) :=
      (Spec.preimage (V.isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom.toAlgebra
    refine ⟨fun i => ?_, ?_⟩
    · rw [hbridge]
      exact M.elem_nonzerodiv f C hCpre R γβ c p b hpb i
    · refine M.largeIdeal_collapse γβ.1 _ (fun i => ?_)
      letI := M.Dprin i γβ.1
      letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
      have hY := hsub i γβ
      rw [hbridge, CommRingCat.hom_comp, ← Ideal.map_map]
      refine le_trans (Ideal.map_mono hY) ?_
      show Ideal.map _ (Ideal.map (pull_mor_ring X M.Drep T f γβ).hom
        (M.Drep.ideal i γβ.1)) ≤ _
      rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1),
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
      exact le_rfl
  have key2 : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T)
      (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
      (p : Spec Rr ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
      (b : Spec Rr ⟶ Spec (C.cov.obj c)) (g : Spec Rr ⟶ M.dilatation),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧ IsOpenImmersion b ∧
      p ≫ (pull_cov X M.Drep T f).map γβ = emb ∧
      b ≫ C.cov.map c = emb ∧
      g ≫ M.structureMap = emb ≫ f := by
    intro x
    obtain ⟨Rr, emb, hemb, hxe, γβ, c, p, b, hb, hp, hbc⟩ := key x
    haveI := hemb
    haveI := hb
    have hva : emb ≫ f =
        (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)) ≫ M.cov.map γβ.1 := by
      rw [← hp, Category.assoc, pull_cov_map_comp, Category.assoc]
      rfl
    have hpb : b ≫ C.cov.map c = p ≫ (pull_cov X M.Drep T f).map γβ := by
      rw [hbc, hp]
    letI : Algebra (M.cov.obj γβ.1) Γ(Spec Rr, ⊤) :=
      (Spec.preimage ((Spec Rr).isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom.toAlgebra
    obtain ⟨hnzd, hgen⟩ := cond (Spec Rr) inferInstance γβ c p b hb hpb
    refine ⟨Rr, emb, γβ, c, p, b,
      (Spec Rr).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Multicenter.desc (M.localMulticenter γβ.1) hnzd hgen).toRingHom) ≫
        M.chartTo γβ.1, hemb, hxe, hb, hp, hbc, ?_⟩
    show _ ≫ M.structureMap = _
    rw [Category.assoc, Category.assoc, M.structureMap_chart γβ.1]
    show _ ≫ _ ≫ M.chartHom γβ.1 ≫ M.cov.map γβ.1 = _
    rw [show M.chartHom γβ.1 = Spec.map (CommRingCat.ofHom
      (algebraMap (M.cov.obj γβ.1)
        (Multicenter.Dilatation (M.localMulticenter γβ.1)))) from rfl]
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
    rw [show CommRingCat.ofHom (algebraMap (M.cov.obj γβ.1)
        (Multicenter.Dilatation (M.localMulticenter γβ.1))) ≫
        CommRingCat.ofHom (Multicenter.desc (M.localMulticenter γβ.1)
          hnzd hgen).toRingHom =
        Spec.preimage ((Spec Rr).isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ))) from by
      apply CommRingCat.hom_ext
      ext s
      exact (Multicenter.desc (M.localMulticenter γβ.1) hnzd hgen).commutes s]
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]
    exact hva.symm
  choose Rr emb γβ c p b glift hemb hxe hb hp hbc hglift using key2
  have hcompat : ∀ x y : T, pullback.fst (emb x) (emb y) ≫ glift x =
      pullback.snd (emb x) (emb y) ≫ glift y := by
    intro x y
    haveI := hemb x
    haveI := hemb y
    refine (pullback (emb x) (emb y)).affineCover.hom_ext _ _ (fun k => ?_)
    set ι := (pullback (emb x) (emb y)).affineCover.map k with hι
    haveI : IsOpenImmersion (ι ≫ pullback.fst (emb x) (emb y)) := inferInstance
    haveI : IsOpenImmersion (ι ≫ pullback.fst (emb x) (emb y) ≫ b x) := by
      haveI := hb x
      infer_instance
    obtain ⟨hnzd, hgen⟩ := cond
      ((pullback (emb x) (emb y)).affineCover.obj k) inferInstance (γβ x) (c x)
      (ι ≫ pullback.fst (emb x) (emb y) ≫ p x)
      (ι ≫ pullback.fst (emb x) (emb y) ≫ b x) inferInstance
      (by
        simp only [Category.assoc]
        rw [show b x ≫ C.cov.map (c x) =
          p x ≫ (pull_cov X M.Drep T f).map (γβ x) from (hbc x).trans (hp x).symm])
    refine M.local_unique f
      (ι ≫ pullback.fst (emb x) (emb y) ≫ emb x) (γβ x).1 _ ?_ hnzd hgen _ _ ?_ ?_
    · have hstep : emb x ≫ f =
          (p x ≫ Spec.map (pull_mor_ring X M.Drep T f (γβ x))) ≫
            M.cov.map (γβ x).1 := by
        rw [← hp x, Category.assoc, pull_cov_map_comp, Category.assoc]
        rfl
      simp only [Category.assoc]
      rw [hstep]
      simp only [Category.assoc]
    · simp only [Category.assoc]
      rw [show glift x ≫ M.structureMap = emb x ≫ f from hglift x]
    · simp only [Category.assoc]
      rw [show glift y ≫ M.structureMap = emb y ≫ f from hglift y,
        ← Category.assoc (pullback.snd (emb x) (emb y)), ← pullback.condition]
      simp only [Category.assoc]
  let 𝒰 : T.OpenCover :=
    { J := T, obj := fun x => Spec (Rr x), map := emb, f := fun t => t,
      covers := hxe, map_prop := hemb }
  refine ⟨𝒰.glueMorphisms glift hcompat, ?_⟩
  refine 𝒰.hom_ext _ _ (fun x => ?_)
  rw [← Category.assoc, 𝒰.ι_glueMorphisms glift hcompat x]
  exact hglift x

theorem universal_property_unique (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f)
    (u u' : T ⟶ M.dilatation)
    (hu : u ≫ M.structureMap = f) (hu' : u' ≫ M.structureMap = f) :
    u = u' := by
  obtain ⟨C, hCpre, hCeq⟩ := hCars
  rw [show Clos.pullback f M.D =
      Quotient.mk'' (pullback_PreClos X T f M.Drep) from by
    first
      | rfl
      | simp [PreMultiCenter.D]
      | rw [PreMultiCenter.D]] at hCeq
  obtain ⟨R⟩ := Quotient.exact' hCeq
  have key : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧
      ∃ (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
        (p : Spec Rr ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
        (b : Spec Rr ⟶ Spec (C.cov.obj c)),
        IsOpenImmersion b ∧
        p ≫ (pull_cov X M.Drep T f).map γβ = emb ∧
        b ≫ C.cov.map c = emb := by
    intro x
    haveI hp1 : IsOpenImmersion ((pull_cov X M.Drep T f).map
      ((pull_cov X M.Drep T f).f x)) := (pull_cov X M.Drep T f).map_prop _
    haveI hp2 : IsOpenImmersion (C.cov.map (C.cov.f x)) := C.cov.map_prop _
    set U : T.Opens :=
      ⟨Set.range ((pull_cov X M.Drep T f).map ((pull_cov X M.Drep T f).f x)).base ∩
        Set.range (C.cov.map (C.cov.f x)).base,
        (hp1.base_open.isOpen_range).inter (hp2.base_open.isOpen_range)⟩ with hU
    have hxU : x ∈ U :=
      ⟨(pull_cov X M.Drep T f).covers x, C.cov.covers x⟩
    obtain ⟨Rr, emb, hemb, hxe, hrange⟩ :=
      AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
    haveI := hemb
    refine ⟨Rr, emb, hemb, hxe, (pull_cov X M.Drep T f).f x, C.cov.f x,
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).1),
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).2), ?_,
      IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩
    haveI : IsOpenImmersion (IsOpenImmersion.lift (C.cov.map (C.cov.f x)) emb
        (fun _ hy => (hrange hy).2) ≫ C.cov.map (C.cov.f x)) := by
      rw [IsOpenImmersion.lift_fac]
      exact hemb
    exact IsOpenImmersion.of_comp _ (C.cov.map (C.cov.f x))
  have cond : ∀ (V : Scheme.{u+1}) (_ : IsAffine V)
      (γβ : (pull_cov X M.Drep T f).J) (c : C.cov.J)
      (p : V ⟶ Spec ((pull_cov X M.Drep T f).obj γβ))
      (b : V ⟶ Spec (C.cov.obj c)) (_ : IsOpenImmersion b)
      (_ : b ≫ C.cov.map c = p ≫ (pull_cov X M.Drep T f).map γβ),
      (∀ i, (Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
          ((M.localMulticenter γβ.1).elem i) ∈ nonZeroDivisors Γ(V, ⊤)) ∧
      (∀ i, Ideal.span {(Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
            ((M.localMulticenter γβ.1).elem i)} =
          Ideal.map (Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom
            ((M.localMulticenter γβ.1).LargeIdeal i)) := by
    intro V hV γβ c p b hb hpb
    haveI := hV
    haveI := hb
    have hbridge : Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ))) =
        pull_mor_ring X M.Drep T f γβ ≫
          Spec.preimage (V.isoSpec.inv ≫ p) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
    letI : Algebra (M.cov.obj γβ.1) Γ(V, ⊤) :=
      (Spec.preimage (V.isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.Drep T f γβ)))).hom.toAlgebra
    refine ⟨fun i => ?_, ?_⟩
    · rw [hbridge]
      exact M.elem_nonzerodiv f C hCpre R γβ c p b hpb i
    · refine M.largeIdeal_collapse γβ.1 _ (fun i => ?_)
      letI := M.Dprin i γβ.1
      letI : Submodule.IsPrincipal (M.Drep.ideal i γβ.1) := M.Dprin i γβ.1
      have hY := hsub i γβ
      rw [hbridge, CommRingCat.hom_comp, ← Ideal.map_map]
      refine le_trans (Ideal.map_mono hY) ?_
      show Ideal.map _ (Ideal.map (pull_mor_ring X M.Drep T f γβ).hom
        (M.Drep.ideal i γβ.1)) ≤ _
      rw [← Ideal.span_singleton_generator (M.Drep.ideal i γβ.1),
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
      exact le_rfl
  choose Rr emb hemb hxe γβ c p b hb hp hbc using key
  let 𝒰 : T.OpenCover :=
    { J := T, obj := fun x => Spec (Rr x), map := emb, f := fun t => t,
      covers := hxe, map_prop := hemb }
  refine 𝒰.hom_ext u u' (fun x => ?_)
  haveI := hemb x
  haveI := hb x
  obtain ⟨hnzd, hgen⟩ := cond (Spec (Rr x)) inferInstance (γβ x) (c x) (p x) (b x)
    (hb x) (by rw [hbc x, ← hp x])
  refine M.local_unique f (emb x) (γβ x).1 _ ?_ hnzd hgen _ _ ?_ ?_
  · rw [← hp x, Category.assoc, pull_cov_map_comp, Category.assoc]
    rfl
  · rw [Category.assoc, show u ≫ M.structureMap = f from hu]
  · rw [Category.assoc, show u' ≫ M.structureMap = f from hu']

theorem universal_property (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) :
    ∃! g : T ⟶ M.dilatation, g ≫ M.structureMap = f := by
  obtain ⟨g, hg⟩ := M.universal_property_exists T f hCars hsub
  exact ⟨g, hg, fun g' hg' => M.universal_property_unique T f hCars hsub g' g hg' hg⟩

end PreMultiCenter

namespace MultiCenter

variable (M : MultiCenter X)

def pullSubset {T : Scheme.{u+1}} (f : T ⟶ X) : Prop :=
  ∀ P : PreMultiCenter X, (Quotient.mk'' P : MultiCenter X) = M → P.pullSubset f

theorem universal_property_exists (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) :
    ∃ g : T ⟶ M.dilatation, g ≫ M.structureMap = f := by

  obtain ⟨C, hCpre, hCeq⟩ := hCars
  rw [show Clos.pullback f M.D =
      Quotient.mk'' (pullback_PreClos X T f M.rep.Drep) from by
    rw [← M.rep_D]; rfl] at hCeq
  obtain ⟨R⟩ := Quotient.exact' hCeq

  have key : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧
      ∃ (γβ : (pull_cov X M.rep.Drep T f).J) (c : C.cov.J)
        (p : Spec Rr ⟶ Spec ((pull_cov X M.rep.Drep T f).obj γβ))
        (b : Spec Rr ⟶ Spec (C.cov.obj c)),
        IsOpenImmersion b ∧
        p ≫ (pull_cov X M.rep.Drep T f).map γβ = emb ∧
        b ≫ C.cov.map c = emb := by
    intro x
    haveI hp1 : IsOpenImmersion ((pull_cov X M.rep.Drep T f).map
      ((pull_cov X M.rep.Drep T f).f x)) := (pull_cov X M.rep.Drep T f).map_prop _
    haveI hp2 : IsOpenImmersion (C.cov.map (C.cov.f x)) := C.cov.map_prop _
    set U : T.Opens :=
      ⟨Set.range ((pull_cov X M.rep.Drep T f).map ((pull_cov X M.rep.Drep T f).f x)).base ∩
        Set.range (C.cov.map (C.cov.f x)).base,
        (hp1.base_open.isOpen_range).inter (hp2.base_open.isOpen_range)⟩ with hU
    have hxU : x ∈ U :=
      ⟨(pull_cov X M.rep.Drep T f).covers x, C.cov.covers x⟩
    obtain ⟨Rr, emb, hemb, hxe, hrange⟩ :=
      AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
    haveI := hemb
    refine ⟨Rr, emb, hemb, hxe, (pull_cov X M.rep.Drep T f).f x, C.cov.f x,
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).1),
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).2), ?_,
      IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩
    haveI : IsOpenImmersion (IsOpenImmersion.lift (C.cov.map (C.cov.f x)) emb
        (fun _ hy => (hrange hy).2) ≫ C.cov.map (C.cov.f x)) := by
      rw [IsOpenImmersion.lift_fac]
      exact hemb
    exact IsOpenImmersion.of_comp _ (C.cov.map (C.cov.f x))
  have cond : ∀ (V : Scheme.{u+1}) (_ : IsAffine V)
      (γβ : (pull_cov X M.rep.Drep T f).J) (c : C.cov.J)
      (p : V ⟶ Spec ((pull_cov X M.rep.Drep T f).obj γβ))
      (b : V ⟶ Spec (C.cov.obj c)) (_ : IsOpenImmersion b)
      (_ : b ≫ C.cov.map c = p ≫ (pull_cov X M.rep.Drep T f).map γβ),
      (∀ i, (Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
          ((M.rep.localMulticenter γβ.1).elem i) ∈ nonZeroDivisors Γ(V, ⊤)) ∧
      (∀ i, Ideal.span {(Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
            ((M.rep.localMulticenter γβ.1).elem i)} =
          Ideal.map (Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
            ((M.rep.localMulticenter γβ.1).LargeIdeal i)) := by
    intro V hV γβ c p b hb hpb
    haveI := hV
    haveI := hb
    have hbridge : Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ))) =
        pull_mor_ring X M.rep.Drep T f γβ ≫
          Spec.preimage (V.isoSpec.inv ≫ p) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
    letI : Algebra (M.rep.cov.obj γβ.1) Γ(V, ⊤) :=
      (Spec.preimage (V.isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom.toAlgebra
    refine ⟨fun i => ?_, ?_⟩
    · rw [hbridge]
      exact M.rep.elem_nonzerodiv f C hCpre R γβ c p b hpb i
    · refine M.rep.largeIdeal_collapse γβ.1 _ (fun i => ?_)
      letI := M.rep.Dprin i γβ.1
      letI : Submodule.IsPrincipal (M.rep.Drep.ideal i γβ.1) := M.rep.Dprin i γβ.1
      have hY := hsub M.rep M.rep_eq i γβ
      rw [hbridge, CommRingCat.hom_comp, ← Ideal.map_map]
      refine le_trans (Ideal.map_mono hY) ?_
      show Ideal.map _ (Ideal.map (pull_mor_ring X M.rep.Drep T f γβ).hom
        (M.rep.Drep.ideal i γβ.1)) ≤ _
      rw [← Ideal.span_singleton_generator (M.rep.Drep.ideal i γβ.1),
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
      exact le_rfl
  have key2 : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T)
      (γβ : (pull_cov X M.rep.Drep T f).J) (c : C.cov.J)
      (p : Spec Rr ⟶ Spec ((pull_cov X M.rep.Drep T f).obj γβ))
      (b : Spec Rr ⟶ Spec (C.cov.obj c)) (g : Spec Rr ⟶ M.dilatation),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧ IsOpenImmersion b ∧
      p ≫ (pull_cov X M.rep.Drep T f).map γβ = emb ∧
      b ≫ C.cov.map c = emb ∧
      g ≫ M.structureMap = emb ≫ f := by
    intro x
    obtain ⟨Rr, emb, hemb, hxe, γβ, c, p, b, hb, hp, hbc⟩ := key x
    haveI := hemb
    haveI := hb
    have hva : emb ≫ f =
        (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)) ≫ M.rep.cov.map γβ.1 := by
      rw [← hp, Category.assoc, pull_cov_map_comp, Category.assoc]
      rfl
    have hpb : b ≫ C.cov.map c = p ≫ (pull_cov X M.rep.Drep T f).map γβ := by
      rw [hbc, hp]
    letI : Algebra (M.rep.cov.obj γβ.1) Γ(Spec Rr, ⊤) :=
      (Spec.preimage ((Spec Rr).isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom.toAlgebra
    obtain ⟨hnzd, hgen⟩ := cond (Spec Rr) inferInstance γβ c p b hb hpb
    refine ⟨Rr, emb, γβ, c, p, b,
      (Spec Rr).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Multicenter.desc (M.rep.localMulticenter γβ.1) hnzd hgen).toRingHom) ≫
        M.rep.chartTo γβ.1, hemb, hxe, hb, hp, hbc, ?_⟩
    show _ ≫ M.rep.structureMap = _
    rw [Category.assoc, Category.assoc, M.rep.structureMap_chart γβ.1]
    show _ ≫ _ ≫ M.rep.chartHom γβ.1 ≫ M.rep.cov.map γβ.1 = _
    rw [show M.rep.chartHom γβ.1 = Spec.map (CommRingCat.ofHom
      (algebraMap (M.rep.cov.obj γβ.1)
        (Multicenter.Dilatation (M.rep.localMulticenter γβ.1)))) from rfl]
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
    rw [show CommRingCat.ofHom (algebraMap (M.rep.cov.obj γβ.1)
        (Multicenter.Dilatation (M.rep.localMulticenter γβ.1))) ≫
        CommRingCat.ofHom (Multicenter.desc (M.rep.localMulticenter γβ.1)
          hnzd hgen).toRingHom =
        Spec.preimage ((Spec Rr).isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ))) from by
      apply CommRingCat.hom_ext
      ext s
      exact (Multicenter.desc (M.rep.localMulticenter γβ.1) hnzd hgen).commutes s]
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]
    exact hva.symm
  choose Rr emb γβ c p b glift hemb hxe hb hp hbc hglift using key2
  have hcompat : ∀ x y : T, pullback.fst (emb x) (emb y) ≫ glift x =
      pullback.snd (emb x) (emb y) ≫ glift y := by
    intro x y
    haveI := hemb x
    haveI := hemb y
    refine (pullback (emb x) (emb y)).affineCover.hom_ext _ _ (fun k => ?_)
    set ι := (pullback (emb x) (emb y)).affineCover.map k with hι
    haveI : IsOpenImmersion (ι ≫ pullback.fst (emb x) (emb y)) := inferInstance
    haveI : IsOpenImmersion (ι ≫ pullback.fst (emb x) (emb y) ≫ b x) := by
      haveI := hb x
      infer_instance
    obtain ⟨hnzd, hgen⟩ := cond
      ((pullback (emb x) (emb y)).affineCover.obj k) inferInstance (γβ x) (c x)
      (ι ≫ pullback.fst (emb x) (emb y) ≫ p x)
      (ι ≫ pullback.fst (emb x) (emb y) ≫ b x) inferInstance
      (by
        simp only [Category.assoc]
        rw [show b x ≫ C.cov.map (c x) =
          p x ≫ (pull_cov X M.rep.Drep T f).map (γβ x) from (hbc x).trans (hp x).symm])
    refine M.rep.local_unique f
      (ι ≫ pullback.fst (emb x) (emb y) ≫ emb x) (γβ x).1 _ ?_ hnzd hgen _ _ ?_ ?_
    · have hstep : emb x ≫ f =
          (p x ≫ Spec.map (pull_mor_ring X M.rep.Drep T f (γβ x))) ≫
            M.rep.cov.map (γβ x).1 := by
        rw [← hp x, Category.assoc, pull_cov_map_comp, Category.assoc]
        rfl
      simp only [Category.assoc]
      rw [hstep]
      simp only [Category.assoc]
    · simp only [Category.assoc]
      rw [show glift x ≫ M.rep.structureMap = emb x ≫ f from hglift x]
    · simp only [Category.assoc]
      rw [show glift y ≫ M.rep.structureMap = emb y ≫ f from hglift y,
        ← Category.assoc (pullback.snd (emb x) (emb y)), ← pullback.condition]
      simp only [Category.assoc]
  let 𝒰 : T.OpenCover :=
    { J := T, obj := fun x => Spec (Rr x), map := emb, f := fun t => t,
      covers := hxe, map_prop := hemb }
  refine ⟨𝒰.glueMorphisms glift hcompat, ?_⟩
  refine 𝒰.hom_ext _ _ (fun x => ?_)
  rw [← Category.assoc, 𝒰.ι_glueMorphisms glift hcompat x]
  exact hglift x

theorem universal_property_unique (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f)
    (u u' : T ⟶ M.dilatation)
    (hu : u ≫ M.structureMap = f) (hu' : u' ≫ M.structureMap = f) :
    u = u' := by
  obtain ⟨C, hCpre, hCeq⟩ := hCars
  rw [show Clos.pullback f M.D =
      Quotient.mk'' (pullback_PreClos X T f M.rep.Drep) from by
    rw [← M.rep_D]; rfl] at hCeq
  obtain ⟨R⟩ := Quotient.exact' hCeq
  have key : ∀ x : T, ∃ (Rr : CommRingCat.{u+1}) (emb : Spec Rr ⟶ T),
      IsOpenImmersion emb ∧ x ∈ Set.range emb.base ∧
      ∃ (γβ : (pull_cov X M.rep.Drep T f).J) (c : C.cov.J)
        (p : Spec Rr ⟶ Spec ((pull_cov X M.rep.Drep T f).obj γβ))
        (b : Spec Rr ⟶ Spec (C.cov.obj c)),
        IsOpenImmersion b ∧
        p ≫ (pull_cov X M.rep.Drep T f).map γβ = emb ∧
        b ≫ C.cov.map c = emb := by
    intro x
    haveI hp1 : IsOpenImmersion ((pull_cov X M.rep.Drep T f).map
      ((pull_cov X M.rep.Drep T f).f x)) := (pull_cov X M.rep.Drep T f).map_prop _
    haveI hp2 : IsOpenImmersion (C.cov.map (C.cov.f x)) := C.cov.map_prop _
    set U : T.Opens :=
      ⟨Set.range ((pull_cov X M.rep.Drep T f).map ((pull_cov X M.rep.Drep T f).f x)).base ∩
        Set.range (C.cov.map (C.cov.f x)).base,
        (hp1.base_open.isOpen_range).inter (hp2.base_open.isOpen_range)⟩ with hU
    have hxU : x ∈ U :=
      ⟨(pull_cov X M.rep.Drep T f).covers x, C.cov.covers x⟩
    obtain ⟨Rr, emb, hemb, hxe, hrange⟩ :=
      AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
    haveI := hemb
    refine ⟨Rr, emb, hemb, hxe, (pull_cov X M.rep.Drep T f).f x, C.cov.f x,
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).1),
      IsOpenImmersion.lift _ emb (fun _ hy => (hrange hy).2), ?_,
      IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩
    haveI : IsOpenImmersion (IsOpenImmersion.lift (C.cov.map (C.cov.f x)) emb
        (fun _ hy => (hrange hy).2) ≫ C.cov.map (C.cov.f x)) := by
      rw [IsOpenImmersion.lift_fac]
      exact hemb
    exact IsOpenImmersion.of_comp _ (C.cov.map (C.cov.f x))
  have cond : ∀ (V : Scheme.{u+1}) (_ : IsAffine V)
      (γβ : (pull_cov X M.rep.Drep T f).J) (c : C.cov.J)
      (p : V ⟶ Spec ((pull_cov X M.rep.Drep T f).obj γβ))
      (b : V ⟶ Spec (C.cov.obj c)) (_ : IsOpenImmersion b)
      (_ : b ≫ C.cov.map c = p ≫ (pull_cov X M.rep.Drep T f).map γβ),
      (∀ i, (Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
          ((M.rep.localMulticenter γβ.1).elem i) ∈ nonZeroDivisors Γ(V, ⊤)) ∧
      (∀ i, Ideal.span {(Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
            ((M.rep.localMulticenter γβ.1).elem i)} =
          Ideal.map (Spec.preimage (V.isoSpec.inv ≫
            (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom
            ((M.rep.localMulticenter γβ.1).LargeIdeal i)) := by
    intro V hV γβ c p b hb hpb
    haveI := hV
    haveI := hb
    have hbridge : Spec.preimage (V.isoSpec.inv ≫
          (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ))) =
        pull_mor_ring X M.rep.Drep T f γβ ≫
          Spec.preimage (V.isoSpec.inv ≫ p) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
    letI : Algebra (M.rep.cov.obj γβ.1) Γ(V, ⊤) :=
      (Spec.preimage (V.isoSpec.inv ≫
        (p ≫ Spec.map (pull_mor_ring X M.rep.Drep T f γβ)))).hom.toAlgebra
    refine ⟨fun i => ?_, ?_⟩
    · rw [hbridge]
      exact M.rep.elem_nonzerodiv f C hCpre R γβ c p b hpb i
    · refine M.rep.largeIdeal_collapse γβ.1 _ (fun i => ?_)
      letI := M.rep.Dprin i γβ.1
      letI : Submodule.IsPrincipal (M.rep.Drep.ideal i γβ.1) := M.rep.Dprin i γβ.1
      have hY := hsub M.rep M.rep_eq i γβ
      rw [hbridge, CommRingCat.hom_comp, ← Ideal.map_map]
      refine le_trans (Ideal.map_mono hY) ?_
      show Ideal.map _ (Ideal.map (pull_mor_ring X M.rep.Drep T f γβ).hom
        (M.rep.Drep.ideal i γβ.1)) ≤ _
      rw [← Ideal.span_singleton_generator (M.rep.Drep.ideal i γβ.1),
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
      exact le_rfl
  choose Rr emb hemb hxe γβ c p b hb hp hbc using key
  let 𝒰 : T.OpenCover :=
    { J := T, obj := fun x => Spec (Rr x), map := emb, f := fun t => t,
      covers := hxe, map_prop := hemb }
  refine 𝒰.hom_ext u u' (fun x => ?_)
  haveI := hemb x
  haveI := hb x
  obtain ⟨hnzd, hgen⟩ := cond (Spec (Rr x)) inferInstance (γβ x) (c x) (p x) (b x)
    (hb x) (by rw [hbc x, ← hp x])
  refine M.rep.local_unique f (emb x) (γβ x).1 _ ?_ hnzd hgen _ _ ?_ ?_
  · rw [← hp x, Category.assoc, pull_cov_map_comp, Category.assoc]
    rfl
  · rw [Category.assoc, show u ≫ M.rep.structureMap = f from hu]
  · rw [Category.assoc, show u' ≫ M.rep.structureMap = f from hu']

theorem universal_property (T : Scheme.{u+1}) (f : T ⟶ X)
    (hCars : IsCars T (Clos.pullback f M.D))
    (hsub : M.pullSubset f) :
    ∃! g : T ⟶ M.dilatation, g ≫ M.structureMap = f := by
  obtain ⟨g, hg⟩ := M.universal_property_exists T f hCars hsub
  exact ⟨g, hg, fun g' hg' => M.universal_property_unique T f hCars hsub g' g hg' hg⟩

instance dilatationOver (M : MultiCenter X) : (M.dilatation).Over X := ⟨M.structureMap⟩

theorem universal_property_over (M : MultiCenter X) (T : Scheme.{u+1}) [T.Over X]
    (hCars : IsCars T (Clos.pullback (T ↘ X) M.D))
    (hsub : M.pullSubset (T ↘ X)) :
    ∃! g : T ⟶ M.dilatation, Scheme.Hom.IsOver g X := by
  obtain ⟨g, hg, huniq⟩ := M.universal_property T (T ↘ X) hCars hsub
  exact ⟨g, ⟨hg⟩, fun g' hg' => huniq g' hg'.1⟩
