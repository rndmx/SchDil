import Project.Dilatation.Multicenter
import Mathlib.Data.Sum.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Project.Dilatation.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dilatation.lemma
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Basic
import Project.Dilatation.Family
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Project.HomogeneousSubmonoid.Basic
import Project.ForMathlib.TensorProduct
import Project.Proj.Over
import Project.Proj.OfLE
import Project.Dilatation.Multicenter
import Mathlib.Topology.Sets.Closeds
import Mathlib.AlgebraicGeometry.PullbackCarrier

import Project.ForMathlib.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.RingTheory.RingHom.Flat

import Project.Blowups.PreClosAndClos
import Project.Blowups.Bl

suppress_compilation

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {ι : Type} [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]
variable {X : Scheme.{u+1}}

structure conceptual_blowup (Z : Clos X) where
  scheme : Scheme
  over : Scheme.Over scheme X
  in_cars : pullback_Clos (scheme ↘ X) Z ∈ CarsAsSubsetOfClos scheme
  φ (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    T ⟶ scheme
  φ_over (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    Scheme.Hom.IsOver (φ T in_preCars) X
  φ_uniq (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    ∀ φ' : T ⟶ scheme, Scheme.Hom.IsOver φ' X → φ' = φ T in_preCars

def singletonCovering (A: CommRingCat) :
    Scheme.AffineCover IsOpenImmersion (Spec A) where
  J := PUnit
  obj _ := A
  map _ := 𝟙 _
  f _ := .unit
  covers := by simp
  map_prop _ := inferInstance

def loc_to_PreClos (A: CommRingCat) (L : ι → Ideal A) : PreClos (Spec A) where
  indnumb := ι
  subscheme i := Spec (CommRingCat.of <| A ⧸ L i)
  over i :=
  { hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk (L i) }
  cov := singletonCovering A
  ideal i _ := L i
  condiso i _ :=
    ⟨Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i))),
      Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i)).symm),
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        ext x
        exact (Algebra.TensorProduct.rid A A (A ⧸ L i)).apply_symm_apply x),
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        ext x
        exact (Algebra.TensorProduct.rid A A (A ⧸ L i)).symm_apply_apply x)⟩ ≪≫
        (AlgebraicGeometry.pullbackSpecIso A (A ⧸ L i) A).symm ≪≫ pullback.congrHom rfl (Spec.map_id _)
  condover i _ := by
    rw [Scheme.Hom.isOver_iff]
    simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom]
    erw [pullback.lift_snd]
    rw [Category.comp_id]
    erw [pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
    ext a
    simp [Algebra.smul_def]

def loc_to_Clos (A: CommRingCat) (L : ι → Ideal A) : Clos (Spec A) :=
  Quotient.mk' (loc_to_PreClos A L)

instance (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

instance (X Y : Scheme) [Scheme.Over X Y]
  (O : Opens X) : (X.restrict O.isOpenEmbedding).Over Y where
    hom := X.ofRestrict .. ≫ X ↘ Y

def loc_to_PreClos_baseChange (A R : CommRingCat) [Algebra A R] (L : ι → Ideal A) :
    relStructure (loc_to_PreClos R (fun i => Ideal.map (algebraMap A R) (L i)))
      (pullback_PreClos (Spec A) (Spec R) (Spec R ↘ Spec A) (loc_to_PreClos A L)) where
  indnumb_equiv := Equiv.refl ι
  subscheme_iso i :=
    { hom := Spec.map (CommRingCat.ofHom (lemma_iso A R (L i)).symm.toRingHom)
      inv := Spec.map (CommRingCat.ofHom (lemma_iso A R (L i)).toRingHom)
      hom_inv_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        exact RingHom.ext fun x => (lemma_iso A R (L i)).symm_apply_apply x
      inv_hom_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        exact RingHom.ext fun x => (lemma_iso A R (L i)).apply_symm_apply x } ≪≫
      (AlgebraicGeometry.pullbackSpecIso A (A ⧸ L i) R).symm
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom]
    erw [pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
    ext a

    show (lemma_iso A R (L i)).symm (1 ⊗ₜ[A] a) = _
    rw [AlgEquiv.symm_apply_eq]
    simp [lemma_iso]

lemma ideal_eq_of_specQuot_iso (B : CommRingCat.{u+1}) (I J : Ideal B)
    (e : Spec (CommRingCat.of (B ⧸ I)) ≅ Spec (CommRingCat.of (B ⧸ J)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : I = J := by
  have he' : e.inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have key : ∀ (f : Spec (CommRingCat.of (B ⧸ I)) ⟶ Spec (CommRingCat.of (B ⧸ J))),
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) →
      ∀ b : B, (Spec.preimage f) (Ideal.Quotient.mk J b) = Ideal.Quotient.mk I b := by
    intro f hf b
    have : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ Spec.preimage f =
        CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hf
    exact congrArg (fun g => CommRingCat.Hom.hom g b) this
  have key' : ∀ (f : Spec (CommRingCat.of (B ⧸ J)) ⟶ Spec (CommRingCat.of (B ⧸ I))),
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
      ∀ b : B, (Spec.preimage f) (Ideal.Quotient.mk I b) = Ideal.Quotient.mk J b := by
    intro f hf b
    have : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage f =
        CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hf
    exact congrArg (fun g => CommRingCat.Hom.hom g b) this
  refine le_antisymm (fun b hb => ?_) (fun b hb => ?_)
  · have h0 : Ideal.Quotient.mk I b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [← key' e.inv he' b, h0, map_zero]
  · have h0 : Ideal.Quotient.mk J b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [← key e.hom he b, h0, map_zero]

lemma loc_to_PreClos_isPreCars (R : CommRingCat) (M : ι → Ideal R) (g : ι → R)
    (hg : ∀ i, M i = Ideal.span {g i}) (hnzd : ∀ i, g i ∈ nonZeroDivisors R) :
    IsPreCars (Spec R) (loc_to_PreClos R M) := by
  have hprin : ∀ i (γ : (loc_to_PreClos R M).cov.J),
      ((loc_to_PreClos R M).ideal i γ).IsPrincipal := fun i _ => ⟨⟨g i, hg i⟩⟩
  refine ⟨⟨hprin⟩, ?_⟩
  intro i γ
  haveI := hprin i γ
  have hmem : g i ∈
      Ideal.span {Submodule.IsPrincipal.generator ((loc_to_PreClos R M).ideal i γ)} := by
    rw [Ideal.span_singleton_generator]
    show g i ∈ M i
    rw [hg i]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine (mul_mem_nonZeroDivisors.1 (?_ : v * _ ∈ nonZeroDivisors _)).2
  rw [hv]
  exact hnzd i

lemma loc_isCars_of_principal (A R : CommRingCat) [Algebra A R] (L : ι → Ideal A) (g : ι → R)
    (hg : ∀ i, Ideal.map (algebraMap A R) (L i) = Ideal.span {g i})
    (hnzd : ∀ i, g i ∈ nonZeroDivisors R) :
    IsCars (Spec R) (pullback_Clos (Spec R ↘ Spec A) (loc_to_Clos A L)) :=
  ⟨⟨loc_to_PreClos R (fun i => Ideal.map (algebraMap A R) (L i)),
    loc_to_PreClos_isPreCars R _ g hg hnzd,
    Quotient.sound ⟨loc_to_PreClos_baseChange A R L⟩⟩⟩

lemma PreClos_ideal_eq_of_rel (A : CommRingCat.{u+1}) (L : ι → Ideal A)
    {T : Scheme} [T.Over (Spec A)]
    (Z : PreClos T)
    (r : relStructure Z (pullback_PreClos (Spec A) T (T ↘ Spec A) (loc_to_PreClos A L)))
    (γ : Z.cov.J) (j : Z.indnumb) [Algebra A (Z.cov.obj γ)]
    (halg : Z.cov.map γ ≫ (T ↘ Spec A) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Z.cov.obj γ)))) :
    Z.ideal j γ =
      Ideal.map (algebraMap A (Z.cov.obj γ)) (L (r.indnumb_equiv j)) := by
  set i := r.indnumb_equiv j with hi

  let e2 : pullback (Z.subscheme j ↘ T) (Z.cov.map γ) ≅
      pullback ((pullback_PreClos (Spec A) T (T ↘ Spec A) (loc_to_PreClos A L)).subscheme i ↘ T)
        (Z.cov.map γ) :=
  { hom := pullback.map _ _ _ _ (r.subscheme_iso j).hom (𝟙 _) (𝟙 _) (by
      simp only [Category.comp_id]
      have := r.subscheme_iso_over j
      simp only [comp_over]) (by simp)
    inv := pullback.map _ _ _ _ (r.subscheme_iso j).inv (𝟙 _) (𝟙 _) (by
      simp only [Category.comp_id]
      have := r.subscheme_iso_over j
      rw [Scheme.Hom.isOver_iff] at this
      rw [← this]
      simp only [Iso.inv_hom_id_assoc]
      rfl) (by simp)
    hom_inv_id := by rw [pullback.map_comp]; simp only [Iso.hom_inv_id, Category.comp_id,
      pullback.map_id]
    inv_hom_id := by rw [pullback.map_comp]; simp only [Iso.inv_hom_id, Category.comp_id,
      pullback.map_id] }
  refine ideal_eq_of_specQuot_iso (Z.cov.obj γ) _ _
    (Z.condiso j γ ≪≫ e2 ≪≫
      pullbackLeftPullbackSndIso ((loc_to_PreClos A L).subscheme i ↘ Spec A) (T ↘ Spec A)
        (Z.cov.map γ) ≪≫
      pullback.congrHom rfl halg ≪≫
      ((loc_to_PreClos_baseChange A (Z.cov.obj γ) L).subscheme_iso i).symm) ?_
  have h5 : ((loc_to_PreClos_baseChange A (Z.cov.obj γ) L).subscheme_iso i).hom ≫
      pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap A (Z.cov.obj γ)) (L i)))) :=
    ((loc_to_PreClos_baseChange A (Z.cov.obj γ) L).subscheme_iso_over i).comp_over
  have h5' : ((loc_to_PreClos_baseChange A (Z.cov.obj γ) L).subscheme_iso i).inv ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap A (Z.cov.obj γ)) (L i)))) = pullback.snd _ _ := by
    rw [← h5, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h1 : (Z.condiso j γ).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal j γ))) :=
    (Z.condover j γ).comp_over
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, h5', e2, pullback.congrHom_hom]

  erw [pullback.lift_snd]
  simp only [Category.comp_id]
  rw [pullbackLeftPullbackSndIso_hom_snd]
  erw [pullback.lift_snd]
  simp only [Category.comp_id]
  exact h1

open GoodPotionIngredient HomogeneousSubmonoid
set_option maxHeartbeats 3200000 in
theorem ProjBlowup_UnivProp_unicity_affine
  (A: CommRingCat.{u+1}) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : IsCars _ (pullback_Clos (T ↘ Spec A) (loc_to_Clos A L)))

  (φ φ' : T ⟶ BlMu L)
  (φ_over : Scheme.Hom.IsOver φ (Spec A))
  (φ'_over : Scheme.Hom.IsOver φ' (Spec A)) : φ = φ' := by
  obtain ⟨Z, hZ, eq⟩ := cond
  change Quotient.mk'' _ = Quotient.mk'' _ at eq
  rw [Quotient.eq''] at eq
  obtain ⟨eq⟩ := eq
  let O (P P' : Mu L) (x : T) :
    Opens T :=
    ⟨(φ.base ⁻¹' (((glueData (τ := Mu L) (map_index L)).ι P).opensRange).1) ∩
      (φ'.base ⁻¹' (((glueData (τ := Mu L) (map_index L)).ι P').opensRange).1) ∩
        (Z.cov.map <| Z.cov.f x).opensRange.1,
        IsOpen.inter (IsOpen.inter
          (by
            apply Continuous.isOpen_preimage
            · continuity
            · exact (Scheme.Hom.opensRange ((glueData (map_index L)).ι P)).is_open')
          (by
            apply Continuous.isOpen_preimage
            · continuity
            · exact (Scheme.Hom.opensRange ((glueData (map_index L)).ι P')).is_open'))
          ((Scheme.Hom.opensRange _).is_open')⟩

  let S (P P' : Mu L) (x : T) : Scheme := T.restrict (O P P' x).isOpenEmbedding

  let SToSpecP (P P' : Mu L) (x : T) : S P P' x ⟶
    Spec (CommRingCat.of <| (map_index L P).Potion) :=
    IsOpenImmersion.lift ((glueData (map_index L)).ι P) (T.ofRestrict .. ≫ φ)
      (by
        rintro _ ⟨⟨z, ⟨⟨⟨y, hy1⟩, mem2⟩, mem3⟩⟩, rfl⟩
        simp only [Scheme.comp_coeBase, Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp,
          ContinuousMap.comp_apply, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  letI isOver₀ (P P' : Mu L) (x : T) :
      (Spec (CommRingCat.of (map_index L P).Potion)).Over (Spec A) :=
    { hom := (glueData (τ := Mu L) (map_index L)).ι P ≫ (BlMu L) ↘ Spec A  }

  have isOverA₀_eq (P P' : Mu L) (x : T) :
      SToSpecP P P' x ≫ ((glueData (τ := Mu L) (map_index L)).ι P ≫ (BlMu L) ↘ Spec A) =
        (S P P' x) ↘ Spec A := by
    simp only [SToSpecP]
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, φ_over.comp_over]
    rfl

  have isOverA₀ (P P' : Mu L) (x : T) :
    @Scheme.Hom.IsOver _ _ (SToSpecP P P' x) (Spec A) inferInstance (isOver₀ P P' x) := by
    letI := isOver₀ P P' x
    exact ⟨isOverA₀_eq P P' x⟩

  let SToSpecP' (P P' : Mu L) (x) : S P P' x ⟶ Spec (CommRingCat.of <| (map_index L P').Potion) :=
    IsOpenImmersion.lift ((glueData (map_index L)).ι P') (T.ofRestrict .. ≫ φ')
      (by
        rintro _ ⟨⟨z, ⟨⟨mem1, ⟨y, hy1⟩⟩, mem3⟩⟩, rfl⟩
        simp only [Scheme.comp_coeBase, Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp,
          ContinuousMap.comp_apply, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  let SToSpecRx (P P' : Mu L) (x) :
      S P P' x ⟶
      Spec (Z.cov.obj <| Z.cov.f x) :=
    IsOpenImmersion.lift (Z.cov.map _) (T.ofRestrict ..)
      (by
        rintro _ ⟨⟨z, ⟨⟨mem1, mem2⟩, ⟨y, hy1⟩⟩⟩, rfl⟩
        simp only [Scheme.ofRestrict_toLRSHom_base, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  have key (x : T) :
    ∃ (P P' : Mu L) (B : CommRingCat) (_ : Algebra A B)
      (i : Spec B ⟶
        T.restrict (O P P' x).isOpenEmbedding),
      IsOpenImmersion i ∧
      Scheme.Hom.IsOver i (Spec A) ∧
      x ∈ Set.range ((i ≫ T.ofRestrict ..).base) ∧
      i ≫ T.ofRestrict _ ≫ φ = i ≫ T.ofRestrict _ ≫ φ' := by
    let y := φ.base x
    let y' := φ'.base x
    have  ⟨(P : Mu L), (Y : Spec <| _), hY⟩ := (glueData <| map_index L).ι_jointly_surjective y
    have  ⟨(P' : Mu L), (Y' : Spec <| _), hY'⟩ := (glueData <| map_index L).ι_jointly_surjective y'

    have x_in_inter : x ∈ O P P' x := ⟨⟨⟨Y, hY⟩, ⟨Y', hY'⟩⟩, Z.cov.covers x⟩

    let γ := Z.cov.f x
    let Rx : CommRingCat := Z.cov.obj γ
    let SpecRxOverT : Scheme.Over (Spec Rx) T :=
      { hom := Z.cov.map γ }
    let SpecRxOverSpecA : Scheme.Over (Spec Rx) (Spec A) :=
      { hom := Spec Rx ↘ T ≫ T ↘ Spec A}

    let x' : S P P' x := ⟨x, x_in_inter⟩
    obtain ⟨U, B, ⟨isoB : _⟩⟩ := (S P P' x).local_affine ⟨x, x_in_inter⟩

    let F : Spec B ⟶ Spec A := ⟨isoB.inv⟩ ≫ (S P P' x).restrict U.isOpenEmbedding ↘ Spec A
    let f : A ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ F.app _ ≫ (Scheme.ΓSpecIso _).hom
    let alg : Algebra A B := RingHom.toAlgebra f.hom

    have specB_over_specA_eq : Spec B ↘ Spec A = F := by
      change Spec.map (_ ≫ _ ≫ _) = _ ≫ _
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        Spec.toLocallyRingedSpace_obj]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let specBToSpecP : Spec B ⟶ Spec (CommRingCat.of <| (map_index L P).Potion) :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecP P P' x

    let specBToSpecP' : Spec B ⟶ Spec (CommRingCat.of <| (map_index L P').Potion) :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecP' P P' x

    let specBToSpecRx : Spec B ⟶ Spec Rx :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecRx P P' x

    haveI oi1 : IsOpenImmersion specBToSpecRx := by
      apply IsOpenImmersion.comp

    haveI flat1 : Flat specBToSpecRx := inferInstance

    let PToB : CommRingCat.of (map_index L P).Potion ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecP.app _ ≫ (Scheme.ΓSpecIso _).hom

    have PToB_def' : Spec.map PToB = specBToSpecP := by
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc, PToB]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let RxToB : Rx ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecRx.app _ ≫ (Scheme.ΓSpecIso _).hom

    letI alg2 : Algebra A (map_index L P).Potion :=
      instAlgebraPotionFinsuppIntReesAlgebraClo_mu _ _

    letI alg2' : Algebra A (map_index L P').Potion :=
      instAlgebraPotionFinsuppIntReesAlgebraClo_mu _ _

    letI alg3 : Algebra Rx B :=
      RingHom.toAlgebra <| RxToB.hom

    let P'ToB : CommRingCat.of (map_index L P').Potion ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecP'.app _ ≫ (Scheme.ΓSpecIso _).hom

    have P'ToB_def' : Spec.map P'ToB = specBToSpecP' := by
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc, P'ToB]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let RxToB : Rx ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecRx.app _ ≫ (Scheme.ΓSpecIso _).hom
    let AToRx : A ⟶ Rx :=
      (Scheme.ΓSpecIso _).inv ≫ (_ ↘ Spec A).app _ ≫ (Scheme.ΓSpecIso _).hom

    have RxToB_def' : Spec.map RxToB = specBToSpecRx := by
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        Spec.toLocallyRingedSpace_obj, RxToB]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    have AToRx_def' : Spec.map AToRx = (Spec Rx ↘ Spec A) := by
      change Spec.map (_ ≫ _ ≫ _) = _ ≫ _
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        Spec.toLocallyRingedSpace_obj]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    have hPA : PToB.hom.comp (algebraMap A ((map_index L P).Potion)) = algebraMap A B := by
      have h : CommRingCat.ofHom (algebraMap A ((map_index L P).Potion)) ≫ PToB =
          CommRingCat.ofHom (algebraMap A B) := by
        apply Spec.map_injective
        rw [Spec.map_comp, PToB_def', ← BlMu_ι_over A L P]
        show _ = Spec B ↘ Spec A
        rw [specB_over_specA_eq]
        simp only [specBToSpecP, SToSpecP, Category.assoc]
        rw [← Category.assoc (IsOpenImmersion.lift _ _ _), IsOpenImmersion.lift_fac]
        simp only [Category.assoc]
        rw [φ_over.comp_over]
        rfl
      have := congrArg CommRingCat.Hom.hom h
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this
      exact this

    have hP'A : P'ToB.hom.comp (algebraMap A ((map_index L P').Potion)) = algebraMap A B := by
      have h : CommRingCat.ofHom (algebraMap A ((map_index L P').Potion)) ≫ P'ToB =
          CommRingCat.ofHom (algebraMap A B) := by
        apply Spec.map_injective
        rw [Spec.map_comp, P'ToB_def', ← BlMu_ι_over A L P']
        show _ = Spec B ↘ Spec A
        rw [specB_over_specA_eq]
        simp only [specBToSpecP', SToSpecP', Category.assoc]
        rw [← Category.assoc (IsOpenImmersion.lift _ _ _), IsOpenImmersion.lift_fac]
        simp only [Category.assoc]
        rw [φ'_over.comp_over]
        rfl
      have := congrArg CommRingCat.Hom.hom h
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this
      exact this

    have hRxA : (Spec Rx ↘ Spec A) = Z.cov.map γ ≫ (T ↘ Spec A) := rfl
    have hfac : algebraMap A B = RingHom.comp RxToB.hom AToRx.hom := by
      have hlift : SToSpecRx P P' x ≫ Z.cov.map γ = T.ofRestrict _ :=
        IsOpenImmersion.lift_fac _ _ _
      have hF : Spec.map (CommRingCat.ofHom (algebraMap A B)) = F := specB_over_specA_eq
      have h : AToRx ≫ RxToB = CommRingCat.ofHom (algebraMap A B) := by
        apply Spec.map_injective
        rw [Spec.map_comp, RxToB_def', AToRx_def', hRxA, hF]
        have expand : specBToSpecRx = Scheme.Hom.mk isoB.inv ≫
            (S P P' x).ofRestrict _ ≫ SToSpecRx P P' x := rfl
        rw [expand]
        simp only [Category.assoc]
        rw [reassoc_of% hlift]
        rfl
      have := congrArg CommRingCat.Hom.hom h
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
      exact this.symm

    refine ⟨P, P', B, inferInstance, (⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict ..), inferInstance, ?_,
      ?_, ?_⟩
    · rw [Scheme.Hom.isOver_iff, Category.assoc, specB_over_specA_eq]
      rfl
    · simp only [Spec.toLocallyRingedSpace_obj, Category.assoc, Scheme.comp_coeBase,
      Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp, ContinuousMap.comp_assoc,
      ContinuousMap.coe_comp, Set.mem_range, Function.comp_apply]
      refine ⟨isoB.hom.base ⟨⟨x, x_in_inter⟩, U.2⟩, ?_⟩
      erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply]
      rw [← Category.assoc]
      change ((isoB.hom ≫ isoB.inv).base ≫ _) _ = x
      rw [Iso.hom_inv_id]
      rfl
    ·
      have nonzerodiv (i : ι) := hZ.nonzerodiv (eq.indnumb_equiv.symm i) γ
      have prin (i : ι) := hZ.prin (eq.indnumb_equiv.symm i) γ

      obtain ⟨g'', ⟨g''_comp_eq, g''_comp_eq'⟩, g''_uniq⟩ := lemm_dila_double_union L P P' (B := B)
        (fun i => ⟨RxToB.hom <| Submodule.IsPrincipal.generator (Z.ideal (eq.indnumb_equiv.symm i) γ),
            by
              apply RingHom.Flat.preserves_nonzeroDivisors
              · have flat2 := flat1.flat_of_affine_subset ⟨⊤, isAffineOpen_top _⟩
                  ⟨⊤, isAffineOpen_top _⟩ (by intro x hx; simp)
                simp only at flat2
                simp only [Opens.map_top, CommRingCat.hom_comp, RxToB, Rx]
                refine RingHom.Flat.comp ?_ (RingHom.Flat.comp flat2 ?_) <;>
                · apply RingHom.Flat.of_bijective
                  exact ConcreteCategory.bijective_of_isIso _
              · apply nonzerodiv⟩)
        (g := AlgHom.comp
            { toRingHom := PToB.hom
              commutes' := fun a => RingHom.congr_fun hPA a }
            (Mu_mor_iso L P).toAlgHom)
        (g' := AlgHom.comp
            { toRingHom := P'ToB.hom
              commutes' := fun a => RingHom.congr_fun hP'A a }
            (Mu_mor_iso L P').toAlgHom)
        (cond1 := by
          intro i
          dsimp
          have eq0 : Ideal.map AToRx.hom (L i) =
            (Ideal.span
              {Submodule.IsPrincipal.generator
                (Z.ideal (eq.indnumb_equiv.symm i) γ)}) := by
            haveI := prin i
            rw [Ideal.span_singleton_generator]
            letI algARx : Algebra A Rx := RingHom.toAlgebra AToRx.hom
            have halg : Z.cov.map γ ≫ (T ↘ Spec A) =
                Spec.map (CommRingCat.ofHom (algebraMap A Rx)) := by
              rw [show CommRingCat.ofHom (algebraMap A Rx) = AToRx from
                CommRingCat.ofHom_hom _, AToRx_def']
              rfl
            have h := PreClos_ideal_eq_of_rel A L Z eq γ (eq.indnumb_equiv.symm i) halg
            rw [Equiv.apply_symm_apply] at h
            exact h.symm
          rw [hfac]
          rw [← Ideal.map_map, eq0, Ideal.map_span, Set.image_singleton])
        (cond2 := by simp)
        (cond2' := by simp)

      exact calc Scheme.Hom.mk isoB.inv ≫ (S P P' x).ofRestrict _ ≫ T.ofRestrict _ ≫ φ
          _ = specBToSpecP ≫ (glueData (map_index L)).ι _ := by
            simp [specBToSpecP, SToSpecP]
          _ =
            (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
            (Spec.map (CommRingCat.ofHom <| potionMapOfLE _ _ (clo_mu_union_Mu_left L P P')) :
                  Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion) ⟶
                  Spec (CommRingCat.of <| (map_index L P).Potion)) ≫
            (glueData (map_index L)).ι _ := by
            simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
              AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
              Spec.map_comp, ← Category.assoc]
            congr 1
            simp only [Spec.toLocallyRingedSpace_obj, ← Spec.map_comp, specBToSpecP, SToSpecP]
            rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
            have : PToB.hom.comp _  = g''.toRingHom.comp (dilationToUnion_left _ _ _).toRingHom :=
              congr($(g''_comp_eq).toRingHom)
            rw [Mu_mor_iso_commutes_ringHom', ← RingHom.comp_assoc, ← RingHom.comp_assoc] at this
            simp only [AlgEquiv.toAlgHom_eq_coe, AlgHomClass.toRingHom_toAlgHom,
              AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] at this
            erw [RingEquiv.comp_cancel] at this
            erw [← this]
            erw [PToB_def']
          _ = (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
              (glueData (map_index L)).ι _ := by
              rw [proj_glue_condition (ℱ := map_index L) P (union_Mu L P P')
                (clo_mu_union_Mu_left L P P')]
          _ = (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
            (Spec.map (CommRingCat.ofHom <| potionMapOfLE _ _ (clo_mu_union_Mu_right L P P')) :
                  Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion) ⟶
                  Spec (CommRingCat.of <| (map_index L P').Potion)) ≫
            (glueData (map_index L)).ι _ := by
            have := proj_glue_condition (ℱ := map_index L) P' (union_Mu L P P')
              (clo_mu_union_Mu_right L P P')
            rw [this]
          _ = specBToSpecP' ≫ (glueData (map_index L)).ι _ := by
            simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
              AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
              Spec.map_comp, ← Category.assoc]
            congr 1
            simp only [← Spec.map_comp]
            rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
            have : P'ToB.hom.comp _  = g''.toRingHom.comp (dilationToUnion_right _ _ _).toRingHom :=
              congr($(g''_comp_eq').toRingHom)
            rw [Mu_mor_iso_commutes_ringHom_right', ← RingHom.comp_assoc, ← RingHom.comp_assoc] at this
            simp only [AlgEquiv.toAlgHom_eq_coe, AlgHomClass.toRingHom_toAlgHom,
              AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] at this
            erw [RingEquiv.comp_cancel] at this
            erw [← this]
            erw [P'ToB_def']
          _ = Scheme.Hom.mk isoB.inv ≫ (S P P' x).ofRestrict _ ≫ T.ofRestrict _ ≫ φ' := by
            simp [specBToSpecP', SToSpecP']

  have : (∀ x : T,
    ∃ (P P' : Mu L) (B : CommRingCat) (_ : Algebra A B)
      (i : Spec B ⟶ T.restrict (O P P' x).isOpenEmbedding),
      IsOpenImmersion i ∧
      Scheme.Hom.IsOver i (Spec A) ∧
      x ∈ Set.range ((i ≫ T.ofRestrict ..).base) ∧
      (i ≫ T.ofRestrict _ ≫ φ = i ≫ T.ofRestrict _ ≫ φ')) → φ = φ' := by

      intro H
      refine Scheme.hom_ext_of_forall φ φ' (fun x => ?_)
      obtain ⟨P, P', B, _, i, o_i, -, hx, hcomp⟩ := H x
      haveI : IsOpenImmersion i := o_i
      let j : Spec B ⟶ T := i ≫ T.ofRestrict (O P P' x).isOpenEmbedding
      haveI : IsOpenImmersion j := IsOpenImmersion.comp _ _
      refine ⟨j.opensRange, hx, ?_⟩
      have hι : j.opensRange.ι = j.isoOpensRange.inv ≫ j := (j.isoOpensRange_inv_comp).symm
      rw [hι]
      simp only [j, Category.assoc]
      rw [hcomp]
  exact this key
