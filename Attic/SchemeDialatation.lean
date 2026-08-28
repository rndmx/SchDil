import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.TensorProduct.Basic
import MulticenterRing
import PreClosAndClos
import PreClosClosedImmersion
import PreMultiCenter
import MultiCenter

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

lemma RingEquiv.mem_nonZeroDivisors_map {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {a : R} (ha : a ∈ nonZeroDivisors R) : e a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * e a = 0 → x = 0 := by
    intro x hx
    have h := congrArg e.symm hx
    rw [map_mul, e.symm_apply_apply, map_zero] at h
    have := (mem_nonZeroDivisors_iff.1 ha).2 _ h
    simpa using congrArg e this
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

lemma nonzerodiv_baseChange (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B]
    (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) (i : F.index) :
    (algebraMap A[F] (A[F] ⊗[A] B)) ((algebraMap A A[F]) (F.elem i)) ∈
      nonZeroDivisors (A[F] ⊗[A] B) := by
  haveI : Module.Flat A B := flat_algebraMap_iff.mp flat
  haveI : Module.Flat A[F] (A[F] ⊗[A] B) := inferInstance
  refine (flat_algebraMap_iff.mpr inferInstance).preserves_nonzeroDivisors ?_
  have h := Multicenter.Dilatation.nonzerodiv_image (F := F) (Finsupp.single i 1)
  rw [familyPow_single] at h
  exact h

lemma span_baseChange (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B]
    (F : Multicenter A) (i : F.index) :
    Ideal.span {(algebraMap A (A[F] ⊗[A] B)) (F.elem i)} =
      Ideal.map (algebraMap A (A[F] ⊗[A] B)) (F.LargeIdeal i) := by
  have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal (F := F) (Finsupp.single i 1)
  rw [familyPow_single, familyPow_single] at h
  have h2 := congrArg (Ideal.map (algebraMap A[F] (A[F] ⊗[A] B))) h
  rwa [Ideal.map_span, Set.image_singleton, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply] at h2

lemma span_baseChange' (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B]
    (F : Multicenter A) (i : F.index) :
    Ideal.span {(algebraMap A (B ⊗[A] A[F])) (F.elem i)} =
      Ideal.map (algebraMap A (B ⊗[A] A[F])) (F.LargeIdeal i) := by
  have hAlg : (Algebra.TensorProduct.includeRight :
        A[F] →ₐ[A] B ⊗[A] A[F]).toRingHom.comp (algebraMap A A[F]) =
      algebraMap A (B ⊗[A] A[F]) :=
    (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]).comp_algebraMap
  have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal (F := F) (Finsupp.single i 1)
  rw [familyPow_single, familyPow_single] at h
  have h2 := congrArg (Ideal.map
    (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]).toRingHom) h
  rwa [Ideal.map_span, Set.image_singleton, Ideal.map_map, hAlg,
    show (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]).toRingHom
        ((algebraMap A A[F]) (F.elem i)) = (algebraMap A (B ⊗[A] A[F])) (F.elem i) from
      (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]).commutes (F.elem i)] at h2

lemma nonzerodiv_baseChange' (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B]
    (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) (i : F.index) :
    (algebraMap A (B ⊗[A] A[F])) (F.elem i) ∈ nonZeroDivisors (B ⊗[A] A[F]) := by
  have h := nonzerodiv_baseChange A B F flat i
  rw [← IsScalarTower.algebraMap_apply] at h
  have h2 := RingEquiv.mem_nonZeroDivisors_map
    (Algebra.TensorProduct.comm A A[F] B).toRingEquiv h
  have hc : (Algebra.TensorProduct.comm A A[F] B).toRingEquiv
      ((algebraMap A (A[F] ⊗[A] B)) (F.elem i)) =
      (algebraMap A (B ⊗[A] A[F])) (F.elem i) :=
    (Algebra.TensorProduct.comm A A[F] B).commutes _
  rwa [hc] at h2

noncomputable def dilatation_baseChange_inv (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Algebra A B] (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) :
    B[image_mult (B := B) F] →ₐ[B] (B ⊗[A] A[F]) :=
  Multicenter.desc (image_mult (B := B) F)
    (by
      intro i
      have h := nonzerodiv_baseChange' A B F flat i
      rwa [IsScalarTower.algebraMap_apply A B (B ⊗[A] A[F])] at h)
    (by
      intro i
      have h := span_baseChange' A B F i
      rw [IsScalarTower.algebraMap_apply A B (B ⊗[A] A[F])] at h
      rw [image_mult_elem, image_mult_LargeIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
      exact h)

noncomputable def dilatation_baseChange_hom (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Algebra A B] (F : Multicenter A) :
    (B ⊗[A] A[F]) →ₐ[B] B[image_mult (B := B) F] :=
  letI : IsScalarTower A B (B[image_mult (B := B) F]) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId B _) (Multicenter.functo_dila_alg F)
    (fun _ _ => Commute.all _ _)

lemma dilatation_baseChange_inv_functo (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Algebra A B] (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) (a : A[F]) :
    dilatation_baseChange_inv A B F flat (Multicenter.functo_dila_alg F a) =
      (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]) a := by
  letI : IsScalarTower A B (B[image_mult (B := B) F]) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ((dilatation_baseChange_inv A B F flat).restrictScalars A).comp
      (Multicenter.functo_dila_alg F) =
      (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F]) :=
    Multicenter.lemma_exists_unique_morphism' F
      (fun i => nonzerodiv_baseChange' A B F flat i)
      (fun i => span_baseChange' A B F i) _ _
  exact AlgHom.congr_fun key a

noncomputable def dilatation_baseChange_equiv (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Algebra A B] (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) :
    (B ⊗[A] A[F]) ≃ₐ[B] B[image_mult (B := B) F] := by
  refine AlgEquiv.ofAlgHom (dilatation_baseChange_hom A B F)
    (dilatation_baseChange_inv A B F flat) ?_ ?_
  ·
    refine Multicenter.lemma_exists_unique_morphism' (image_mult (B := B) F)
      (fun i => ?_) (fun i => ?_) _ _
    · have h := Multicenter.Dilatation.nonzerodiv_image
        (F := image_mult (B := B) F) (Finsupp.single i 1)
      rwa [familyPow_single] at h
    · have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
        (F := image_mult (B := B) F) (Finsupp.single i 1)
      rwa [familyPow_single, familyPow_single] at h
  ·
    refine Algebra.TensorProduct.ext' (fun b a => ?_)
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq,
      dilatation_baseChange_hom, Algebra.TensorProduct.lift_tmul, map_mul,
      Algebra.ofId_apply, AlgHom.commutes, dilatation_baseChange_inv_functo,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    simp

instance schemeOverOfAlgebra (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

lemma open_implies_flat_ring (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] : RingHom.Flat (algebraMap A B) := by
  haveI hf : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    inferInstanceAs (AlgebraicGeometry.Flat (Spec B ↘ Spec A))
  have h := (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat)
    (φ := CommRingCat.ofHom (algebraMap A B))).mp hf
  simpa using h

/-- Elementary ring-theoretic bridge: if two quotients `R ⧸ J` and `S ⧸ J'` of rings related
by an isomorphism `e : R ≃+* S` are compatible via a ring isomorphism `φ` of the quotients
commuting with the quotient maps and `e`, then the ideals correspond exactly under `e`
(no abstract "closed subschemes of `Spec R` biject with ideals" uniqueness needed — this is
just `ker (φ ∘ mk J) = ker (mk J)` since `φ` is injective). -/
theorem Ideal.map_eq_of_quotientIso {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (J : Ideal R) (J' : Ideal S) (φ : R ⧸ J ≃+* S ⧸ J')
    (h : ∀ r : R, Ideal.Quotient.mk J' (e r) = φ (Ideal.Quotient.mk J r)) :
    J' = Ideal.map (e : R →+* S) J := by
  apply Ideal.ext
  intro s
  rw [Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective]
  constructor
  · intro hs
    refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
    have h0 : Ideal.Quotient.mk J' (e (e.symm s)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (by rwa [e.apply_symm_apply])
    rw [h, ← map_zero φ] at h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (φ.injective h0)
  · rintro ⟨r, hr, rfl⟩
    have h0 : Ideal.Quotient.mk J r = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hr
    have h2 := h r
    rw [h0, map_zero] at h2
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2

/-- Uniqueness half of the dilatation universal property at scheme level, for an affine
source: two maps to `Spec A[F]` inducing the same map to `Spec A`, over a ring whose
pushed elems are nonzerodivisors generating the pushed `LargeIdeal`s, agree. -/
theorem dila_hom_unique (A : CommRingCat.{u+1}) (F : Multicenter A) {T : Scheme.{u+1}}
    [IsAffine T] (w : A ⟶ Γ(T, ⊤))
    (hnzd : ∀ i, w.hom (F.elem i) ∈ nonZeroDivisors Γ(T, ⊤))
    (hgen : ∀ i, Ideal.span {w.hom (F.elem i)} = Ideal.map w.hom (F.LargeIdeal i))
    (u v : T ⟶ Spec (CommRingCat.of (Multicenter.Dilatation F)))
    (hu : u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) =
      T.isoSpec.hom ≫ Spec.map w)
    (hv : v ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) =
      T.isoSpec.hom ≫ Spec.map w) : u = v := by
  letI : Algebra A Γ(T, ⊤) := w.hom.toAlgebra
  have key : ∀ t : T ⟶ Spec (CommRingCat.of (Multicenter.Dilatation F)),
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) =
        T.isoSpec.hom ≫ Spec.map w →
      ∃ χ : Multicenter.Dilatation F →ₐ[A] Γ(T, ⊤),
        t = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) := by
    intro t ht
    set ρ := Spec.preimage (T.isoSpec.inv ≫ t) with hρ
    have hcomm : CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F)) ≫ ρ = w := by
      apply Spec.map_injective
      rw [Spec.map_comp, hρ, Spec.map_preimage, Category.assoc, ht,
        Iso.inv_hom_id_assoc]
    refine ⟨{ toRingHom := ρ.hom, commutes' := fun a => ?_ }, ?_⟩
    · exact congrArg (fun f => (CommRingCat.Hom.hom f) a) hcomm
    · rw [show Spec.map (CommRingCat.ofHom ρ.hom) = T.isoSpec.inv ≫ t from by
        rw [CommRingCat.ofHom_hom, hρ, Spec.map_preimage], Iso.hom_inv_id_assoc]
  obtain ⟨χu, hχu⟩ := key u hu
  obtain ⟨χv, hχv⟩ := key v hv
  have : χu = χv := Multicenter.lemma_exists_unique_morphism' F hnzd hgen χu χv
  rw [hχu, hχv, this]

/-- Uniqueness half of the dilatation universal property for an ARBITRARY source `T`
(no affineness): two maps to `Spec A[F]` over the same `w : T ⟶ Spec A` agree, provided
the Cartier/generation conditions hold on the pieces of some affine open cover.
Proved by restricting to each piece and applying the affine case, then `hom_ext`.

This is the analogue of `ProjBlowup_UnivProp_unicity_affine`: "affine" refers to the
BASE `Spec A`, never to the source. -/
theorem dila_hom_unique_cover (A : CommRingCat.{u+1}) (F : Multicenter A) {T : Scheme.{u+1}}
    (w : T ⟶ Spec A) (𝒰 : T.OpenCover) [∀ j, IsAffine (𝒰.obj j)]
    (hnzd : ∀ (j : 𝒰.J) (i : F.index),
      (Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫ w)).hom (F.elem i) ∈
        nonZeroDivisors Γ(𝒰.obj j, ⊤))
    (hgen : ∀ (j : 𝒰.J) (i : F.index),
      Ideal.span {(Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫ w)).hom (F.elem i)} =
        Ideal.map (Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫ w)).hom
          (F.LargeIdeal i))
    (u v : T ⟶ Spec (CommRingCat.of (Multicenter.Dilatation F)))
    (hu : u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) = w)
    (hv : v ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) = w) :
    u = v := by
  refine 𝒰.hom_ext u v fun j => ?_
  set wj := Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫ w) with hwj
  have hwj_eq : (𝒰.obj j).isoSpec.hom ≫ Spec.map wj = 𝒰.map j ≫ w := by
    rw [hwj, Spec.map_preimage, Iso.hom_inv_id_assoc]
  refine dila_hom_unique A F wj (hnzd j) (hgen j) _ _ ?_ ?_
  · rw [Category.assoc, hu, hwj_eq]
  · rw [Category.assoc, hv, hwj_eq]

/-- Two generators of the same principal ideal: if one is a nonzerodivisor, so is the
other (they differ by a unit). -/
lemma nonZeroDivisors_of_span_singleton_eq {R : Type*} [CommRing R] {a b : R}
    (h : Ideal.span {a} = Ideal.span {b}) (hb : b ∈ nonZeroDivisors R) :
    a ∈ nonZeroDivisors R := by
  have ha' : a ∈ Ideal.span ({b} : Set R) := h ▸ Ideal.subset_span rfl
  have hb' : b ∈ Ideal.span ({a} : Set R) := h ▸ Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton'] at ha' hb'
  obtain ⟨r, hr⟩ := ha'
  obtain ⟨s, hs⟩ := hb'
  have hcancel : (1 - s * r) * b = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hr, hs, sub_self]
  have hsr : (1 : R) - s * r = 0 := (mem_nonZeroDivisors_iff.mp hb).2 _ hcancel
  have hunit : IsUnit r :=
    isUnit_of_mul_eq_one r s (by rw [mul_comm]; exact (sub_eq_zero.mp hsr).symm)
  rw [← hr]
  exact mul_mem (hunit.mem_nonZeroDivisors) hb

namespace SchemeDilatation

variable {X : Scheme.{u+1}}


namespace PreMultiCenter

variable (M : PreMultiCenter X)

noncomputable def localChart (γ : M.cov.J) : Scheme :=
  Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)))

instance localChart_isAffine (γ : M.cov.J) : IsAffine (M.localChart γ) := by
  unfold localChart
  infer_instance

noncomputable def localChartHom (γ : M.cov.J) : M.localChart γ ⟶ Spec (M.cov.obj γ) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ))))

instance localChartHom_affine (γ : M.cov.J) : IsAffineHom (M.localChartHom γ) :=
  isAffineHom_of_isAffine _

def chartToBase (γ : M.cov.J) : M.localChart γ ⟶ X :=
  M.localChartHom γ ≫ M.cov.map γ

def overlap (γ γ' : M.cov.J) : Scheme :=
  pullback (M.chartToBase γ) (M.cov.map γ')

def overlapFst (γ γ' : M.cov.J) : M.overlap γ γ' ⟶ M.localChart γ :=
  pullback.fst _ _

instance overlapFst_isOpenImmersion (γ γ' : M.cov.J) :
    IsOpenImmersion (M.overlapFst γ γ') := by
  unfold overlapFst
  infer_instance

def overlapToBase (γ γ' : M.cov.J) : M.overlap γ γ' ⟶ X :=
  M.overlapFst γ γ' ≫ M.chartToBase γ

noncomputable def overlapPaste (γ γ' : M.cov.J) :
    M.overlap γ γ' ≅ pullback (M.localChartHom γ) (pullback.fst (M.cov.map γ) (M.cov.map γ')) :=
  (pullbackRightPullbackFstIso (M.cov.map γ) (M.cov.map γ') (M.localChartHom γ)).symm

section AffineBase

variable [IsAffine X]

noncomputable def baseRingHom (γ : M.cov.J) : CommRingCat.of (Γ(X, ⊤)) ⟶ M.cov.obj γ :=
  Spec.preimage (M.cov.map γ ≫ X.isoSpec.hom)

theorem baseRingHom_spec (γ : M.cov.J) :
    M.cov.map γ ≫ X.isoSpec.hom = Spec.map (M.baseRingHom γ) :=
  (Spec.map_preimage _).symm

noncomputable instance baseAlgebra (γ : M.cov.J) : Algebra (Γ(X, ⊤)) (M.cov.obj γ) :=
  (M.baseRingHom γ).hom.toAlgebra

theorem baseAlgebra_algebraMap (γ : M.cov.J) :
    algebraMap (Γ(X, ⊤)) (M.cov.obj γ) = (M.baseRingHom γ).hom := rfl

noncomputable instance baseAlgebraDilatation (γ : M.cov.J) :
    Algebra (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)) :=
  Multicenter.Dilatation.instAlgebra _

theorem chartToBase_spec (γ : M.cov.J) :
    M.chartToBase γ ≫ X.isoSpec.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)))) := by
  unfold chartToBase localChartHom
  rw [Category.assoc, M.baseRingHom_spec γ, ← Spec.map_comp]
  congr 1

noncomputable def pullbackTargetIso {Y Z W : Scheme.{u+1}} (f : Y ⟶ X) (g : Z ⟶ X)
    (e : X ≅ W) : pullback f g ≅ pullback (f ≫ e.hom) (g ≫ e.hom) :=
  asIso (pullback.map f g (f ≫ e.hom) (g ≫ e.hom) (𝟙 _) (𝟙 _) e.hom
    (by simp) (by simp))

noncomputable abbrev overlapRing (γ γ' : M.cov.J) : Type (u + 1) :=
  TensorProduct (Γ(X, ⊤)) (M.cov.obj γ) (M.cov.obj γ')

/-- The *plain* (undilated) double chart, `Spec R_γ ×_X Spec R_γ'`. -/
def plainOverlap (γ γ' : M.cov.J) : Scheme :=
  pullback (M.cov.map γ) (M.cov.map γ')

theorem cov_map_eq (γ : M.cov.J) :
    M.cov.map γ = Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.cov.obj γ))) ≫
      X.isoSpec.inv := by
  rw [show CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.cov.obj γ)) = M.baseRingHom γ from rfl,
    ← M.baseRingHom_spec γ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem overlapRing_legL_eq (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := M.cov.obj γ) (B := M.cov.obj γ'))) ≫ M.cov.map γ =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ'))) ≫
        X.isoSpec.inv := by
  rw [M.cov_map_eq γ, ← Category.assoc, ← Spec.map_comp]
  congr 2

theorem overlapRing_legR_eq (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := Γ(X, ⊤)) (A := M.cov.obj γ)
        (B := M.cov.obj γ')).toRingHom)) ≫ M.cov.map γ' =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ'))) ≫
        X.isoSpec.inv := by
  rw [M.cov_map_eq γ', ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  show Algebra.TensorProduct.includeRight ((M.baseRingHom γ').hom a) = _
  rw [← M.baseAlgebra_algebraMap γ', AlgHom.commutes]
  rfl

noncomputable def plainOverlapFwd (γ γ' : M.cov.J) :
    Spec (CommRingCat.of (M.overlapRing γ γ')) ⟶ M.plainOverlap γ γ' :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := M.cov.obj γ) (B := M.cov.obj γ'))))
    (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := Γ(X, ⊤)) (A := M.cov.obj γ)
        (B := M.cov.obj γ')).toRingHom)))
    (by rw [M.overlapRing_legL_eq γ γ', M.overlapRing_legR_eq γ γ'])

noncomputable def plainOverlapBwd (γ γ' : M.cov.J) :
    M.plainOverlap γ γ' ⟶ Spec (CommRingCat.of (M.overlapRing γ γ')) :=
  pullback.lift (pullback.fst (M.cov.map γ) (M.cov.map γ'))
    (pullback.snd (M.cov.map γ) (M.cov.map γ'))
    (by
      have h1 := pullback.condition (f := M.cov.map γ) (g := M.cov.map γ')
      rw [← cancel_mono X.isoSpec.inv, Category.assoc, Category.assoc,
        ← M.cov_map_eq γ, ← M.cov_map_eq γ']
      exact h1) ≫ (pullbackSpecIso (Γ(X, ⊤)) (M.cov.obj γ) (M.cov.obj γ')).hom

noncomputable def plainOverlapSpecIso (γ γ' : M.cov.J) :
    M.plainOverlap γ γ' ≅ Spec (CommRingCat.of (M.overlapRing γ γ')) where
  hom := M.plainOverlapBwd γ γ'
  inv := M.plainOverlapFwd γ γ'
  hom_inv_id := by
    unfold plainOverlapFwd plainOverlapBwd
    apply pullback.hom_ext <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSpecIso_hom_fst, pullbackSpecIso_hom_snd]
  inv_hom_id := by
    show M.plainOverlapFwd γ γ' ≫ M.plainOverlapBwd γ γ' = 𝟙 _
    unfold plainOverlapBwd
    rw [← Category.assoc, Iso.comp_hom_eq_id]
    apply pullback.hom_ext <;>
      unfold plainOverlapFwd <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]

theorem plainOverlap_over (γ γ' : M.cov.J) :
    (M.plainOverlapSpecIso γ γ').inv ≫ pullback.fst (M.cov.map γ) (M.cov.map γ') =
      Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))) := by
  show M.plainOverlapFwd γ γ' ≫ pullback.fst (M.cov.map γ) (M.cov.map γ') = _
  unfold plainOverlapFwd
  rw [pullback.lift_fst]
  rfl

theorem chartToBase_eq (γ : M.cov.J) :
    M.chartToBase γ = Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)))) ≫
      X.isoSpec.inv := by
  rw [← M.chartToBase_spec γ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem overlapDila_legL_eq (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := Multicenter.Dilatation (M.localMulticenter γ))
      (B := M.cov.obj γ'))) ≫ M.chartToBase γ =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤))
        (TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ))
          (M.cov.obj γ')))) ≫ X.isoSpec.inv := by
  rw [M.chartToBase_eq γ, ← Category.assoc, ← Spec.map_comp]
  congr 2

theorem overlapDila_legR_eq (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := Γ(X, ⊤))
        (A := Multicenter.Dilatation (M.localMulticenter γ))
        (B := M.cov.obj γ')).toRingHom)) ≫ M.cov.map γ' =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤))
        (TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ))
          (M.cov.obj γ')))) ≫ X.isoSpec.inv := by
  rw [M.cov_map_eq γ', ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  show Algebra.TensorProduct.includeRight ((M.baseRingHom γ').hom a) = _
  rw [← M.baseAlgebra_algebraMap γ', AlgHom.commutes]
  rfl

noncomputable def overlapSpecFwd (γ γ' : M.cov.J) :
    Spec (CommRingCat.of (TensorProduct (Γ(X, ⊤))
      (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ'))) ⟶ M.overlap γ γ' :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := Multicenter.Dilatation (M.localMulticenter γ))
      (B := M.cov.obj γ'))))
    (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := Γ(X, ⊤))
        (A := Multicenter.Dilatation (M.localMulticenter γ))
        (B := M.cov.obj γ')).toRingHom)))
    (by rw [M.overlapDila_legL_eq γ γ', M.overlapDila_legR_eq γ γ'])

noncomputable def overlapSpecBwd (γ γ' : M.cov.J) :
    M.overlap γ γ' ⟶ Spec (CommRingCat.of (TensorProduct (Γ(X, ⊤))
      (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ'))) :=
  pullback.lift (pullback.fst (M.chartToBase γ) (M.cov.map γ'))
    (pullback.snd (M.chartToBase γ) (M.cov.map γ'))
    (by
      have h1 := pullback.condition (f := M.chartToBase γ) (g := M.cov.map γ')
      rw [← cancel_mono X.isoSpec.inv, Category.assoc, Category.assoc,
        ← M.chartToBase_eq γ, ← M.cov_map_eq γ']
      exact h1) ≫
    (pullbackSpecIso (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ))
      (M.cov.obj γ')).hom

noncomputable def overlapSpecIso (γ γ' : M.cov.J) :
    M.overlap γ γ' ≅
      Spec (CommRingCat.of
        (TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ))
          (M.cov.obj γ'))) where
  hom := M.overlapSpecBwd γ γ'
  inv := M.overlapSpecFwd γ γ'
  hom_inv_id := by
    unfold overlapSpecFwd overlapSpecBwd
    apply pullback.hom_ext <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSpecIso_hom_fst, pullbackSpecIso_hom_snd]
  inv_hom_id := by
    show M.overlapSpecFwd γ γ' ≫ M.overlapSpecBwd γ γ' = 𝟙 _
    unfold overlapSpecBwd
    rw [← Category.assoc, Iso.comp_hom_eq_id]
    apply pullback.hom_ext <;>
      unfold overlapSpecFwd <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]

/-- The first projection of the overlap reads through `overlapSpecIso` as the left
tensor inclusion. -/
theorem overlapSpecIso_inv_fst (γ γ' : M.cov.J) :
    (M.overlapSpecIso γ γ').inv ≫ pullback.fst (M.chartToBase γ) (M.cov.map γ') =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Γ(X, ⊤)) (A := Multicenter.Dilatation (M.localMulticenter γ))
        (B := M.cov.obj γ'))) := by
  show M.overlapSpecFwd γ γ' ≫ pullback.fst _ _ = _
  unfold overlapSpecFwd
  rw [pullback.lift_fst]

/-- The symmetry of the two-chart overlap ring, `R_γ ⊗[A] R_γ' ≃ R_γ' ⊗[A] R_γ`. -/
noncomputable def overlapRingComm (γ γ' : M.cov.J) :
    M.overlapRing γ γ' ≃+* M.overlapRing γ' γ :=
  (Algebra.TensorProduct.comm (Γ(X, ⊤)) (M.cov.obj γ) (M.cov.obj γ')).toRingEquiv

/-- The canonical map `Spec (R_γ ⊗[A] R_γ') ⟶ X`, through which BOTH chart legs factor. -/
noncomputable def overlapBaseMap (γ γ' : M.cov.J) :
    Spec (CommRingCat.of (M.overlapRing γ γ')) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ'))) ≫ X.isoSpec.inv

/-- Transporting along the tensor-swap identifies the two base maps. -/
theorem overlapBaseMap_comm (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom) ≫
      M.overlapBaseMap γ γ' = M.overlapBaseMap γ' γ := by
  unfold overlapBaseMap
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  exact (Algebra.TensorProduct.comm (Γ(X, ⊤)) (M.cov.obj γ) (M.cov.obj γ')).commutes a

/-- The `γ`-chart leg `Spec S → Spec R_γ → X` equals the canonical base map. -/
theorem chartPaste_leg (γ γ' : M.cov.J) :
    Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))) ≫
      M.cov.map γ = M.overlapBaseMap γ γ' := by
  rw [M.cov_map_eq γ, ← Category.assoc, ← Spec.map_comp]
  unfold overlapBaseMap
  congr 2

/-- Pasting `Y'`'s chart-`γ` presentation out to the double overlap:
the pullback of the global subscheme along the canonical base map is
`Spec (S ⧸ J_γ·S)` where `J_γ = Y'.ideal i γ`. -/
noncomputable def overlapPasteY (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    pullback (M.Yrep.subscheme i ↘ X) (M.overlapBaseMap γ γ') ≅
      Spec (CommRingCat.of ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ))) :=
  letI : Algebra (M.Yrep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')) :=
    inferInstanceAs (Algebra (M.cov.obj γ) (M.overlapRing γ γ'))
  pullback.congrHom rfl (M.chartPaste_leg γ γ').symm ≪≫
    M.Yrep.chartPasteIso γ i (CommRingCat.of (M.overlapRing γ γ'))

/-- Same, for the `D`-side representative. -/
noncomputable def overlapPasteD (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    pullback (M.Drep.subscheme i ↘ X) (M.overlapBaseMap γ γ') ≅
      Spec (CommRingCat.of ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ))) :=
  letI : Algebra (M.Drep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')) :=
    inferInstanceAs (Algebra (M.cov.obj γ) (M.overlapRing γ γ'))
  pullback.congrHom rfl (M.chartPaste_leg γ γ').symm ≪≫
    M.Drep.chartPasteIso γ i (CommRingCat.of (M.overlapRing γ γ'))

@[reassoc]
theorem overlapPasteY_snd (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    (M.overlapPasteY γ γ' i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ)))) =
      pullback.snd (M.Yrep.subscheme i ↘ X) (M.overlapBaseMap γ γ') := by
  letI : Algebra (M.Yrep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')) :=
    inferInstanceAs (Algebra (M.cov.obj γ) (M.overlapRing γ γ'))
  have h := M.Yrep.chartPasteIso_snd γ i (CommRingCat.of (M.overlapRing γ γ'))
  have hmk : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.Yrep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')))
          (M.Yrep.ideal i γ)))) := rfl
  have hsnd : pullback.snd (M.Yrep.subscheme i ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (M.Yrep.cov.obj γ)
        (CommRingCat.of (M.overlapRing γ γ')))) ≫ M.Yrep.cov.map γ) =
      pullback.snd (M.Yrep.subscheme i ↘ X)
        (Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))) ≫
          M.cov.map γ) := rfl
  unfold overlapPasteY
  simp only [Iso.trans_hom, Category.assoc]
  rw [hmk, h]
  rw [pullback.congrHom_hom, hsnd, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem overlapPasteD_snd (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    (M.overlapPasteD γ γ' i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ)))) =
      pullback.snd (M.Drep.subscheme i ↘ X) (M.overlapBaseMap γ γ') := by
  letI : Algebra (M.Drep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')) :=
    inferInstanceAs (Algebra (M.cov.obj γ) (M.overlapRing γ γ'))
  have h := M.Drep.chartPasteIso_snd γ i (CommRingCat.of (M.overlapRing γ γ'))
  have hmk : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.Drep.cov.obj γ) (CommRingCat.of (M.overlapRing γ γ')))
          (M.Drep.ideal i γ)))) := rfl
  have hsnd : pullback.snd (M.Drep.subscheme i ↘ X)
      (Spec.map (CommRingCat.ofHom (algebraMap (M.Drep.cov.obj γ)
        (CommRingCat.of (M.overlapRing γ γ')))) ≫ M.Drep.cov.map γ) =
      pullback.snd (M.Drep.subscheme i ↘ X)
        (Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))) ≫
          M.cov.map γ) := rfl
  unfold overlapPasteD
  simp only [Iso.trans_hom, Category.assoc]
  rw [hmk, h]
  rw [pullback.congrHom_hom, hsnd, pullback.lift_snd, Category.comp_id]

theorem overlapRingComm_symm (γ γ' : M.cov.J) :
    M.overlapRingComm γ' γ = (M.overlapRingComm γ γ').symm := by
  unfold overlapRingComm
  rw [← Algebra.TensorProduct.comm_symm]
  rfl

/-- Transport of pullbacks along the tensor-swap of the two base maps. Generic in the
scheme mapping to `X`. -/
noncomputable def overlapTransport (γ γ' : M.cov.J) {W : Scheme.{u+1}} (w : W ⟶ X) :
    pullback w (M.overlapBaseMap γ' γ) ≅ pullback w (M.overlapBaseMap γ γ') where
  hom := pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom)) (𝟙 _)
    (by simp) (by rw [Category.comp_id]; exact (M.overlapBaseMap_comm γ γ').symm)
  inv := pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (M.overlapRingComm γ' γ).toRingHom)) (𝟙 _)
    (by simp) (by rw [Category.comp_id]; exact (M.overlapBaseMap_comm γ' γ).symm)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [show (M.overlapRingComm γ γ').toRingHom.comp (M.overlapRingComm γ' γ).toRingHom =
          RingHom.id _ from ?_]
      · simp
      · rw [M.overlapRingComm_symm γ γ']
        ext s
        exact (M.overlapRingComm γ γ').apply_symm_apply s
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [show (M.overlapRingComm γ' γ).toRingHom.comp (M.overlapRingComm γ γ').toRingHom =
          RingHom.id _ from ?_]
      · simp
      · rw [M.overlapRingComm_symm γ γ']
        ext s
        exact (M.overlapRingComm γ γ').symm_apply_apply s

@[reassoc]
theorem overlapTransport_snd (γ γ' : M.cov.J) {W : Scheme.{u+1}} (w : W ⟶ X) :
    (M.overlapTransport γ γ' w).hom ≫ pullback.snd w (M.overlapBaseMap γ γ') =
      pullback.snd w (M.overlapBaseMap γ' γ) ≫
        Spec.map (CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom) := by
  unfold overlapTransport
  exact pullback.lift_snd _ _ _

/-- The comparison of the two quotient presentations of the pullback of `Y'.subscheme i`
to the double overlap, at charts `γ'` and `γ`. -/
noncomputable def overlapCompareY (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    Spec (CommRingCat.of ((M.overlapRing γ' γ) ⧸
        Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Yrep.ideal i γ'))) ≅
    Spec (CommRingCat.of ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ))) :=
  (M.overlapPasteY γ' γ i).symm ≪≫ M.overlapTransport γ γ' (M.Yrep.subscheme i ↘ X) ≪≫
    M.overlapPasteY γ γ' i

noncomputable def overlapCompareD (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    Spec (CommRingCat.of ((M.overlapRing γ' γ) ⧸
        Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ'))) ≅
    Spec (CommRingCat.of ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ))) :=
  (M.overlapPasteD γ' γ i).symm ≪≫ M.overlapTransport γ γ' (M.Drep.subscheme i ↘ X) ≪≫
    M.overlapPasteD γ γ' i

/-- The comparison commutes with the quotient maps and the tensor swap. -/
theorem overlapCompareY_square (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    (M.overlapCompareY γ γ' i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Yrep.ideal i γ')))) ≫
        Spec.map (CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom) := by
  unfold overlapCompareY
  simp only [Iso.trans_hom, Category.assoc]
  rw [M.overlapPasteY_snd γ γ' i, M.overlapTransport_snd γ γ' (M.Yrep.subscheme i ↘ X),
    ← Category.assoc, Iso.symm_hom]
  rw [← M.overlapPasteY_snd γ' γ i, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem overlapCompareD_square (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    (M.overlapCompareD γ γ' i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ')))) ≫
        Spec.map (CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom) := by
  unfold overlapCompareD
  simp only [Iso.trans_hom, Category.assoc]
  rw [M.overlapPasteD_snd γ γ' i, M.overlapTransport_snd γ γ' (M.Drep.subscheme i ↘ X),
    ← Category.assoc, Iso.symm_hom]
  rw [← M.overlapPasteD_snd γ' γ i, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The ring-level isomorphism of the two quotient presentations, extracted from
`overlapCompareY` by full faithfulness of `Spec`. -/
noncomputable def overlapQuotEquivY (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ)) ≃+*
    ((M.overlapRing γ' γ) ⧸
        Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Yrep.ideal i γ')) :=
  CategoryTheory.Iso.commRingCatIsoToRingEquiv
    { hom := Spec.preimage (M.overlapCompareY γ γ' i).hom
      inv := Spec.preimage (M.overlapCompareY γ γ' i).inv
      hom_inv_id := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id, Spec.map_id])
      inv_hom_id := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id, Spec.map_id]) }

noncomputable def overlapQuotEquivD (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    ((M.overlapRing γ γ') ⧸
        Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ)) ≃+*
    ((M.overlapRing γ' γ) ⧸
        Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ')) :=
  CategoryTheory.Iso.commRingCatIsoToRingEquiv
    { hom := Spec.preimage (M.overlapCompareD γ γ' i).hom
      inv := Spec.preimage (M.overlapCompareD γ γ' i).inv
      hom_inv_id := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.inv_hom_id, Spec.map_id])
      inv_hom_id := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id, Spec.map_id]) }

/-- THE ideal correspondence: the `γ'`-side pushed ideal is the tensor-swap image of the
`γ`-side pushed ideal. Both present the pullback of the same global subscheme `Y'`. -/
theorem overlapIdealY_eq (γ γ' : M.cov.J) (i : M.Yrep.indnumb) :
    Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Yrep.ideal i γ') =
      Ideal.map ((M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ)) := by
  refine Ideal.map_eq_of_quotientIso (M.overlapRingComm γ γ') _ _
    (M.overlapQuotEquivY γ γ' i) fun s => ?_
  have hring : CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Yrep.ideal i γ))) ≫
        CommRingCat.ofHom ((M.overlapQuotEquivY γ γ' i) : _ →+* _) =
      CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Yrep.ideal i γ'))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    have hpre : Spec.map (CommRingCat.ofHom ((M.overlapQuotEquivY γ γ' i) : _ →+* _)) =
        (M.overlapCompareY γ γ' i).hom := by
      rw [show CommRingCat.ofHom ((M.overlapQuotEquivY γ γ' i) : _ →+* _) =
        Spec.preimage (M.overlapCompareY γ γ' i).hom from rfl, Spec.map_preimage]
    rw [hpre]
    exact M.overlapCompareY_square γ γ' i
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) s) hring).symm

theorem overlapIdealD_eq (γ γ' : M.cov.J) (i : M.Drep.indnumb) :
    Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ') =
      Ideal.map ((M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ)) := by
  refine Ideal.map_eq_of_quotientIso (M.overlapRingComm γ γ') _ _
    (M.overlapQuotEquivD γ γ' i) fun s => ?_
  have hring : CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ))) ≫
        CommRingCat.ofHom ((M.overlapQuotEquivD γ γ' i) : _ →+* _) =
      CommRingCat.ofHom (M.overlapRingComm γ γ').toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ'))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    have hpre : Spec.map (CommRingCat.ofHom ((M.overlapQuotEquivD γ γ' i) : _ →+* _)) =
        (M.overlapCompareD γ γ' i).hom := by
      rw [show CommRingCat.ofHom ((M.overlapQuotEquivD γ γ' i) : _ →+* _) =
        Spec.preimage (M.overlapCompareD γ γ' i).hom from rfl, Spec.map_preimage]
    rw [hpre]
    exact M.overlapCompareD_square γ γ' i
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) s) hring).symm

/-- The pushed local elems generate corresponding principal ideals under the tensor swap:
both push the same `Drep.ideal i` (at charts `γ` resp. `γ'`) into the overlap ring. -/
theorem overlapElemSpan_eq (γ γ' : M.cov.J) (i : M.indnumb) :
    Ideal.span {(M.overlapRingComm γ γ')
      ((algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) ((M.localMulticenter γ).elem i))} =
    Ideal.span {(algebraMap (M.cov.obj γ') (M.overlapRing γ' γ))
      ((M.localMulticenter γ').elem i)} := by
  letI := M.Dprin i γ
  letI := M.Dprin i γ'
  have hγ : Ideal.span {(algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))
      ((M.localMulticenter γ).elem i)} =
      Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) (M.Drep.ideal i γ) := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact congrArg _ (Ideal.span_singleton_generator _)
  have hγ' : Ideal.span {(algebraMap (M.cov.obj γ') (M.overlapRing γ' γ))
      ((M.localMulticenter γ').elem i)} =
      Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)) (M.Drep.ideal i γ') := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact congrArg _ (Ideal.span_singleton_generator _)
  rw [hγ', ← Set.image_singleton, ← Ideal.map_span, hγ]
  exact (M.overlapIdealD_eq γ γ' i).symm

/-- The pushed `LargeIdeal`s correspond under the tensor swap. -/
theorem overlapLargeIdeal_eq (γ γ' : M.cov.J) (i : M.indnumb) :
    Ideal.map ((M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
      (Ideal.map (algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))
        ((M.localMulticenter γ).LargeIdeal i)) =
    Ideal.map (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ))
      ((M.localMulticenter γ').LargeIdeal i) := by
  letI := M.Dprin i γ
  letI := M.Dprin i γ'
  have hspanγ : Ideal.span {(M.localMulticenter γ).elem i} = M.Drep.ideal i γ :=
    Ideal.span_singleton_generator _
  have hspanγ' : Ideal.span {(M.localMulticenter γ').elem i} = M.Drep.ideal i γ' :=
    Ideal.span_singleton_generator _
  unfold Multicenter.LargeIdeal
  rw [Submodule.add_eq_sup, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_sup, Ideal.map_sup,
    hspanγ, hspanγ']
  congr 1
  · exact (M.overlapIdealY_eq γ γ' i).symm
  · exact (M.overlapIdealD_eq γ γ' i).symm

/-- Nonzerodivisor condition for `desc`: the swap-image of a pushed local elem is a
nonzerodivisor in the `γ'`-side dilatation, because it generates the same principal
ideal as the `γ'`-side pushed elem, which is a nonzerodivisor there. -/
theorem swap_nonzerodiv (γ γ' : M.cov.J) (i : M.indnumb) :
    ((algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')))).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
      ((Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ)).elem i) ∈
      nonZeroDivisors (Multicenter.Dilatation (Multicenter.image_mult
        (B := M.overlapRing γ' γ) (M.localMulticenter γ'))) := by
  have hnzd : (algebraMap (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ'))))
      ((Multicenter.image_mult (B := M.overlapRing γ' γ) (M.localMulticenter γ')).elem i) ∈
      nonZeroDivisors _ := by
    have h := Multicenter.Dilatation.nonzerodiv_image
      (F := Multicenter.image_mult (B := M.overlapRing γ' γ) (M.localMulticenter γ'))
      (Finsupp.single i 1)
    rwa [familyPow_single] at h
  refine nonZeroDivisors_of_span_singleton_eq ?_ hnzd
  have hspan := congrArg (Ideal.map (algebraMap (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ'))))) (M.overlapElemSpan_eq γ γ' i)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at hspan
  exact hspan

/-- Generation condition for `desc`: the span of the swap-image of a pushed elem is the
push of the corresponding `LargeIdeal`. -/
theorem swap_gen (γ γ' : M.cov.J) (i : M.indnumb) :
    Ideal.span {((algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')))).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
      ((Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ)).elem i)} =
    Ideal.map ((algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')))).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
      ((Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ)).LargeIdeal i) := by
  have hgen' := Multicenter.Dilatation.image_elem_LargeIdeal_equal
    (F := Multicenter.image_mult (B := M.overlapRing γ' γ) (M.localMulticenter γ'))
    (Finsupp.single i 1)
  rw [familyPow_single, familyPow_single, Multicenter.image_mult_elem] at hgen'
  have hspan := congrArg (Ideal.map (algebraMap (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ'))))) (M.overlapElemSpan_eq γ γ' i)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at hspan
  rw [show (((algebraMap (M.overlapRing γ' γ) _).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ)))
      ((Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ)).elem i)) =
      ((algebraMap (M.overlapRing γ' γ) _) ((M.overlapRingComm γ γ')
        ((algebraMap (M.cov.obj γ) (M.overlapRing γ γ'))
          ((M.localMulticenter γ).elem i)))) from rfl]
  rw [hspan, hgen', ← Ideal.map_map]
  congr 1
  rw [Multicenter.image_mult_LargeIdeal, Multicenter.image_mult_LargeIdeal]
  exact (M.overlapLargeIdeal_eq γ γ' i).symm

/-- The swap ring hom between the two overlap dilatations, via the universal property
(`Multicenter.desc`). -/
noncomputable def swapRingHom (γ γ' : M.cov.J) :
    Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
      (M.localMulticenter γ)) →+*
    Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
      (M.localMulticenter γ')) :=
  letI : Algebra (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ'))) :=
    ((algebraMap (M.overlapRing γ' γ) _).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ))).toAlgebra
  (Multicenter.desc (Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ))
    (fun i => M.swap_nonzerodiv γ γ' i) (fun i => M.swap_gen γ γ' i)).toRingHom

theorem swapRingHom_algebraMap (γ γ' : M.cov.J) (s : M.overlapRing γ γ') :
    M.swapRingHom γ γ' ((algebraMap (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ)))) s) =
    (algebraMap (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ')))) ((M.overlapRingComm γ γ') s) := by
  letI : Algebra (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ'))) :=
    ((algebraMap (M.overlapRing γ' γ) _).comp
      (M.overlapRingComm γ γ' : (M.overlapRing γ γ') →+* (M.overlapRing γ' γ))).toAlgebra
  exact (Multicenter.desc (Multicenter.image_mult (B := M.overlapRing γ γ')
    (M.localMulticenter γ))
    (fun i => M.swap_nonzerodiv γ γ' i) (fun i => M.swap_gen γ γ' i)).commutes s

theorem swapRingHom_comp (γ γ' : M.cov.J) :
    (M.swapRingHom γ' γ).comp (M.swapRingHom γ γ') = RingHom.id _ := by
  have hnzd : ∀ i, (algebraMap (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))))
      ((Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ)).elem i) ∈
      nonZeroDivisors _ := fun i => by
    have h := Multicenter.Dilatation.nonzerodiv_image
      (F := Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ))
      (Finsupp.single i 1)
    rwa [familyPow_single] at h
  have hgen : ∀ i, Ideal.span {(algebraMap (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))))
      ((Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ)).elem i)} =
      Ideal.map (algebraMap (M.overlapRing γ γ') _)
        ((Multicenter.image_mult (B := M.overlapRing γ γ')
          (M.localMulticenter γ)).LargeIdeal i) := fun i => by
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
      (F := Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ))
      (Finsupp.single i 1)
    rwa [familyPow_single, familyPow_single] at h
  have hcommutes : ∀ s : M.overlapRing γ γ',
      ((M.swapRingHom γ' γ).comp (M.swapRingHom γ γ'))
        ((algebraMap (M.overlapRing γ γ')
          (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
            (M.localMulticenter γ)))) s) =
      (algebraMap (M.overlapRing γ γ') _) s := by
    intro s
    rw [RingHom.comp_apply, M.swapRingHom_algebraMap γ γ' s,
      M.swapRingHom_algebraMap γ' γ _]
    rw [M.overlapRingComm_symm γ γ']
    rw [(M.overlapRingComm γ γ').symm_apply_apply s]
  have key := Multicenter.lemma_exists_unique_morphism'
    (Multicenter.image_mult (B := M.overlapRing γ γ') (M.localMulticenter γ))
    hnzd hgen
    { toRingHom := (M.swapRingHom γ' γ).comp (M.swapRingHom γ γ')
      commutes' := hcommutes }
    (AlgHom.id _ _)
  have := congrArg AlgHom.toRingHom key
  simpa using this

/-- The swap ring equivalence between the two overlap dilatation rings. -/
noncomputable def swapRingEquiv (γ γ' : M.cov.J) :
    Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
      (M.localMulticenter γ)) ≃+*
    Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
      (M.localMulticenter γ')) :=
  RingEquiv.ofRingHom (M.swapRingHom γ γ') (M.swapRingHom γ' γ)
    (M.swapRingHom_comp γ' γ) (M.swapRingHom_comp γ γ')

instance chart_over_isOpenImmersion (γ : M.cov.J) :
    IsOpenImmersion (Spec (M.cov.obj γ) ↘ Spec (CommRingCat.of (Γ(X, ⊤)))) := by
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.cov.obj γ))))
  rw [M.baseAlgebra_algebraMap]
  simp only [CommRingCat.ofHom_hom]
  rw [← M.baseRingHom_spec γ]
  infer_instance

instance chartFlat (γ : M.cov.J) : Module.Flat (Γ(X, ⊤)) (M.cov.obj γ) :=
  flat_algebraMap_iff.mp (open_implies_flat_ring (CommRingCat.of (Γ(X, ⊤))) (M.cov.obj γ))

instance overlapRing_flat (γ γ' : M.cov.J) :
    Module.Flat (M.cov.obj γ) (M.overlapRing γ γ') := by
  unfold overlapRing
  infer_instance

theorem overlapRing_flat' (γ γ' : M.cov.J) :
    RingHom.Flat (algebraMap (M.cov.obj γ) (M.overlapRing γ γ')) :=
  flat_algebraMap_iff.mpr (M.overlapRing_flat γ γ')

instance scalarTowerBaseChartDilatation (γ : M.cov.J) :
    IsScalarTower (Γ(X, ⊤)) (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance scalarTowerOverlapImageDilatation (γ γ' : M.cov.J) :
    IsScalarTower (M.cov.obj γ) (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable def overlapAlgEquiv (γ γ' : M.cov.J) :
    TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ')
      ≃ₐ[M.cov.obj γ]
    Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
      (M.localMulticenter γ)) :=
  ((Algebra.TensorProduct.cancelBaseChange (Γ(X, ⊤)) (M.cov.obj γ) (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ')).symm.trans
      (Algebra.TensorProduct.comm (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ))
        (M.overlapRing γ γ'))).trans
    ((dilatation_baseChange_equiv (M.cov.obj γ) (M.overlapRing γ γ') (M.localMulticenter γ)
      (M.overlapRing_flat' γ γ')).restrictScalars (M.cov.obj γ))

noncomputable def overlapRingEquiv (γ γ' : M.cov.J) :
    TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ') ≃+*
      Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ)) :=
  (M.overlapAlgEquiv γ γ').toRingEquiv

/-- `overlapRingEquiv` is compatible with the `Γ(X,⊤)`-algebra structures, through the towers
`Γ(X,⊤) → R_γ → T` and `Γ(X,⊤) → S → S[F_γ]`. -/
theorem overlapRingEquiv_algebraMap (γ γ' : M.cov.J) (a : Γ(X, ⊤)) :
    (M.overlapRingEquiv γ γ')
      ((algebraMap (Γ(X, ⊤)) (TensorProduct (Γ(X, ⊤))
        (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ'))) a) =
    (algebraMap (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))))
      ((algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ')) a) := by
  rw [IsScalarTower.algebraMap_apply (Γ(X, ⊤)) (M.cov.obj γ)
    (TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ')) a]
  rw [show (M.overlapRingEquiv γ γ')
      ((algebraMap (M.cov.obj γ) (TensorProduct (Γ(X, ⊤))
        (Multicenter.Dilatation (M.localMulticenter γ)) (M.cov.obj γ')))
        ((algebraMap (Γ(X, ⊤)) (M.cov.obj γ)) a)) =
      (algebraMap (M.cov.obj γ) (Multicenter.Dilatation (Multicenter.image_mult
        (B := M.overlapRing γ γ') (M.localMulticenter γ))))
        ((algebraMap (Γ(X, ⊤)) (M.cov.obj γ)) a) from
    (M.overlapAlgEquiv γ γ').commutes _]
  rw [IsScalarTower.algebraMap_apply (M.cov.obj γ) (M.overlapRing γ γ')
    (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
      (M.localMulticenter γ)))]
  rw [← IsScalarTower.algebraMap_apply (Γ(X, ⊤)) (M.cov.obj γ) (M.overlapRing γ γ')]

noncomputable def overlapDilaIso (γ γ' : M.cov.J) :
    M.overlap γ γ' ≅
      Spec (CommRingCat.of
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
          (M.localMulticenter γ)))) :=
  M.overlapSpecIso γ γ' ≪≫
    Scheme.Spec.mapIso ((M.overlapRingEquiv γ γ').symm.toCommRingCatIso.op)

/-- The structure map to the base reads through `overlapSpecIso` as the canonical
`Spec` of the algebra map. -/
theorem overlapSpecIso_inv_toBase (γ γ' : M.cov.J) :
    (M.overlapSpecIso γ γ').inv ≫ M.overlapToBase γ γ' =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤))
        (TensorProduct (Γ(X, ⊤)) (Multicenter.Dilatation (M.localMulticenter γ))
          (M.cov.obj γ')))) ≫ X.isoSpec.inv := by
  show (M.overlapSpecIso γ γ').inv ≫ M.overlapFst γ γ' ≫ M.chartToBase γ = _
  rw [← Category.assoc]
  rw [show (M.overlapSpecIso γ γ').inv ≫ M.overlapFst γ γ' =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := Multicenter.Dilatation (M.localMulticenter γ))
      (B := M.cov.obj γ'))) from M.overlapSpecIso_inv_fst γ γ']
  exact M.overlapDila_legL_eq γ γ'

/-- The structure map to the base reads through `overlapDilaIso` as `Spec` of the
composite algebra map `Γ(X,⊤) → S → S[F_γ]`. -/
theorem overlapDilaIso_inv_toBase (γ γ' : M.cov.J) :
    (M.overlapDilaIso γ γ').inv ≫ M.overlapToBase γ γ' =
      Spec.map (CommRingCat.ofHom ((algebraMap (M.overlapRing γ γ')
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
          (M.localMulticenter γ)))).comp
        (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ')))) ≫ X.isoSpec.inv := by
  unfold overlapDilaIso
  simp only [Iso.trans_inv, Category.assoc]
  rw [M.overlapSpecIso_inv_toBase γ γ']
  rw [show (Scheme.Spec.mapIso ((M.overlapRingEquiv γ γ').symm.toCommRingCatIso.op)).inv =
    Spec.map (CommRingCat.ofHom ((M.overlapRingEquiv γ γ') : _ →+* _)) from rfl]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  exact M.overlapRingEquiv_algebraMap γ γ' a

/-- The swap isomorphism between the two overlaps, transported through `overlapDilaIso`. -/
noncomputable def overlapSwapIso (γ γ' : M.cov.J) :
    M.overlap γ γ' ≅ M.overlap γ' γ :=
  M.overlapDilaIso γ γ' ≪≫
    (Scheme.Spec.mapIso ((M.swapRingEquiv γ γ').toCommRingCatIso.op)).symm ≪≫
    (M.overlapDilaIso γ' γ).symm

/-- The swap isomorphism commutes with the structure maps to the base:
this is the existence half of the comparison. -/
theorem overlapSwapIso_toBase (γ γ' : M.cov.J) :
    (M.overlapSwapIso γ γ').hom ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ' := by
  unfold overlapSwapIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [M.overlapDilaIso_inv_toBase γ' γ]
  rw [show (Scheme.Spec.mapIso ((M.swapRingEquiv γ γ').toCommRingCatIso.op)).inv =
    Spec.map (CommRingCat.ofHom ((M.swapRingEquiv γ γ').symm : _ →+* _)) from rfl]
  rw [← Spec.map_comp_assoc]
  rw [show (CommRingCat.ofHom ((algebraMap (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
        (M.localMulticenter γ')))).comp
      (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ)))) ≫
      (CommRingCat.ofHom ((M.swapRingEquiv γ γ').symm : _ →+* _)) =
      CommRingCat.ofHom ((algebraMap (M.overlapRing γ γ')
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
          (M.localMulticenter γ)))).comp
        (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ'))) from ?_]
  · rw [← M.overlapDilaIso_inv_toBase γ γ', ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  · apply CommRingCat.hom_ext
    ext a
    show (M.swapRingEquiv γ γ').symm ((algebraMap (M.overlapRing γ' γ) _)
      ((algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ)) a)) = _
    rw [show ((M.swapRingEquiv γ γ').symm : _ → _) = (M.swapRingHom γ' γ : _ → _) from rfl]
    rw [M.swapRingHom_algebraMap γ' γ]
    simp only [CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact congrArg (algebraMap (M.overlapRing γ γ')
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))))
      ((Algebra.TensorProduct.comm (Γ(X, ⊤)) (M.cov.obj γ') (M.cov.obj γ)).commutes a)

/-- The open immersion `Spec S' → X` through which both overlap structure maps factor. -/
theorem baseOpen_mono (γ γ' : M.cov.J) :
    Mono (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ))) ≫ X.isoSpec.inv) := by
  haveI hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (M.cov.obj γ') (M.overlapRing γ' γ)))) := by
    rw [← M.plainOverlap_over γ' γ]
    haveI := M.cov.map_prop γ
    infer_instance
  haveI hcov : IsOpenImmersion (M.cov.map γ') := M.cov.map_prop γ'
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(X, ⊤)) (A := M.cov.obj γ') (B := M.cov.obj γ))) ≫ M.cov.map γ') := by
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Γ(X, ⊤)) (A := M.cov.obj γ') (B := M.cov.obj γ)))) := hopen
    infer_instance
  rw [← M.overlapRing_legL_eq γ' γ]
  infer_instance

/-- Uniqueness of over-morphisms between the two overlaps: any two maps commuting with the
structure maps to the base agree — by the universal property (ring-level unicity) of the
dilatation, after upgrading over-`X` to over-`Spec S'` through the open immersion. -/
theorem overlap_hom_unique {γ γ' : M.cov.J} (f g : M.overlap γ γ' ⟶ M.overlap γ' γ)
    (hf : f ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ')
    (hg : g ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ') :
    f = g := by
  letI : Algebra (M.overlapRing γ' γ)
      (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
        (M.localMulticenter γ))) :=
    ((algebraMap (M.overlapRing γ γ') _).comp
      (M.overlapRingComm γ' γ : (M.overlapRing γ' γ) →+* (M.overlapRing γ γ'))).toAlgebra
  -- The transported map and its ring-level S'-algebra-hom structure, for any over-map h.
  have main : ∀ h : M.overlap γ γ' ⟶ M.overlap γ' γ,
      h ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ' →
      ∃ χ : Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')) →ₐ[M.overlapRing γ' γ]
          Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
            (M.localMulticenter γ)),
        h = (M.overlapDilaIso γ γ').hom ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
          (M.overlapDilaIso γ' γ).inv := by
    intro h hh
    set φ := (M.overlapDilaIso γ γ').inv ≫ h ≫ (M.overlapDilaIso γ' γ).hom with hφ
    set ρ := Spec.preimage φ with hρ
    -- over-X condition transported to Spec-level
    have hover : φ ≫ Spec.map (CommRingCat.ofHom ((algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')))).comp
        (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ)))) ≫ X.isoSpec.inv =
        Spec.map (CommRingCat.ofHom ((algebraMap (M.overlapRing γ γ')
          (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
            (M.localMulticenter γ)))).comp
          (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ')))) ≫ X.isoSpec.inv := by
      rw [← M.overlapDilaIso_inv_toBase γ' γ, ← M.overlapDilaIso_inv_toBase γ γ']
      rw [hφ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [hh]
    -- upgrade to over-Spec S' via the open immersion
    haveI := M.baseOpen_mono γ γ'
    have hAA : Spec.map (CommRingCat.ofHom
        (M.overlapRingComm γ' γ : (M.overlapRing γ' γ) →+* (M.overlapRing γ γ'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ))) ≫
          X.isoSpec.inv =
        Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ'))) ≫
          X.isoSpec.inv := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [show (CommRingCat.ofHom ((M.overlapRingComm γ' γ :
          (M.overlapRing γ' γ) →+* (M.overlapRing γ γ')).comp
          (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ)))) =
        CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ')) from ?_]
      · apply CommRingCat.hom_ext
        ext a
        exact (Algebra.TensorProduct.comm (Γ(X, ⊤)) (M.cov.obj γ')
          (M.cov.obj γ)).commutes a
    have hS' : φ ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ'))))) =
        Spec.map (CommRingCat.ofHom (algebraMap (M.overlapRing γ γ')
          (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
            (M.localMulticenter γ))))) ≫
          Spec.map (CommRingCat.ofHom
            (M.overlapRingComm γ' γ : (M.overlapRing γ' γ) →+* (M.overlapRing γ γ'))) := by
      rw [← cancel_mono (Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ))) ≫ X.isoSpec.inv)]
      calc (φ ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.overlapRing γ' γ) _))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ))) ≫
              X.isoSpec.inv
          = φ ≫ Spec.map (CommRingCat.ofHom ((algebraMap (M.overlapRing γ' γ)
              (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
                (M.localMulticenter γ')))).comp
              (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ)))) ≫ X.isoSpec.inv := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
            simp only [Category.assoc]
        _ = Spec.map (CommRingCat.ofHom ((algebraMap (M.overlapRing γ γ')
              (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
                (M.localMulticenter γ)))).comp
              (algebraMap (Γ(X, ⊤)) (M.overlapRing γ γ')))) ≫ X.isoSpec.inv := hover
        _ = (Spec.map (CommRingCat.ofHom (algebraMap (M.overlapRing γ γ') _)) ≫
              Spec.map (CommRingCat.ofHom
                (M.overlapRingComm γ' γ : (M.overlapRing γ' γ) →+* (M.overlapRing γ γ')))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, ⊤)) (M.overlapRing γ' γ))) ≫
                X.isoSpec.inv := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
            simp only [Category.assoc]
            congr 1
            exact hAA.symm
    -- ring-level S'-algebra hom from φ
    have hring : CommRingCat.ofHom (algebraMap (M.overlapRing γ' γ)
        (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ' γ)
          (M.localMulticenter γ')))) ≫ ρ =
        CommRingCat.ofHom ((algebraMap (M.overlapRing γ γ')
          (Multicenter.Dilatation (Multicenter.image_mult (B := M.overlapRing γ γ')
            (M.localMulticenter γ)))).comp
          (M.overlapRingComm γ' γ : (M.overlapRing γ' γ) →+* (M.overlapRing γ γ'))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hρ, Spec.map_preimage]
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact hS'
    refine ⟨{ toRingHom := ρ.hom, commutes' := fun s => ?_ }, ?_⟩
    · exact congrArg (fun t => (CommRingCat.Hom.hom t) s) hring
    · rw [show Spec.map (CommRingCat.ofHom ρ.hom) = φ from by
        rw [CommRingCat.ofHom_hom, hρ, Spec.map_preimage]]
      rw [hφ]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  obtain ⟨χf, hχf⟩ := main f hf
  obtain ⟨χg, hχg⟩ := main g hg
  have : χf = χg := Multicenter.lemma_exists_unique_morphism'
    (Multicenter.image_mult (B := M.overlapRing γ' γ) (M.localMulticenter γ'))
    (fun i => M.swap_nonzerodiv γ' γ i) (fun i => M.swap_gen γ' γ i) χf χg
  rw [hχf, hχg, this]

/-- THE comparison theorem: there is a unique isomorphism of the two overlaps commuting
with the structure maps to the base. -/
theorem overlap_comparison (γ γ' : M.cov.J) :
    ∃! e : M.overlap γ γ' ≅ M.overlap γ' γ,
      e.hom ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ' :=
  ⟨M.overlapSwapIso γ γ', M.overlapSwapIso_toBase γ γ', fun e he =>
    Iso.ext (M.overlap_hom_unique e.hom (M.overlapSwapIso γ γ').hom he
      (M.overlapSwapIso_toBase γ γ'))⟩

noncomputable def overlapIso (γ γ' : M.cov.J) : M.overlap γ γ' ≅ M.overlap γ' γ :=
  M.overlapSwapIso γ γ'

theorem overlapIso_over (γ γ' : M.cov.J) :
    (M.overlapIso γ γ').hom ≫ M.overlapToBase γ' γ = M.overlapToBase γ γ' :=
  M.overlapSwapIso_toBase γ γ'

/-- The map from the triple-overlap piece into the `(γ', δ)`-overlap: first factor
transported through the swap, second factor kept. -/
noncomputable def overlapTriple (γ γ' δ : M.cov.J) :
    pullback (M.overlapFst γ γ') (M.overlapFst γ δ) ⟶ M.overlap γ' δ :=
  pullback.lift
    (pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ (M.overlapIso γ γ').hom ≫
      M.overlapFst γ' γ)
    (pullback.snd (M.overlapFst γ γ') (M.overlapFst γ δ) ≫
      pullback.snd (M.chartToBase γ) (M.cov.map δ))
    (by
      show _ ≫ (M.overlapIso γ γ').hom ≫ M.overlapFst γ' γ ≫ M.chartToBase γ' = _
      rw [show M.overlapFst γ' γ ≫ M.chartToBase γ' = M.overlapToBase γ' γ from rfl]
      rw [M.overlapIso_over γ γ']
      rw [show M.overlapToBase γ γ' = M.overlapFst γ γ' ≫ M.chartToBase γ from rfl]
      rw [← Category.assoc, pullback.condition (f := M.overlapFst γ γ')
        (g := M.overlapFst γ δ), Category.assoc]
      rw [show M.overlapFst γ δ ≫ M.chartToBase γ = M.overlapToBase γ δ from rfl]
      rw [show M.overlapToBase γ δ =
        pullback.snd (M.chartToBase γ) (M.cov.map δ) ≫ M.cov.map δ from
        pullback.condition (f := M.chartToBase γ) (g := M.cov.map δ)]
      rw [Category.assoc])

@[reassoc]
theorem overlapTriple_fst (γ γ' δ : M.cov.J) :
    M.overlapTriple γ γ' δ ≫ M.overlapFst γ' δ =
      pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ (M.overlapIso γ γ').hom ≫
        M.overlapFst γ' γ := by
  unfold overlapTriple overlapFst
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem overlapTriple_snd (γ γ' δ : M.cov.J) :
    M.overlapTriple γ γ' δ ≫ pullback.snd (M.chartToBase γ') (M.cov.map δ) =
      pullback.snd (M.overlapFst γ γ') (M.overlapFst γ δ) ≫
        pullback.snd (M.chartToBase γ) (M.cov.map δ) := by
  unfold overlapTriple
  exact pullback.lift_snd _ _ _

/-- The transition comparison on triple overlaps, mirroring `Proj_loc_pair_t'`. -/
noncomputable def overlapT' (γ γ' δ : M.cov.J) :
    pullback (M.overlapFst γ γ') (M.overlapFst γ δ) ⟶
      pullback (M.overlapFst γ' δ) (M.overlapFst γ' γ) :=
  pullback.lift (M.overlapTriple γ γ' δ)
    (pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ (M.overlapIso γ γ').hom)
    (by rw [show M.overlapTriple γ γ' δ ≫ M.overlapFst γ' δ = _ from
        M.overlapTriple_fst γ γ' δ, Category.assoc])

@[reassoc]
theorem overlapT'_fst (γ γ' δ : M.cov.J) :
    M.overlapT' γ γ' δ ≫ pullback.fst (M.overlapFst γ' δ) (M.overlapFst γ' γ) =
      M.overlapTriple γ γ' δ := by
  unfold overlapT'
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem overlapT'_snd (γ γ' δ : M.cov.J) :
    M.overlapT' γ γ' δ ≫ pullback.snd (M.overlapFst γ' δ) (M.overlapFst γ' γ) =
      pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ (M.overlapIso γ γ').hom := by
  unfold overlapT'
  exact pullback.lift_snd _ _ _

instance overlap_isAffine (γ γ' : M.cov.J) : IsAffine (M.overlap γ γ') :=
  isAffine_of_isIso (M.overlapSpecIso γ γ').hom

/-- `overlapT'` respects the structure maps to the base. -/
@[reassoc]
theorem overlapT'_toBase (γ γ' δ : M.cov.J) :
    M.overlapT' γ γ' δ ≫ pullback.fst (M.overlapFst γ' δ) (M.overlapFst γ' γ) ≫
      M.overlapToBase γ' δ =
    pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ M.overlapToBase γ γ' := by
  rw [← Category.assoc, M.overlapT'_fst γ γ' δ]
  rw [show M.overlapToBase γ' δ = M.overlapFst γ' δ ≫ M.chartToBase γ' from rfl]
  rw [← Category.assoc, M.overlapTriple_fst γ γ' δ]
  simp only [Category.assoc]
  rw [show M.overlapFst γ' γ ≫ M.chartToBase γ' = M.overlapToBase γ' γ from rfl]
  rw [M.overlapIso_over γ γ']

/-- The cocycle identity for the transition maps, by the uniqueness half of the
dilatation universal property: the triple composite and the identity agree after
composing with the (monic) open immersion to the `γ`-chart, since both are maps of
the triple overlap over `Spec R_γ` and the triple-overlap ring inherits the
nonzerodivisor/generation conditions along the flat open immersion. -/
theorem overlapT'_cocycle (γ γ' δ : M.cov.J) :
    M.overlapT' γ γ' δ ≫ M.overlapT' γ' δ γ ≫ M.overlapT' δ γ γ' = 𝟙 _ := by
  haveI := M.cov.map_prop γ
  set P := pullback (M.overlapFst γ γ') (M.overlapFst γ δ) with hP
  set m := pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ M.overlapFst γ γ' with hm
  haveI hm_open : IsOpenImmersion m := by
    rw [hm]
    infer_instance
  -- P is affine
  haveI hfstAff : IsAffineHom (M.overlapFst γ δ) := isAffineHom_of_isAffine _
  haveI : IsAffineHom (pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ)) :=
    MorphismProperty.pullback_fst _ _ hfstAff
  haveI hPaff : IsAffine P :=
    isAffine_of_isAffineHom (pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ))
  -- the chain is over the base on the first projection
  have hchainBase : (M.overlapT' γ γ' δ ≫ M.overlapT' γ' δ γ ≫ M.overlapT' δ γ γ') ≫
      pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ M.overlapToBase γ γ' =
      pullback.fst (M.overlapFst γ γ') (M.overlapFst γ δ) ≫ M.overlapToBase γ γ' := by
    simp only [Category.assoc]
    rw [M.overlapT'_toBase δ γ γ', M.overlapT'_toBase γ' δ γ, M.overlapT'_toBase γ γ' δ]
  -- ring-level data for the uniqueness lemma
  set w := Spec.preimage (P.isoSpec.inv ≫ m ≫ M.localChartHom γ) with hwdef
  have hw : Spec.map w = P.isoSpec.inv ≫ m ≫ M.localChartHom γ := Spec.map_preimage _
  set mring := Spec.preimage (P.isoSpec.inv ≫ m) with hmringdef
  have hmring : Spec.map mring = P.isoSpec.inv ≫ m := Spec.map_preimage _
  have hfactor : w = CommRingCat.ofHom (algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ))) ≫ mring := by
    apply Spec.map_injective
    rw [Spec.map_comp, hmring, hw, Category.assoc]
    rfl
  -- flatness of the open piece over the dilatation ring
  letI : Algebra (Multicenter.Dilatation (M.localMulticenter γ)) Γ(P, ⊤) :=
    mring.hom.toAlgebra
  haveI : IsOpenImmersion (Spec Γ(P, ⊤) ↘
      Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)))) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom mring.hom))
    rw [CommRingCat.ofHom_hom, hmring]
    infer_instance
  have hflat : RingHom.Flat (algebraMap (Multicenter.Dilatation (M.localMulticenter γ))
      Γ(P, ⊤)) :=
    open_implies_flat_ring _ _
  -- the two conditions on Γ(P)
  have hnzd : ∀ i, w.hom ((M.localMulticenter γ).elem i) ∈ nonZeroDivisors Γ(P, ⊤) := by
    intro i
    rw [hfactor]
    show mring.hom ((algebraMap (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ)))
      ((M.localMulticenter γ).elem i)) ∈ _
    refine hflat.preserves_nonzeroDivisors ?_
    have h := Multicenter.Dilatation.nonzerodiv_image (F := M.localMulticenter γ)
      (Finsupp.single i 1)
    rwa [familyPow_single] at h
  have hgen : ∀ i, Ideal.span {w.hom ((M.localMulticenter γ).elem i)} =
      Ideal.map w.hom ((M.localMulticenter γ).LargeIdeal i) := by
    intro i
    rw [hfactor]
    show Ideal.span {mring.hom ((algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ))) ((M.localMulticenter γ).elem i))} =
      Ideal.map (mring.hom.comp (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) ((M.localMulticenter γ).LargeIdeal i)
    rw [← Ideal.map_map]
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal (F := M.localMulticenter γ)
      (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single] at h
    rw [← h, Ideal.map_span, Set.image_singleton]
  -- the over-Spec-R_γ compatibilities
  have hv : m ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ)))) = P.isoSpec.hom ≫ Spec.map w := by
    rw [hw, Iso.hom_inv_id_assoc]
    rfl
  have hu : ((M.overlapT' γ γ' δ ≫ M.overlapT' γ' δ γ ≫ M.overlapT' δ γ γ') ≫ m) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) = P.isoSpec.hom ≫ Spec.map w := by
    rw [← hv]
    haveI : Mono (M.cov.map γ) := inferInstance
    rw [← cancel_mono (M.cov.map γ)]
    simp only [Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ)))) ≫ M.cov.map γ =
      M.chartToBase γ from rfl]
    rw [hm]
    simp only [Category.assoc]
    rw [show M.overlapFst γ γ' ≫ M.chartToBase γ = M.overlapToBase γ γ' from rfl]
    have := hchainBase
    simp only [Category.assoc] at this
    exact this
  have key := dila_hom_unique (M.cov.obj γ) (M.localMulticenter γ) w hnzd hgen
    ((M.overlapT' γ γ' δ ≫ M.overlapT' γ' δ γ ≫ M.overlapT' δ γ γ') ≫ m) m hu hv
  rw [← cancel_mono m, Category.id_comp]
  exact key

noncomputable def glueData : Scheme.GlueData where
  J := M.cov.J
  U := M.localChart
  V p := M.overlap p.1 p.2
  f γ γ' := M.overlapFst γ γ'
  f_id γ := by
    show IsIso (M.overlapFst γ γ)
    unfold overlapFst chartToBase
    infer_instance
  f_open γ γ' := M.overlapFst_isOpenImmersion γ γ'
  t γ γ' := (M.overlapIso γ γ').hom
  t_id γ :=
    M.overlap_hom_unique (M.overlapIso γ γ).hom (𝟙 _)
      (M.overlapIso_over γ γ) (Category.id_comp _)
  t' γ γ' δ := M.overlapT' γ γ' δ
  t_fac γ γ' δ := M.overlapT'_snd γ γ' δ
  cocycle γ γ' δ := M.overlapT'_cocycle γ γ' δ

noncomputable def dilatation : Scheme :=
  M.glueData.glued

noncomputable def chartToDilatation (γ : M.cov.J) : M.localChart γ ⟶ M.dilatation :=
  M.glueData.ι γ

instance chartToDilatation_isOpenImmersion (γ : M.cov.J) :
    IsOpenImmersion (M.chartToDilatation γ) := by
  unfold chartToDilatation
  infer_instance

theorem chart_glue_compat (γ γ' : M.cov.J) :
    M.overlapFst γ γ' ≫ M.chartToDilatation γ =
    (M.overlapIso γ γ').hom ≫ M.overlapFst γ' γ ≫ M.chartToDilatation γ' :=
  (M.glueData.glue_condition γ γ').symm

/-- The inverse of the swap is the reverse swap (by uniqueness of the comparison). -/
theorem overlapIso_symm (γ γ' : M.cov.J) :
    M.overlapIso γ γ' = (M.overlapIso γ' γ).symm := by
  refine Iso.ext (M.overlap_hom_unique _ _ (M.overlapIso_over γ γ') ?_)
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact (M.overlapIso_over γ' γ).symm

noncomputable def structure_map : M.dilatation ⟶ X :=
  Multicoequalizer.desc M.glueData.diagram _ (fun γ => M.chartToBase γ) <| by
    rintro ⟨γ, γ'⟩
    change M.overlapFst γ γ' ≫ M.chartToBase γ =
      ((M.overlapIso γ γ').hom ≫ M.overlapFst γ' γ) ≫ M.chartToBase γ'
    rw [Category.assoc]
    exact (M.overlapIso_over γ γ').symm

theorem structure_map_chart (γ : M.cov.J) :
    M.chartToDilatation γ ≫ M.structure_map = M.chartToBase γ :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The preimage of the chart `U_γ` in the glued dilatation is exactly the `γ`-chart:
every point over `U_γ` lies in the image of `ι_γ`, via the gluing. -/
theorem structure_map_range (γ : M.cov.J) (p : M.dilatation)
    (hp : M.structure_map.base p ∈ Set.range (M.cov.map γ).base) :
    p ∈ Set.range (M.chartToDilatation γ).base := by
  obtain ⟨γ', y, hy⟩ := M.glueData.ι_jointly_surjective p
  have hy' : (M.chartToDilatation γ').base y = p := hy
  have hsy : (M.chartToBase γ').base y ∈ Set.range (M.cov.map γ).base := by
    have h := congrArg (fun t : M.localChart γ' ⟶ X => t.base y) (M.structure_map_chart γ')
    simp only [Scheme.comp_base_apply] at h
    rw [← h, hy']
    exact hp
  have hover : y ∈ (M.chartToBase γ').base ⁻¹' Set.range (M.cov.map γ).base := hsy
  rw [← Scheme.Pullback.range_fst] at hover
  obtain ⟨z, hz⟩ := hover
  refine ⟨(M.overlapFst γ γ').base ((M.overlapIso γ' γ).hom.base z), ?_⟩
  have hglue := congrArg (fun t : M.overlap γ' γ ⟶ M.dilatation => t.base z)
    (M.chart_glue_compat γ' γ)
  simp only [Scheme.comp_base_apply] at hglue
  rw [← hy', ← hz]
  exact hglue.symm

theorem structure_map_affine : IsAffineHom M.structure_map := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsAffineHom) M.cov.cover]
  intro γ
  have hcomm : M.chartToDilatation γ ≫ M.structure_map =
      M.localChartHom γ ≫ M.cov.cover.map γ := by
    rw [M.structure_map_chart γ]
    rfl
  haveI hf1 : IsOpenImmersion (M.cov.cover.map γ) := M.cov.cover.map_prop γ
  set k : M.localChart γ ⟶ pullback M.structure_map (M.cov.cover.map γ) :=
    pullback.lift (M.chartToDilatation γ) (M.localChartHom γ) hcomm with hk
  have hkfst : k ≫ pullback.fst M.structure_map (M.cov.cover.map γ) =
    M.chartToDilatation γ := pullback.lift_fst _ _ _
  haveI : IsOpenImmersion (k ≫ pullback.fst M.structure_map (M.cov.cover.map γ)) := by
    rw [hkfst]
    infer_instance
  haveI hkopen : IsOpenImmersion k :=
    IsOpenImmersion.of_comp k (pullback.fst M.structure_map (M.cov.cover.map γ))
  haveI hkepi : Epi k.base := by
    rw [TopCat.epi_iff_surjective]
    intro q
    have hcond : M.structure_map.base
        ((pullback.fst M.structure_map (M.cov.cover.map γ)).base q) ∈
        Set.range (M.cov.map γ).base := by
      refine ⟨(pullback.snd M.structure_map (M.cov.cover.map γ)).base q, ?_⟩
      have h := congrArg (fun t : pullback M.structure_map (M.cov.cover.map γ) ⟶ X =>
        t.base q) (pullback.condition (f := M.structure_map) (g := M.cov.cover.map γ))
      simp only [Scheme.comp_base_apply] at h
      exact h.symm
    obtain ⟨w, hw⟩ := M.structure_map_range γ _ hcond
    refine ⟨w, ?_⟩
    have hinj := (pullback.fst M.structure_map
      (M.cov.cover.map γ)).isOpenEmbedding.injective
    apply hinj
    have hkw := congrArg (fun t : M.localChart γ ⟶ M.dilatation => t.base w) hkfst
    simp only [Scheme.comp_base_apply] at hkw
    rw [hkw, hw]
  haveI : IsIso k := IsOpenImmersion.to_iso k
  show IsAffineHom (pullback.snd M.structure_map (M.cov.cover.map γ))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) k
    (pullback.snd M.structure_map (M.cov.cover.map γ))]
  rw [show k ≫ pullback.snd M.structure_map (M.cov.cover.map γ) =
    M.localChartHom γ from pullback.lift_snd _ _ _]
  infer_instance

/-- The universal property of the dilatation, chart-affine version: an affine scheme
mapping into the chart `U_γ` whose pulled-back elems are nonzerodivisors generating the
pulled `LargeIdeal`s lifts uniquely to the dilatation. Existence is `Multicenter.desc`;
uniqueness factors any competitor through the `γ`-chart via `structure_map_range` and
concludes by `dila_hom_unique`. -/
theorem universal_property_affine_chart (γ : M.cov.J) (T : Scheme.{u+1}) [IsAffine T]
    (w : M.cov.obj γ ⟶ Γ(T, ⊤))
    (hnzd : ∀ i, w.hom ((M.localMulticenter γ).elem i) ∈ nonZeroDivisors Γ(T, ⊤))
    (hgen : ∀ i, Ideal.span {w.hom ((M.localMulticenter γ).elem i)} =
      Ideal.map w.hom ((M.localMulticenter γ).LargeIdeal i)) :
    ∃! g : T ⟶ M.dilatation,
      g ≫ M.structure_map = T.isoSpec.hom ≫ Spec.map w ≫ M.cov.map γ := by
  letI : Algebra (M.cov.obj γ) Γ(T, ⊤) := w.hom.toAlgebra
  set χ := Multicenter.desc (M.localMulticenter γ) hnzd hgen with hχ
  have hχw : CommRingCat.ofHom (algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ))) ≫
      CommRingCat.ofHom χ.toRingHom = w := by
    apply CommRingCat.hom_ext
    ext a
    exact χ.commutes a
  set g₀ : T ⟶ M.localChart γ := T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom χ.toRingHom)
    with hg₀
  have hg₀w : g₀ ≫ M.localChartHom γ = T.isoSpec.hom ≫ Spec.map w := by
    rw [hg₀, Category.assoc]
    rw [show M.localChartHom γ = Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
      (Multicenter.Dilatation (M.localMulticenter γ)))) from rfl]
    rw [← Spec.map_comp, hχw]
  refine ⟨g₀ ≫ M.chartToDilatation γ, ?_, ?_⟩
  · show (g₀ ≫ M.chartToDilatation γ) ≫ M.structure_map =
      T.isoSpec.hom ≫ Spec.map w ≫ M.cov.map γ
    rw [Category.assoc, M.structure_map_chart γ,
      show M.chartToBase γ = M.localChartHom γ ≫ M.cov.map γ from rfl,
      ← Category.assoc, hg₀w, Category.assoc]
  · intro g' hg'
    -- g' factors through the γ-chart
    have hrange : Set.range g'.base ⊆ Set.range (M.chartToDilatation γ).base := by
      rintro _ ⟨t, rfl⟩
      refine M.structure_map_range γ _ ?_
      have h := congrArg (fun u : T ⟶ X => u.base t) hg'
      simp only [Scheme.comp_base_apply] at h
      rw [h]
      exact ⟨(T.isoSpec.hom ≫ Spec.map w).base t, by simp [Scheme.comp_base_apply]⟩
    set g'₀ := IsOpenImmersion.lift (M.chartToDilatation γ) g' hrange with hg'₀
    have hfac : g'₀ ≫ M.chartToDilatation γ = g' := IsOpenImmersion.lift_fac _ _ _
    -- g'₀ agrees with g₀ by uniqueness
    haveI := M.cov.map_prop γ
    haveI : Mono (M.cov.map γ) := inferInstance
    have hstruct : g'₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) =
        T.isoSpec.hom ≫ Spec.map w := by
      rw [← cancel_mono (M.cov.map γ)]
      rw [show Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) = M.localChartHom γ from rfl]
      have h1 : g'₀ ≫ M.localChartHom γ ≫ M.cov.map γ = g'₀ ≫ M.chartToBase γ := rfl
      rw [Category.assoc, h1]
      rw [show M.chartToBase γ = M.chartToDilatation γ ≫ M.structure_map from
        (M.structure_map_chart γ).symm]
      rw [← Category.assoc, hfac, hg']
      rw [Category.assoc]
    have hg₀struct : g₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) =
        T.isoSpec.hom ≫ Spec.map w := hg₀w
    have := dila_hom_unique (M.cov.obj γ) (M.localMulticenter γ) w hnzd hgen
      g'₀ g₀ hstruct hg₀struct
    rw [← hfac, this]

end AffineBase

end PreMultiCenter

namespace MultiCenter

variable (M : MultiCenter X)

/-- The dilatation of a multicenter, via its selected presentation. -/
noncomputable def dilatation [IsAffine X] : Scheme := M.rep.dilatation

/-- The structure morphism of the dilatation of a multicenter. -/
noncomputable def structure_map [IsAffine X] : M.dilatation ⟶ X := M.rep.structure_map

end MultiCenter

end SchemeDilatation
