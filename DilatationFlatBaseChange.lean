import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Basic
import MulticenterRing
import Flat
import PreClosAndClos

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct Multicenter

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

lemma dilatation_ring_flat_base_change (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Algebra A B] (F : Multicenter A) (flat : RingHom.Flat (algebraMap A B)) :
    Subsingleton ((B ⊗[A] A[F]) ≃ₐ[B] B[image_mult F]) := by
  classical
  have h1 : ∀ i : F.index,
      (algebraMap A (B[image_mult (B := B) F])) (F.elem i) ∈ nonZeroDivisors _ := by
    intro i
    have h := Multicenter.Dilatation.nonzerodiv_image
      (F := image_mult (B := B) F) (Finsupp.single i 1)
    simp at h
    exact h
  have h2 : ∀ i : F.index,
      Ideal.span {(algebraMap A (B[image_mult (B := B) F])) (F.elem i)} =
        Ideal.map (algebraMap A (B[image_mult (B := B) F])) (F.LargeIdeal i) := by
    intro i
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
      (F := image_mult (B := B) F) (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single, image_mult_LargeIdeal, Ideal.map_map] at h
    exact h
  letI : IsScalarTower A B (B[image_mult (B := B) F]) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨fun e₁ e₂ => AlgEquiv.ext fun x => ?_⟩
  have key : (((e₁ : (B ⊗[A] A[F]) →ₐ[B] _).restrictScalars A).comp
        (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F])) =
      (((e₂ : (B ⊗[A] A[F]) →ₐ[B] _).restrictScalars A).comp
        (Algebra.TensorProduct.includeRight : A[F] →ₐ[A] B ⊗[A] A[F])) :=
    Multicenter.lemma_exists_unique_morphism' F h1 h2 _ _
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
      have hb : (b ⊗ₜ[A] a : B ⊗[A] A[F]) =
          b • (Algebra.TensorProduct.includeRight a : B ⊗[A] A[F]) := by
        simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul']
      rw [hb, map_smul, map_smul]
      exact congrArg (b • ·) (AlgHom.congr_fun key a)
  | add p q hp hq => simp only [map_add, hp, hq]

instance (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

lemma open_implies_flat_ring (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] : RingHom.Flat (algebraMap A B) := by
  haveI hf : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    inferInstanceAs (AlgebraicGeometry.Flat (Spec B ↘ Spec A))
  have h := (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat)
    (φ := CommRingCat.ofHom (algebraMap A B))).mp hf
  simpa using h

lemma base_change_dil_open (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)]
    (F : Multicenter A) :
    ∃! (e : pullback ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A) ≅
        Spec (CommRingCat.of B[image_mult (B := B) F])),
      Scheme.Hom.IsOver e.hom (Spec B) := by
  have flat : RingHom.Flat (algebraMap A B) := open_implies_flat_ring A B
  haveI subsing : Subsingleton ((B ⊗[A] A[F]) ≃ₐ[B] B[image_mult F]) :=
    dilatation_ring_flat_base_change A B F flat
  let e0 : A[F] ⊗[A] B ≃+* B[image_mult (B := B) F] :=
    (Algebra.TensorProduct.comm A A[F] B).toRingEquiv.trans
      (dilatation_baseChange_equiv A B F flat).toRingEquiv
  let iso2 : Spec (CommRingCat.of (A[F] ⊗[A] B)) ≅
      Spec (CommRingCat.of (B[image_mult (B := B) F])) :=
    (Scheme.Spec.mapIso (e0.toCommRingCatIso.op)).symm
  have hiso2 : iso2.hom = Spec.map (CommRingCat.ofHom e0.symm.toRingHom) := rfl
  let hiso : pullback ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A) ≅
      Spec (CommRingCat.of B[image_mult (B := B) F]) :=
    pullbackSpecIso A A[F] B ≪≫ iso2
  have hover : Scheme.Hom.IsOver hiso.hom (Spec B) := by
    refine ⟨?_⟩
    show hiso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B B[image_mult (B := B) F])) =
      pullback.snd ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A)
    show (pullbackSpecIso A A[F] B).hom ≫ iso2.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B B[image_mult (B := B) F])) = _
    rw [hiso2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show e0.symm.toRingHom.comp (algebraMap B B[image_mult (B := B) F]) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A[F] ⊗[A] B).toRingHom from ?_]
    · exact pullbackSpecIso_hom_snd A A[F] B
    · ext b
      show e0.symm (algebraMap B (B[image_mult (B := B) F]) b) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A[F] ⊗[A] B) b
      have h1 := (dilatation_baseChange_equiv A B F flat).symm.commutes b
      have h2 : e0.symm (algebraMap B (B[image_mult (B := B) F]) b) =
          (Algebra.TensorProduct.comm A A[F] B).symm
            ((dilatation_baseChange_equiv A B F flat).symm
              (algebraMap B (B[image_mult (B := B) F]) b)) := rfl
      rw [h2, h1, show algebraMap B (B ⊗[A] A[F]) b = b ⊗ₜ[A] (1 : A[F]) from rfl,
        Algebra.TensorProduct.comm_symm_tmul]
      rfl
  refine ⟨hiso, hover, ?_⟩
  intro e' he'
  let e'' : Spec (CommRingCat.of (A[F] ⊗[A] B)) ≅
      Spec (CommRingCat.of (B[image_mult (B := B) F])) := (pullbackSpecIso A A[F] B).symm ≪≫ e'
  let ψ1 : CommRingCat.of (B[image_mult (B := B) F]) ⟶ CommRingCat.of (A[F] ⊗[A] B) :=
    Spec.preimage e''.hom
  let ψ2 : CommRingCat.of (A[F] ⊗[A] B) ⟶ CommRingCat.of (B[image_mult (B := B) F]) :=
    Spec.preimage e''.inv
  have hmap1 : Spec.map ψ1 = e''.hom := Spec.map_preimage e''.hom
  have hmap2 : Spec.map ψ2 = e''.inv := Spec.map_preimage e''.inv
  have hid1 : ψ1 ≫ ψ2 = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hmap1, hmap2, Spec.map_id, Iso.inv_hom_id])
  have hid2 : ψ2 ≫ ψ1 = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hmap1, hmap2, Spec.map_id, Iso.hom_inv_id])
  let ρ : CommRingCat.of (B[image_mult (B := B) F]) ≅ CommRingCat.of (A[F] ⊗[A] B) :=
    ⟨ψ1, ψ2, hid1, hid2⟩
  let ρequiv : B[image_mult (B := B) F] ≃+* (A[F] ⊗[A] B) := ρ.commRingCatIsoToRingEquiv
  have hρalg : ∀ b : B, ρequiv (algebraMap B (B[image_mult (B := B) F]) b) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A[F] ⊗[A] B) b := by
    intro b
    have hcompat : e''.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B B[image_mult (B := B) F])) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[A] A[F] ⊗[A] B).toRingHom) := by
      show (pullbackSpecIso A A[F] B).inv ≫ e'.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B B[image_mult (B := B) F])) = _
      have he'1 : e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B B[image_mult (B := B) F])) =
          pullback.snd ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A) := he'.1
      rw [he'1]
      exact pullbackSpecIso_inv_snd A A[F] B
    rw [← hmap1] at hcompat
    simp only [← Spec.map_comp] at hcompat
    have hring := Spec.map_injective hcompat
    simp only [← CommRingCat.ofHom_comp] at hring
    have hring' := congrArg (CommRingCat.Hom.hom ·) hring
    simp only [CommRingCat.ofHom_hom] at hring'
    exact congrFun (congrArg DFunLike.coe hring') b
  let ρalg : (B ⊗[A] A[F]) ≃ₐ[B] B[image_mult (B := B) F] :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A A[F] B).toRingEquiv.symm.trans
      ρequiv.symm) (fun x => by
      show ρequiv.symm ((Algebra.TensorProduct.comm A A[F] B).symm
        (algebraMap B (B ⊗[A] A[F]) x)) = algebraMap B (B[image_mult (B := B) F]) x
      rw [show algebraMap B (B ⊗[A] A[F]) x = x ⊗ₜ[A] (1 : A[F]) from rfl,
        Algebra.TensorProduct.comm_symm_tmul]
      have h := congrArg ρequiv.symm (hρalg x)
      rw [RingEquiv.symm_apply_apply] at h
      exact h.symm)
  have huniq : ρalg = dilatation_baseChange_equiv A B F flat := subsing.elim _ _
  have hρequiv_symm : ρequiv.symm = e0 := by
    ext z
    have hz : ρequiv.symm ((Algebra.TensorProduct.comm A A[F] B).toRingEquiv.symm
        ((Algebra.TensorProduct.comm A A[F] B).toRingEquiv z)) =
        (dilatation_baseChange_equiv A B F flat)
          ((Algebra.TensorProduct.comm A A[F] B).toRingEquiv z) :=
      congrFun (congrArg DFunLike.coe huniq) ((Algebra.TensorProduct.comm A A[F] B).toRingEquiv z)
    rwa [RingEquiv.symm_apply_apply] at hz
  have hρhom : ρ.hom = CommRingCat.ofHom e0.symm.toRingHom := by
    have hre : ρequiv = e0.symm := by rw [← hρequiv_symm, RingEquiv.symm_symm]
    apply CommRingCat.hom_ext
    ext x
    exact congrFun (congrArg DFunLike.coe hre) x
  have he''hom : e''.hom = iso2.hom := by
    rw [show e''.hom = Spec.map ρ.hom from hmap1.symm, hρhom, hiso2]
  have : e'.hom = hiso.hom := by
    have h1 : (pullbackSpecIso A A[F] B).inv ≫ e'.hom =
        (pullbackSpecIso A A[F] B).inv ≫ hiso.hom := by
      show e''.hom = (pullbackSpecIso A A[F] B).inv ≫ (pullbackSpecIso A A[F] B).hom ≫ iso2.hom
      rw [Iso.inv_hom_id_assoc, he''hom]
    exact (cancel_epi (pullbackSpecIso A A[F] B).inv).mp h1
  exact Iso.ext this
