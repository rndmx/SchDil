import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import PreMultiCenter
import MultiCenter

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

instance schemeOverOfAlgebra' (A B : CommRingCat) [Algebra A B] :
    Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

lemma open_flat_ring (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] : RingHom.Flat (algebraMap A B) := by
  haveI hf : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    inferInstanceAs (AlgebraicGeometry.Flat (Spec B ↘ Spec A))
  have h := (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat)
    (φ := CommRingCat.ofHom (algebraMap A B))).mp hf
  simpa using h

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

theorem dilaUniqueAffine (A : CommRingCat.{u+1}) (F : Multicenter A) {T : Scheme.{u+1}}
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
      rw [Spec.map_comp, hρ, Spec.map_preimage, Category.assoc, ht, Iso.inv_hom_id_assoc]
    refine ⟨{ toRingHom := ρ.hom, commutes' := fun a => ?_ }, ?_⟩
    · exact congrArg (fun f => (CommRingCat.Hom.hom f) a) hcomm
    · rw [show Spec.map (CommRingCat.ofHom ρ.hom) = T.isoSpec.inv ≫ t from by
        rw [CommRingCat.ofHom_hom, hρ, Spec.map_preimage], Iso.hom_inv_id_assoc]
  obtain ⟨χu, hχu⟩ := key u hu
  obtain ⟨χv, hχv⟩ := key v hv
  have : χu = χv := Multicenter.lemma_exists_unique_morphism' F hnzd hgen χu χv
  rw [hχu, hχv, this]

theorem dilaUnique (A : CommRingCat.{u+1}) (F : Multicenter A) {P : Scheme.{u+1}}
    (m : P ⟶ Spec (CommRingCat.of (Multicenter.Dilatation F))) [IsOpenImmersion m]
    (f g : P ⟶ Spec (CommRingCat.of (Multicenter.Dilatation F)))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) =
      m ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) =
      m ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F)))) :
    f = g := by
  refine P.affineCover.hom_ext f g fun j => ?_
  set U := P.affineCover.obj j
  set ι := P.affineCover.map j
  haveI : IsOpenImmersion (ι ≫ m) := inferInstance

  set mr := Spec.preimage (U.isoSpec.inv ≫ ι ≫ m) with hmr
  have hmr_eq : Spec.map mr = U.isoSpec.inv ≫ ι ≫ m := Spec.map_preimage _
  letI : Algebra (Multicenter.Dilatation F) Γ(U, ⊤) := mr.hom.toAlgebra
  haveI : IsOpenImmersion
      (Spec Γ(U, ⊤) ↘ Spec (CommRingCat.of (Multicenter.Dilatation F))) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom mr.hom))
    rw [CommRingCat.ofHom_hom, hmr_eq]
    infer_instance
  have hflat : RingHom.Flat (algebraMap (Multicenter.Dilatation F) Γ(U, ⊤)) :=
    open_flat_ring _ _

  set w : A ⟶ Γ(U, ⊤) :=
    CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F)) ≫ mr with hw
  have hnzd : ∀ i, w.hom (F.elem i) ∈ nonZeroDivisors Γ(U, ⊤) := by
    intro i
    show mr.hom ((algebraMap A (Multicenter.Dilatation F)) (F.elem i)) ∈ _
    refine hflat.preserves_nonzeroDivisors ?_
    have h := Multicenter.Dilatation.nonzerodiv_image (F := F) (Finsupp.single i 1)
    rwa [familyPow_single] at h
  have hgen : ∀ i, Ideal.span {w.hom (F.elem i)} = Ideal.map w.hom (F.LargeIdeal i) := by
    intro i
    show Ideal.span {mr.hom ((algebraMap A (Multicenter.Dilatation F)) (F.elem i))} =
      Ideal.map (mr.hom.comp (algebraMap A (Multicenter.Dilatation F))) (F.LargeIdeal i)
    rw [← Ideal.map_map]
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal (F := F)
      (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single] at h
    rw [← h, Ideal.map_span, Set.image_singleton]

  have hbase : U.isoSpec.hom ≫ Spec.map w =
      ι ≫ m ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Multicenter.Dilatation F))) := by
    rw [hw, Spec.map_comp, ← Category.assoc, hmr_eq]
    simp
  refine dilaUniqueAffine A F w hnzd hgen _ _ ?_ ?_
  · rw [Category.assoc, hf, hbase]
  · rw [Category.assoc, hg, hbase]

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

namespace PreMultiCenter

variable (M : PreMultiCenter X)

def chart (γ : M.cov.J) : Scheme :=
  Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)))

instance chart_isAffine (γ : M.cov.J) : IsAffine (M.chart γ) := by
  unfold chart; infer_instance

def chartHom (γ : M.cov.J) : M.chart γ ⟶ Spec (M.cov.obj γ) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ))))

def chartToX (γ : M.cov.J) : M.chart γ ⟶ X := M.chartHom γ ≫ M.cov.map γ

def overlap (γ γ' : M.cov.J) : Scheme := pullback (M.chartToX γ) (M.cov.map γ')

def ovFst (γ γ' : M.cov.J) : M.overlap γ γ' ⟶ M.chart γ := pullback.fst _ _

instance ovFst_isOpenImmersion (γ γ' : M.cov.J) : IsOpenImmersion (M.ovFst γ γ') := by
  unfold ovFst; infer_instance

def ovToX (γ γ' : M.cov.J) : M.overlap γ γ' ⟶ X := M.ovFst γ γ' ≫ M.chartToX γ

theorem overlapCond (γ γ' : M.cov.J) {W : Scheme.{u+1}} [IsAffine W]
    (m : W ⟶ M.overlap γ γ') [IsOpenImmersion m] :
    (∀ i, (Spec.preimage (W.isoSpec.inv ≫ m ≫
        pullback.snd (M.chartToX γ) (M.cov.map γ'))).hom
        ((M.localMulticenter γ').elem i) ∈ nonZeroDivisors Γ(W, ⊤)) ∧
    (∀ i, Ideal.span {(Spec.preimage (W.isoSpec.inv ≫ m ≫
        pullback.snd (M.chartToX γ) (M.cov.map γ'))).hom
        ((M.localMulticenter γ').elem i)} =
      Ideal.map (Spec.preimage (W.isoSpec.inv ≫ m ≫
        pullback.snd (M.chartToX γ) (M.cov.map γ'))).hom
        ((M.localMulticenter γ').LargeIdeal i)) := by
  classical
  set A : W ⟶ Spec (M.cov.obj γ) := m ≫ M.ovFst γ γ' ≫ M.chartHom γ with hA
  set B : W ⟶ Spec (M.cov.obj γ') := m ≫ pullback.snd (M.chartToX γ) (M.cov.map γ')
    with hB
  set b := Spec.preimage (W.isoSpec.inv ≫ B) with hbdef
  set a := Spec.preimage (W.isoSpec.inv ≫ A) with hadef

  have hab : A ≫ M.cov.map γ = B ≫ M.cov.map γ' := by
    have h : M.ovFst γ γ' ≫ M.chartToX γ =
        pullback.snd (M.chartToX γ) (M.cov.map γ') ≫ M.cov.map γ' := pullback.condition
    rw [hA, hB, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (fun t => m ≫ t) h

  have hY := chartIdeal_agree M.Yrep A B hab
  have hD := chartIdeal_agree M.Drep A B hab

  set mγ := Spec.preimage (W.isoSpec.inv ≫ m ≫ M.ovFst γ γ') with hmγ
  have hmγ_eq : Spec.map mγ = W.isoSpec.inv ≫ m ≫ M.ovFst γ γ' := Spec.map_preimage _
  letI : Algebra (Multicenter.Dilatation (M.localMulticenter γ)) Γ(W, ⊤) := mγ.hom.toAlgebra
  haveI : IsOpenImmersion (Spec Γ(W, ⊤) ↘
      Spec (CommRingCat.of (Multicenter.Dilatation (M.localMulticenter γ)))) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom mγ.hom))
    rw [CommRingCat.ofHom_hom, hmγ_eq]
    haveI : IsOpenImmersion (m ≫ M.ovFst γ γ') := inferInstance
    infer_instance
  have hflat : RingHom.Flat
      (algebraMap (Multicenter.Dilatation (M.localMulticenter γ)) Γ(W, ⊤)) :=
    open_flat_ring _ _
  have ha_eq : a = CommRingCat.ofHom
      (algebraMap (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ))) ≫ mγ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hmγ_eq, hadef, Spec.map_preimage, hA, Category.assoc]
    rfl
  have hanzd : ∀ i, a.hom ((M.localMulticenter γ).elem i) ∈ nonZeroDivisors Γ(W, ⊤) := by
    intro i
    rw [ha_eq]
    show mγ.hom ((algebraMap (M.cov.obj γ) (Multicenter.Dilatation (M.localMulticenter γ)))
      ((M.localMulticenter γ).elem i)) ∈ _
    refine hflat.preserves_nonzeroDivisors ?_
    have h := Multicenter.Dilatation.nonzerodiv_image (F := M.localMulticenter γ)
      (Finsupp.single i 1)
    rwa [familyPow_single] at h
  have hagen : ∀ i, Ideal.span {a.hom ((M.localMulticenter γ).elem i)} =
      Ideal.map a.hom ((M.localMulticenter γ).LargeIdeal i) := by
    intro i
    rw [ha_eq]
    show Ideal.span {mγ.hom ((algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ))) ((M.localMulticenter γ).elem i))} =
      Ideal.map (mγ.hom.comp (algebraMap (M.cov.obj γ)
        (Multicenter.Dilatation (M.localMulticenter γ)))) ((M.localMulticenter γ).LargeIdeal i)
    rw [← Ideal.map_map]
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal (F := M.localMulticenter γ)
      (Finsupp.single i 1)
    rw [familyPow_single, familyPow_single] at h
    rw [← h, Ideal.map_span, Set.image_singleton]

  have hspan : ∀ i, Ideal.span {b.hom ((M.localMulticenter γ').elem i)} =
      Ideal.span {a.hom ((M.localMulticenter γ).elem i)} := by
    intro i
    letI := M.Dprin i γ
    letI := M.Dprin i γ'
    have e1 : Ideal.span {a.hom ((M.localMulticenter γ).elem i)} =
        Ideal.map a.hom (M.Drep.ideal i γ) := by
      rw [← Set.image_singleton, ← Ideal.map_span]
      exact congrArg _ (Ideal.span_singleton_generator _)
    have e2 : Ideal.span {b.hom ((M.localMulticenter γ').elem i)} =
        Ideal.map b.hom (M.Drep.ideal i γ') := by
      rw [← Set.image_singleton, ← Ideal.map_span]
      exact congrArg _ (Ideal.span_singleton_generator _)
    rw [e1, e2, ← hD i]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact nonZeroDivisors_of_span_singleton_eq (hspan i) (hanzd i)
  ·
    have hL : Ideal.map b.hom ((M.localMulticenter γ').LargeIdeal i) =
        Ideal.map a.hom ((M.localMulticenter γ).LargeIdeal i) := by
      unfold Multicenter.LargeIdeal
      rw [Submodule.add_eq_sup, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_sup]
      congr 1
      · exact (hY i).symm
      · rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
        exact hspan i
    rw [hL, hspan i, hagen i]

theorem homUnique {γ γ' : M.cov.J} (f g : M.overlap γ γ' ⟶ M.overlap γ' γ)
    (hf : f ≫ M.ovToX γ' γ = M.ovToX γ γ') (hg : g ≫ M.ovToX γ' γ = M.ovToX γ γ') :
    f = g := by
  haveI := M.cov.map_prop γ
  haveI := M.cov.map_prop γ'
  haveI : Mono (M.cov.map γ) := inferInstance
  haveI : Mono (M.cov.map γ') := inferInstance

  have hleg : ∀ h : M.overlap γ γ' ⟶ M.overlap γ' γ,
      h ≫ M.ovToX γ' γ = M.ovToX γ γ' →
      h ≫ M.ovFst γ' γ ≫ M.chartHom γ' =
        pullback.snd (M.chartToX γ) (M.cov.map γ') := by
    intro h hh
    rw [← cancel_mono (M.cov.map γ'), Category.assoc, Category.assoc]
    show h ≫ M.ovToX γ' γ = _
    rw [hh]
    exact pullback.condition

  have hfst : f ≫ M.ovFst γ' γ = g ≫ M.ovFst γ' γ := by
    refine (M.overlap γ γ').affineCover.hom_ext _ _ fun j => ?_
    set mW := (M.overlap γ γ').affineCover.map j with hmW
    obtain ⟨hnzd, hgen⟩ := M.overlapCond γ γ' mW
    refine dilaUniqueAffine (M.cov.obj γ') (M.localMulticenter γ') _ hnzd hgen _ _ ?_ ?_
    · show (mW ≫ f ≫ M.ovFst γ' γ) ≫ M.chartHom γ' = _
      rw [Category.assoc, Category.assoc, hleg f hf, Spec.map_preimage,
        Iso.hom_inv_id_assoc]
    · show (mW ≫ g ≫ M.ovFst γ' γ) ≫ M.chartHom γ' = _
      rw [Category.assoc, Category.assoc, hleg g hg, Spec.map_preimage,
        Iso.hom_inv_id_assoc]

  have hsnd : f ≫ pullback.snd (M.chartToX γ') (M.cov.map γ) =
      g ≫ pullback.snd (M.chartToX γ') (M.cov.map γ) := by
    rw [← cancel_mono (M.cov.map γ), Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc, ← Category.assoc]
    show (f ≫ M.ovFst γ' γ) ≫ M.chartToX γ' = (g ≫ M.ovFst γ' γ) ≫ M.chartToX γ'
    rw [hfst]
  exact pullback.hom_ext hfst hsnd

theorem tripleUnique {γ γ' δ : M.cov.J}
    (f g : pullback (M.ovFst γ γ') (M.ovFst γ δ) ⟶ M.chart γ)
    (hf : f ≫ M.chartToX γ = pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovToX γ γ')
    (hg : g ≫ M.chartToX γ = pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovToX γ γ') :
    f = g := by
  haveI := M.cov.map_prop γ
  haveI : Mono (M.cov.map γ) := inferInstance
  set m := pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovFst γ γ' with hm
  haveI : IsOpenImmersion m := by rw [hm]; infer_instance
  have hmX : m ≫ M.chartToX γ =
      pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovToX γ γ' := by
    rw [hm, Category.assoc]; rfl
  refine dilaUnique (M.cov.obj γ) (M.localMulticenter γ) m f g ?_ ?_
  · show f ≫ M.chartHom γ = m ≫ M.chartHom γ
    rw [← cancel_mono (M.cov.map γ), Category.assoc, Category.assoc]
    show f ≫ M.chartToX γ = m ≫ M.chartToX γ
    rw [hf, hmX]
  · show g ≫ M.chartHom γ = m ≫ M.chartHom γ
    rw [← cancel_mono (M.cov.map γ), Category.assoc, Category.assoc]
    show g ≫ M.chartToX γ = m ≫ M.chartToX γ
    rw [hg, hmX]

theorem selfUnique {γ γ' : M.cov.J} (f g : M.overlap γ γ' ⟶ M.overlap γ γ')
    (hf : f ≫ M.ovToX γ γ' = M.ovToX γ γ') (hg : g ≫ M.ovToX γ γ' = M.ovToX γ γ') :
    f = g := by
  haveI := M.cov.map_prop γ
  haveI := M.cov.map_prop γ'
  haveI : Mono (M.cov.map γ) := inferInstance
  haveI : Mono (M.cov.map γ') := inferInstance
  have hfst : f ≫ M.ovFst γ γ' = g ≫ M.ovFst γ γ' := by
    refine dilaUnique (M.cov.obj γ) (M.localMulticenter γ) (M.ovFst γ γ') _ _ ?_ ?_
    · show (f ≫ M.ovFst γ γ') ≫ M.chartHom γ = M.ovFst γ γ' ≫ M.chartHom γ
      rw [← cancel_mono (M.cov.map γ), Category.assoc, Category.assoc]
      show (f ≫ M.ovFst γ γ') ≫ M.chartToX γ = M.ovFst γ γ' ≫ M.chartToX γ
      rw [Category.assoc]; exact hf
    · show (g ≫ M.ovFst γ γ') ≫ M.chartHom γ = M.ovFst γ γ' ≫ M.chartHom γ
      rw [← cancel_mono (M.cov.map γ), Category.assoc, Category.assoc]
      show (g ≫ M.ovFst γ γ') ≫ M.chartToX γ = M.ovFst γ γ' ≫ M.chartToX γ
      rw [Category.assoc]; exact hg
  have hsnd : f ≫ pullback.snd (M.chartToX γ) (M.cov.map γ') =
      g ≫ pullback.snd (M.chartToX γ) (M.cov.map γ') := by
    rw [← cancel_mono (M.cov.map γ'), Category.assoc, Category.assoc,
      ← pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ M.chartToX γ) hfst
  exact pullback.hom_ext hfst hsnd

theorem legUnique (γ γ' : M.cov.J) {Q : Scheme.{u+1}} (n : Q ⟶ M.overlap γ γ')
    [IsOpenImmersion n] (u v : Q ⟶ M.chart γ')
    (hu : u ≫ M.chartHom γ' = n ≫ pullback.snd (M.chartToX γ) (M.cov.map γ'))
    (hv : v ≫ M.chartHom γ' = n ≫ pullback.snd (M.chartToX γ) (M.cov.map γ')) : u = v := by
  refine Q.affineCover.hom_ext u v fun j => ?_
  haveI : IsOpenImmersion (Q.affineCover.map j ≫ n) := inferInstance
  obtain ⟨hnzd, hgen⟩ := M.overlapCond γ γ' (Q.affineCover.map j ≫ n)
  refine dilaUniqueAffine (M.cov.obj γ') (M.localMulticenter γ') _ hnzd hgen _ _ ?_ ?_
  · show (Q.affineCover.map j ≫ u) ≫ M.chartHom γ' = _
    rw [Category.assoc, hu, Spec.map_preimage, Iso.hom_inv_id_assoc, ← Category.assoc]
  · show (Q.affineCover.map j ≫ v) ≫ M.chartHom γ' = _
    rw [Category.assoc, hv, Spec.map_preimage, Iso.hom_inv_id_assoc, ← Category.assoc]

theorem legExists (γ γ' : M.cov.J) :
    ∃ leg : M.overlap γ γ' ⟶ M.chart γ',
      leg ≫ M.chartHom γ' = pullback.snd (M.chartToX γ) (M.cov.map γ') := by
  classical
  set 𝒰 := (M.overlap γ γ').affineCover with h𝒰

  have hloc : ∀ j : 𝒰.J, ∃ l : 𝒰.obj j ⟶ M.chart γ',
      l ≫ M.chartHom γ' = 𝒰.map j ≫ pullback.snd (M.chartToX γ) (M.cov.map γ') := by
    intro j
    obtain ⟨hnzd, hgen⟩ := M.overlapCond γ γ' (𝒰.map j)
    letI : Algebra (M.cov.obj γ') Γ(𝒰.obj j, ⊤) :=
      (Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫
        pullback.snd (M.chartToX γ) (M.cov.map γ'))).hom.toAlgebra
    refine ⟨(𝒰.obj j).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (Multicenter.desc (M.localMulticenter γ') hnzd hgen).toRingHom), ?_⟩
    show _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (M.cov.obj γ')
      (Multicenter.Dilatation (M.localMulticenter γ')))) = _
    rw [Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom (algebraMap (M.cov.obj γ')
        (Multicenter.Dilatation (M.localMulticenter γ'))) ≫ CommRingCat.ofHom
        (Multicenter.desc (M.localMulticenter γ') hnzd hgen).toRingHom =
        Spec.preimage ((𝒰.obj j).isoSpec.inv ≫ 𝒰.map j ≫
          pullback.snd (M.chartToX γ) (M.cov.map γ')) from by
      apply CommRingCat.hom_ext; ext a
      exact (Multicenter.desc (M.localMulticenter γ') hnzd hgen).commutes a]
    rw [Spec.map_preimage, Iso.hom_inv_id_assoc]
  choose l hl using hloc

  have hcompat : ∀ j k, pullback.fst (𝒰.map j) (𝒰.map k) ≫ l j =
      pullback.snd (𝒰.map j) (𝒰.map k) ≫ l k := by
    intro j k
    haveI : IsOpenImmersion (pullback.fst (𝒰.map j) (𝒰.map k) ≫ 𝒰.map j) := inferInstance
    refine M.legUnique γ γ' (pullback.fst (𝒰.map j) (𝒰.map k) ≫ 𝒰.map j) _ _ ?_ ?_
    · rw [Category.assoc, hl j, ← Category.assoc]
    · rw [Category.assoc, hl k, ← Category.assoc, ← pullback.condition, Category.assoc]
  refine ⟨𝒰.glueMorphisms l hcompat, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, 𝒰.ι_glueMorphisms l hcompat j, hl j]

theorem comparison (γ γ' : M.cov.J) :
    ∃! e : M.overlap γ γ' ≅ M.overlap γ' γ, e.hom ≫ M.ovToX γ' γ = M.ovToX γ γ' := by

  have key : ∀ a b : M.cov.J, ∃ e : M.overlap a b ⟶ M.overlap b a,
      e ≫ M.ovToX b a = M.ovToX a b := by
    intro a b
    obtain ⟨leg, hleg⟩ := M.legExists a b
    have hcond : leg ≫ M.chartToX b =
        (M.ovFst a b ≫ M.chartHom a) ≫ M.cov.map a := by
      show leg ≫ M.chartHom b ≫ M.cov.map b = _
      rw [← Category.assoc, hleg, ← pullback.condition, Category.assoc]
      rfl
    refine ⟨pullback.lift leg (M.ovFst a b ≫ M.chartHom a) hcond, ?_⟩
    have hlf : pullback.lift leg (M.ovFst a b ≫ M.chartHom a) hcond ≫ M.ovFst b a = leg :=
      pullback.lift_fst _ _ _
    show pullback.lift leg (M.ovFst a b ≫ M.chartHom a) hcond ≫
      M.ovFst b a ≫ M.chartToX b = M.ovFst a b ≫ M.chartToX a
    rw [← Category.assoc, hlf, hcond, Category.assoc]
    rfl
  obtain ⟨e, he⟩ := key γ γ'
  obtain ⟨e', he'⟩ := key γ' γ
  have h1 : e ≫ e' = 𝟙 _ :=
    M.selfUnique _ _ (by rw [Category.assoc, he', he]) (Category.id_comp _)
  have h2 : e' ≫ e = 𝟙 _ :=
    M.selfUnique _ _ (by rw [Category.assoc, he, he']) (Category.id_comp _)
  exact ⟨⟨e, e', h1, h2⟩, he, fun E hE => Iso.ext (M.homUnique E.hom e hE he)⟩

def ovIso (γ γ' : M.cov.J) : M.overlap γ γ' ≅ M.overlap γ' γ := (M.comparison γ γ').choose

theorem ovIso_over (γ γ' : M.cov.J) :
    (M.ovIso γ γ').hom ≫ M.ovToX γ' γ = M.ovToX γ γ' := (M.comparison γ γ').choose_spec.1

def triple (γ γ' δ : M.cov.J) :
    pullback (M.ovFst γ γ') (M.ovFst γ δ) ⟶ M.overlap γ' δ :=
  pullback.lift
    (pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ (M.ovIso γ γ').hom ≫ M.ovFst γ' γ)
    (pullback.snd (M.ovFst γ γ') (M.ovFst γ δ) ≫
      pullback.snd (M.chartToX γ) (M.cov.map δ))
    (by
      show _ ≫ (M.ovIso γ γ').hom ≫ M.ovFst γ' γ ≫ M.chartToX γ' = _
      rw [show M.ovFst γ' γ ≫ M.chartToX γ' = M.ovToX γ' γ from rfl, M.ovIso_over γ γ',
        show M.ovToX γ γ' = M.ovFst γ γ' ≫ M.chartToX γ from rfl, ← Category.assoc,
        pullback.condition (f := M.ovFst γ γ') (g := M.ovFst γ δ), Category.assoc,
        show M.ovFst γ δ ≫ M.chartToX γ = M.ovToX γ δ from rfl,
        show M.ovToX γ δ = pullback.snd (M.chartToX γ) (M.cov.map δ) ≫ M.cov.map δ from
          pullback.condition (f := M.chartToX γ) (g := M.cov.map δ), Category.assoc])

@[reassoc]
theorem triple_fst (γ γ' δ : M.cov.J) :
    M.triple γ γ' δ ≫ M.ovFst γ' δ =
      pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ (M.ovIso γ γ').hom ≫ M.ovFst γ' γ := by
  unfold triple ovFst; exact pullback.lift_fst _ _ _

def tPrime (γ γ' δ : M.cov.J) :
    pullback (M.ovFst γ γ') (M.ovFst γ δ) ⟶ pullback (M.ovFst γ' δ) (M.ovFst γ' γ) :=
  pullback.lift (M.triple γ γ' δ)
    (pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ (M.ovIso γ γ').hom)
    (by rw [show M.triple γ γ' δ ≫ M.ovFst γ' δ = _ from M.triple_fst γ γ' δ, Category.assoc])

@[reassoc]
theorem tPrime_fst (γ γ' δ : M.cov.J) :
    M.tPrime γ γ' δ ≫ pullback.fst (M.ovFst γ' δ) (M.ovFst γ' γ) = M.triple γ γ' δ := by
  unfold tPrime; exact pullback.lift_fst _ _ _

@[reassoc]
theorem tPrime_snd (γ γ' δ : M.cov.J) :
    M.tPrime γ γ' δ ≫ pullback.snd (M.ovFst γ' δ) (M.ovFst γ' γ) =
      pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ (M.ovIso γ γ').hom := by
  unfold tPrime; exact pullback.lift_snd _ _ _

@[reassoc]
theorem tPrime_toX (γ γ' δ : M.cov.J) :
    M.tPrime γ γ' δ ≫ pullback.fst (M.ovFst γ' δ) (M.ovFst γ' γ) ≫ M.ovToX γ' δ =
      pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovToX γ γ' := by
  rw [← Category.assoc, M.tPrime_fst γ γ' δ,
    show M.ovToX γ' δ = M.ovFst γ' δ ≫ M.chartToX γ' from rfl,
    ← Category.assoc, M.triple_fst γ γ' δ]
  simp only [Category.assoc]
  rw [show M.ovFst γ' γ ≫ M.chartToX γ' = M.ovToX γ' γ from rfl, M.ovIso_over γ γ']

def glueData : Scheme.GlueData where
  J := M.cov.J
  U := M.chart
  V p := M.overlap p.1 p.2
  f γ γ' := M.ovFst γ γ'
  f_id γ := by
    show IsIso (M.ovFst γ γ)
    unfold ovFst chartToX
    infer_instance
  f_open γ γ' := M.ovFst_isOpenImmersion γ γ'
  t γ γ' := (M.ovIso γ γ').hom
  t_id γ := M.homUnique (M.ovIso γ γ).hom (𝟙 _) (M.ovIso_over γ γ) (Category.id_comp _)
  t' γ γ' δ := M.tPrime γ γ' δ
  t_fac γ γ' δ := M.tPrime_snd γ γ' δ
  cocycle γ γ' δ := by
    haveI : Mono (pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovFst γ γ') :=
      inferInstance
    rw [← cancel_mono (pullback.fst (M.ovFst γ γ') (M.ovFst γ δ) ≫ M.ovFst γ γ'),
      Category.id_comp]
    refine M.tripleUnique _ _ ?_ ?_
    · simp only [Category.assoc,
        show M.ovFst γ γ' ≫ M.chartToX γ = M.ovToX γ γ' from rfl]
      rw [M.tPrime_toX δ γ γ', M.tPrime_toX γ' δ γ, M.tPrime_toX γ γ' δ]
    · rw [Category.assoc, show M.ovFst γ γ' ≫ M.chartToX γ = M.ovToX γ γ' from rfl]

def dilatation : Scheme := M.glueData.glued

def chartTo (γ : M.cov.J) : M.chart γ ⟶ M.dilatation := M.glueData.ι γ

instance chartTo_isOpenImmersion (γ : M.cov.J) : IsOpenImmersion (M.chartTo γ) := by
  unfold chartTo; infer_instance

def structureMap : M.dilatation ⟶ X :=
  Multicoequalizer.desc M.glueData.diagram _ (fun γ => M.chartToX γ) <| by
    rintro ⟨γ, γ'⟩
    change M.ovFst γ γ' ≫ M.chartToX γ =
      ((M.ovIso γ γ').hom ≫ M.ovFst γ' γ) ≫ M.chartToX γ'
    rw [Category.assoc]
    exact (M.ovIso_over γ γ').symm

theorem structureMap_chart (γ : M.cov.J) :
    M.chartTo γ ≫ M.structureMap = M.chartToX γ :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem chart_glue (γ γ' : M.cov.J) :
    M.ovFst γ γ' ≫ M.chartTo γ = (M.ovIso γ γ').hom ≫ M.ovFst γ' γ ≫ M.chartTo γ' :=
  (M.glueData.glue_condition γ γ').symm

theorem structureMap_range (γ : M.cov.J) (p : M.dilatation)
    (hp : M.structureMap.base p ∈ Set.range (M.cov.map γ).base) :
    p ∈ Set.range (M.chartTo γ).base := by
  obtain ⟨γ2, y, hy⟩ := M.glueData.ι_jointly_surjective p
  have hy2 : (M.chartTo γ2).base y = p := hy
  have hsy : (M.chartToX γ2).base y ∈ Set.range (M.cov.map γ).base := by
    have h := congrArg (fun t : M.chart γ2 ⟶ X => t.base y) (M.structureMap_chart γ2)
    simp only [Scheme.comp_base_apply] at h
    rw [← h, hy2]
    exact hp
  have hover : y ∈ (M.chartToX γ2).base ⁻¹' Set.range (M.cov.map γ).base := hsy
  rw [← Scheme.Pullback.range_fst] at hover
  obtain ⟨z, hz⟩ := hover
  refine ⟨(M.ovFst γ γ2).base ((M.ovIso γ2 γ).hom.base z), ?_⟩
  have hglue := congrArg (fun t : M.overlap γ2 γ ⟶ M.dilatation => t.base z)
    (M.chart_glue γ2 γ)
  simp only [Scheme.comp_base_apply] at hglue
  rw [← hy2, ← hz]
  exact hglue.symm


def chartCompare (γ : M.cov.J) : M.chart γ ⟶ pullback M.structureMap (M.cov.map γ) :=
  pullback.lift (M.chartTo γ) (M.chartHom γ) (by rw [M.structureMap_chart γ]; rfl)

@[reassoc]
theorem chartCompare_fst (γ : M.cov.J) :
    M.chartCompare γ ≫ pullback.fst M.structureMap (M.cov.map γ) = M.chartTo γ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem chartCompare_snd (γ : M.cov.J) :
    M.chartCompare γ ≫ pullback.snd M.structureMap (M.cov.map γ) = M.chartHom γ :=
  pullback.lift_snd _ _ _

instance chartCompare_isIso (γ : M.cov.J) : IsIso (M.chartCompare γ) := by
  haveI := M.cov.map_prop γ
  haveI : IsOpenImmersion (M.chartCompare γ ≫
      pullback.fst M.structureMap (M.cov.map γ)) := by
    rw [M.chartCompare_fst γ]; infer_instance
  haveI hop : IsOpenImmersion (M.chartCompare γ) :=
    IsOpenImmersion.of_comp _ (pullback.fst M.structureMap (M.cov.map γ))
  haveI : Epi (M.chartCompare γ).base := by
    rw [TopCat.epi_iff_surjective]
    intro q
    have hcond : M.structureMap.base
        ((pullback.fst M.structureMap (M.cov.map γ)).base q) ∈
        Set.range (M.cov.map γ).base := by
      refine ⟨(pullback.snd M.structureMap (M.cov.map γ)).base q, ?_⟩
      have h := congrArg (fun t : pullback M.structureMap (M.cov.map γ) ⟶ X => t.base q)
        (pullback.condition (f := M.structureMap) (g := M.cov.map γ))
      simp only [Scheme.comp_base_apply] at h
      exact h.symm
    obtain ⟨w, hw⟩ := M.structureMap_range γ _ hcond
    refine ⟨w, ?_⟩
    have hinj := (pullback.fst M.structureMap (M.cov.map γ)).isOpenEmbedding.injective
    apply hinj
    have hkw := congrArg (fun t : M.chart γ ⟶ M.dilatation => t.base w)
      (M.chartCompare_fst γ)
    simp only [Scheme.comp_base_apply] at hkw
    rw [hkw, hw]
  exact IsOpenImmersion.to_iso (M.chartCompare γ)

instance chartPullback_isAffine (γ : M.cov.J) :
    IsAffine (pullback M.structureMap (M.cov.map γ)) :=
  IsAffine.of_isIso (inv (M.chartCompare γ))

theorem structureMap_isAffineHom : IsAffineHom M.structureMap := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsAffineHom) M.cov.cover]
  intro γ
  show IsAffineHom (pullback.snd M.structureMap (M.cov.map γ))
  infer_instance

end PreMultiCenter

namespace MultiCenter

variable (M : MultiCenter X)

def dilatation : Scheme := M.rep.dilatation

def structureMap : M.dilatation ⟶ X := M.rep.structureMap

end MultiCenter

end SchemeDilatation
