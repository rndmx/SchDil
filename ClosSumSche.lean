import ClosInterSch

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

theorem Ideal.map_mul_ideal {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I J : Ideal A) : Ideal.map f (I * J) = Ideal.map f I * Ideal.map f J :=
  Ideal.map_mul f I J

theorem Ideal.map_map_mul {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (I J : Ideal A) :
    Ideal.map g (Ideal.map f (I * J)) =
      Ideal.map (g.comp f) I * Ideal.map (g.comp f) J := by
  rw [Ideal.map_mul_ideal, Ideal.map_mul_ideal, Ideal.map_map, Ideal.map_map]

noncomputable def PreClos.prodIdeal (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) : Ideal (W.cov.obj γ) :=
  W.ideal i γ * Z.reindexIdeal W.cov (e i) γ

theorem PreClos.prodIdeal_le_interIdeal (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    W.prodIdeal Z e i γ ≤ W.interIdeal Z e i γ := by
  rw [W.interIdeal_eq Z e i γ]
  exact le_trans Ideal.mul_le_inf (le_trans inf_le_left le_sup_left)

theorem PreClos.prodIdeal_le_left (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) : W.prodIdeal Z e i γ ≤ W.ideal i γ :=
  le_trans Ideal.mul_le_inf inf_le_left

theorem PreClos.prodIdeal_le_right (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    W.prodIdeal Z e i γ ≤ Z.reindexIdeal W.cov (e i) γ :=
  le_trans Ideal.mul_le_inf inf_le_right

theorem PreClos.prodIdeal_eq_left_of_right_eq_top (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J)
    (h : Z.reindexIdeal W.cov (e i) γ = ⊤) :
    W.prodIdeal Z e i γ = W.ideal i γ := by
  rw [PreClos.prodIdeal, h, Ideal.mul_top]

theorem PreClos.prodIdeal_eq_bot_of_right_eq_bot (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J)
    (h : Z.reindexIdeal W.cov (e i) γ = ⊥) : W.prodIdeal Z e i γ = ⊥ := by
  rw [PreClos.prodIdeal, h, Ideal.mul_bot]

theorem PreClos.prodIdeal_span_singleton (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) (a b : W.cov.obj γ)
    (ha : W.ideal i γ = Ideal.span {a})
    (hb : Z.reindexIdeal W.cov (e i) γ = Ideal.span {b}) :
    W.prodIdeal Z e i γ = Ideal.span {a * b} := by
  rw [PreClos.prodIdeal, ha, hb, Ideal.span_singleton_mul_span_singleton]

theorem PreClos.prodIdeal_eq_interIdeal_of_sup_eq_top
    (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb) (i : W.indnumb) (γ : W.cov.J)
    (h : W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ = ⊤) :
    W.prodIdeal Z e i γ = W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ := by
  rw [PreClos.prodIdeal]
  refine le_antisymm Ideal.mul_le_inf ?_
  calc W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ
      = (W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ) * ⊤ := (Ideal.mul_top _).symm
    _ = (W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ) *
          (W.ideal i γ ⊔ Z.reindexIdeal W.cov (e i) γ) := by rw [h]
    _ = (W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ) * W.ideal i γ ⊔
          (W.ideal i γ ⊓ Z.reindexIdeal W.cov (e i) γ) *
            Z.reindexIdeal W.cov (e i) γ := Ideal.mul_sup _ _ _
    _ ≤ W.ideal i γ * Z.reindexIdeal W.cov (e i) γ := sup_le
        (le_trans (Ideal.mul_mono inf_le_right le_rfl) (le_of_eq (mul_comm _ _)))
        (Ideal.mul_mono inf_le_left le_rfl)

structure ChartDatum (X : Scheme.{u+1}) where
  cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X
  idl : (γ : cov.J) → Ideal (cov.obj γ)
  compat : ∀ {W : Scheme.{u+1}} [IsAffine W] {γ γ' : cov.J}
    (a : W ⟶ Spec (cov.obj γ)) (b : W ⟶ Spec (cov.obj γ')),
    a ≫ cov.map γ = b ≫ cov.map γ' →
    Ideal.map (Spec.preimage (W.isoSpec.inv ≫ a)).hom (idl γ) =
      Ideal.map (Spec.preimage (W.isoSpec.inv ≫ b)).hom (idl γ')

namespace ChartDatum

variable {X : Scheme.{u+1}} (D : ChartDatum X)

def chart (γ : D.cov.J) : Scheme :=
  Spec (CommRingCat.of (D.cov.obj γ ⧸ D.idl γ))

def chartHom (γ : D.cov.J) : D.chart γ ⟶ Spec (D.cov.obj γ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.idl γ)))

instance chartHom_isClosedImmersion (γ : D.cov.J) : IsClosedImmersion (D.chartHom γ) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance chartHom_mono (γ : D.cov.J) : Mono (D.chartHom γ) := inferInstance

def chartToX (γ : D.cov.J) : D.chart γ ⟶ X := D.chartHom γ ≫ D.cov.map γ

instance chartToX_mono (γ : D.cov.J) : Mono (D.chartToX γ) := by
  haveI := D.cov.map_prop γ
  haveI : Mono (D.cov.map γ) := inferInstance
  unfold chartToX
  infer_instance

def overlap (γ γ' : D.cov.J) : Scheme := pullback (D.chartToX γ) (D.cov.map γ')

def ovFst (γ γ' : D.cov.J) : D.overlap γ γ' ⟶ D.chart γ := pullback.fst _ _

instance ovFst_isOpenImmersion (γ γ' : D.cov.J) : IsOpenImmersion (D.ovFst γ γ') := by
  haveI := D.cov.map_prop γ'
  unfold ovFst
  infer_instance

def ovToX (γ γ' : D.cov.J) : D.overlap γ γ' ⟶ X := D.ovFst γ γ' ≫ D.chartToX γ

theorem hom_overlap_ext {γ γ' : D.cov.J} (f g : D.overlap γ γ' ⟶ D.overlap γ' γ)
    (hf : f ≫ D.ovToX γ' γ = D.ovToX γ γ') (hg : g ≫ D.ovToX γ' γ = D.ovToX γ γ') :
    f = g := by
  haveI := D.cov.map_prop γ
  haveI : Mono (D.cov.map γ) := inferInstance
  have hfst : f ≫ D.ovFst γ' γ = g ≫ D.ovFst γ' γ := by
    rw [← cancel_mono (D.chartToX γ'), Category.assoc, Category.assoc]
    show f ≫ D.ovToX γ' γ = g ≫ D.ovToX γ' γ
    rw [hf, hg]
  have hsnd : f ≫ pullback.snd (D.chartToX γ') (D.cov.map γ) =
      g ≫ pullback.snd (D.chartToX γ') (D.cov.map γ) := by
    rw [← cancel_mono (D.cov.map γ), Category.assoc, Category.assoc,
      ← pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ D.chartToX γ') hfst
  exact pullback.hom_ext hfst hsnd

theorem hom_overlap_self_ext {γ γ' : D.cov.J} (f g : D.overlap γ γ' ⟶ D.overlap γ γ')
    (hf : f ≫ D.ovToX γ γ' = D.ovToX γ γ') (hg : g ≫ D.ovToX γ γ' = D.ovToX γ γ') :
    f = g := by
  haveI := D.cov.map_prop γ'
  haveI : Mono (D.cov.map γ') := inferInstance
  have hfst : f ≫ D.ovFst γ γ' = g ≫ D.ovFst γ γ' := by
    rw [← cancel_mono (D.chartToX γ), Category.assoc, Category.assoc]
    show f ≫ D.ovToX γ γ' = g ≫ D.ovToX γ γ'
    rw [hf, hg]
  have hsnd : f ≫ pullback.snd (D.chartToX γ) (D.cov.map γ') =
      g ≫ pullback.snd (D.chartToX γ) (D.cov.map γ') := by
    rw [← cancel_mono (D.cov.map γ'), Category.assoc, Category.assoc,
      ← pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ D.chartToX γ) hfst
  exact pullback.hom_ext hfst hsnd

theorem hom_chart_triple_ext {γ γ' δ : D.cov.J}
    (f g : pullback (D.ovFst γ γ') (D.ovFst γ δ) ⟶ D.chart γ)
    (hf : f ≫ D.chartToX γ = pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ D.ovToX γ γ')
    (hg : g ≫ D.chartToX γ = pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ D.ovToX γ γ') :
    f = g := by
  rw [← cancel_mono (D.chartToX γ), hf, hg]

theorem hom_chart_ext (γ γ' : D.cov.J) {Q : Scheme.{u+1}} (u v : Q ⟶ D.chart γ')
    (hu : u ≫ D.chartHom γ' = v ≫ D.chartHom γ') : u = v := by
  rwa [cancel_mono (D.chartHom γ')] at hu

theorem exists_hom_chart_of_affine (γ γ' : D.cov.J) {W : Scheme.{u+1}} [IsAffine W]
    (m : W ⟶ D.overlap γ γ') :
    ∃ l : W ⟶ D.chart γ',
      l ≫ D.chartHom γ' = m ≫ pullback.snd (D.chartToX γ) (D.cov.map γ') := by
  classical
  set A : W ⟶ Spec (D.cov.obj γ) := m ≫ D.ovFst γ γ' ≫ D.chartHom γ with hA
  set B : W ⟶ Spec (D.cov.obj γ') := m ≫ pullback.snd (D.chartToX γ) (D.cov.map γ')
    with hB
  have hab : A ≫ D.cov.map γ = B ≫ D.cov.map γ' := by
    have h : D.ovFst γ γ' ≫ D.chartToX γ =
        pullback.snd (D.chartToX γ) (D.cov.map γ') ≫ D.cov.map γ' := pullback.condition
    rw [hA, hB, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (fun t => m ≫ t) h
  have hfac : Spec.preimage (W.isoSpec.inv ≫ A) =
      CommRingCat.ofHom (Ideal.Quotient.mk (D.idl γ)) ≫
        Spec.preimage (W.isoSpec.inv ≫ m ≫ D.ovFst γ γ') := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, hA]
    simp only [Category.assoc]
    rfl
  have ha0 : Ideal.map (Spec.preimage (W.isoSpec.inv ≫ A)).hom (D.idl γ) = ⊥ := by
    rw [hfac]
    show Ideal.map ((Spec.preimage (W.isoSpec.inv ≫ m ≫ D.ovFst γ γ')).hom.comp
      (Ideal.Quotient.mk (D.idl γ))) (D.idl γ) = ⊥
    rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  have hb0 : Ideal.map (Spec.preimage (W.isoSpec.inv ≫ B)).hom (D.idl γ') = ⊥ := by
    rw [← D.compat A B hab]
    exact ha0
  have hkill : ∀ x ∈ D.idl γ', (Spec.preimage (W.isoSpec.inv ≫ B)).hom x = 0 := by
    intro x hx
    rw [← Ideal.mem_bot, ← hb0]
    exact Ideal.mem_map_of_mem _ hx
  refine ⟨W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift (D.idl γ') (Spec.preimage (W.isoSpec.inv ≫ B)).hom hkill)), ?_⟩
  show _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.idl γ'))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show CommRingCat.ofHom ((Ideal.Quotient.lift (D.idl γ')
      (Spec.preimage (W.isoSpec.inv ≫ B)).hom hkill).comp
      (Ideal.Quotient.mk (D.idl γ'))) = Spec.preimage (W.isoSpec.inv ≫ B) from by
    apply CommRingCat.hom_ext
    ext x
    exact Ideal.Quotient.lift_mk (D.idl γ') _ hkill]
  rw [Spec.map_preimage, Iso.hom_inv_id_assoc]

theorem exists_hom_chart (γ γ' : D.cov.J) :
    ∃ leg : D.overlap γ γ' ⟶ D.chart γ',
      leg ≫ D.chartHom γ' = pullback.snd (D.chartToX γ) (D.cov.map γ') := by
  classical
  set 𝒰 := (D.overlap γ γ').affineCover with h𝒰
  have hloc : ∀ j : 𝒰.J, ∃ l : 𝒰.obj j ⟶ D.chart γ',
      l ≫ D.chartHom γ' = 𝒰.map j ≫ pullback.snd (D.chartToX γ) (D.cov.map γ') :=
    fun j => D.exists_hom_chart_of_affine γ γ' (𝒰.map j)
  choose l hl using hloc
  have hcompat : ∀ j k, pullback.fst (𝒰.map j) (𝒰.map k) ≫ l j =
      pullback.snd (𝒰.map j) (𝒰.map k) ≫ l k := by
    intro j k
    refine D.hom_chart_ext γ γ' _ _ ?_
    rw [Category.assoc, Category.assoc, hl j, hl k, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms l hcompat, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, 𝒰.ι_glueMorphisms l hcompat j, hl j]

theorem existsUnique_ovIso (γ γ' : D.cov.J) :
    ∃! e : D.overlap γ γ' ≅ D.overlap γ' γ, e.hom ≫ D.ovToX γ' γ = D.ovToX γ γ' := by
  have key : ∀ a b : D.cov.J, ∃ e : D.overlap a b ⟶ D.overlap b a,
      e ≫ D.ovToX b a = D.ovToX a b := by
    intro a b
    obtain ⟨leg, hleg⟩ := D.exists_hom_chart a b
    have hcond : leg ≫ D.chartToX b =
        (D.ovFst a b ≫ D.chartHom a) ≫ D.cov.map a := by
      show leg ≫ D.chartHom b ≫ D.cov.map b = _
      rw [← Category.assoc, hleg, ← pullback.condition, Category.assoc]
      rfl
    refine ⟨pullback.lift leg (D.ovFst a b ≫ D.chartHom a) hcond, ?_⟩
    have hlf : pullback.lift leg (D.ovFst a b ≫ D.chartHom a) hcond ≫ D.ovFst b a = leg :=
      pullback.lift_fst _ _ _
    show pullback.lift leg (D.ovFst a b ≫ D.chartHom a) hcond ≫
      D.ovFst b a ≫ D.chartToX b = D.ovFst a b ≫ D.chartToX a
    rw [← Category.assoc, hlf, hcond, Category.assoc]
    rfl
  obtain ⟨e, he⟩ := key γ γ'
  obtain ⟨e', he'⟩ := key γ' γ
  have h1 : e ≫ e' = 𝟙 _ :=
    D.hom_overlap_self_ext _ _ (by rw [Category.assoc, he', he]) (Category.id_comp _)
  have h2 : e' ≫ e = 𝟙 _ :=
    D.hom_overlap_self_ext _ _ (by rw [Category.assoc, he, he']) (Category.id_comp _)
  exact ⟨⟨e, e', h1, h2⟩, he, fun E hE => Iso.ext (D.hom_overlap_ext E.hom e hE he)⟩

noncomputable def ovIso (γ γ' : D.cov.J) : D.overlap γ γ' ≅ D.overlap γ' γ :=
  (D.existsUnique_ovIso γ γ').choose

theorem ovIso_over (γ γ' : D.cov.J) :
    (D.ovIso γ γ').hom ≫ D.ovToX γ' γ = D.ovToX γ γ' := (D.existsUnique_ovIso γ γ').choose_spec.1

def triple (γ γ' δ : D.cov.J) :
    pullback (D.ovFst γ γ') (D.ovFst γ δ) ⟶ D.overlap γ' δ :=
  pullback.lift
    (pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ (D.ovIso γ γ').hom ≫ D.ovFst γ' γ)
    (pullback.snd (D.ovFst γ γ') (D.ovFst γ δ) ≫
      pullback.snd (D.chartToX γ) (D.cov.map δ))
    (by
      show _ ≫ (D.ovIso γ γ').hom ≫ D.ovFst γ' γ ≫ D.chartToX γ' = _
      rw [show D.ovFst γ' γ ≫ D.chartToX γ' = D.ovToX γ' γ from rfl, D.ovIso_over γ γ',
        show D.ovToX γ γ' = D.ovFst γ γ' ≫ D.chartToX γ from rfl, ← Category.assoc,
        pullback.condition (f := D.ovFst γ γ') (g := D.ovFst γ δ), Category.assoc,
        show D.ovFst γ δ ≫ D.chartToX γ = D.ovToX γ δ from rfl,
        show D.ovToX γ δ = pullback.snd (D.chartToX γ) (D.cov.map δ) ≫ D.cov.map δ from
          pullback.condition (f := D.chartToX γ) (g := D.cov.map δ), Category.assoc])

@[reassoc]
theorem triple_fst (γ γ' δ : D.cov.J) :
    D.triple γ γ' δ ≫ D.ovFst γ' δ =
      pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ (D.ovIso γ γ').hom ≫ D.ovFst γ' γ := by
  unfold triple ovFst; exact pullback.lift_fst _ _ _

def tPrime (γ γ' δ : D.cov.J) :
    pullback (D.ovFst γ γ') (D.ovFst γ δ) ⟶ pullback (D.ovFst γ' δ) (D.ovFst γ' γ) :=
  pullback.lift (D.triple γ γ' δ)
    (pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ (D.ovIso γ γ').hom)
    (by rw [show D.triple γ γ' δ ≫ D.ovFst γ' δ = _ from D.triple_fst γ γ' δ,
      Category.assoc])

@[reassoc]
theorem tPrime_fst (γ γ' δ : D.cov.J) :
    D.tPrime γ γ' δ ≫ pullback.fst (D.ovFst γ' δ) (D.ovFst γ' γ) = D.triple γ γ' δ := by
  unfold tPrime; exact pullback.lift_fst _ _ _

@[reassoc]
theorem tPrime_snd (γ γ' δ : D.cov.J) :
    D.tPrime γ γ' δ ≫ pullback.snd (D.ovFst γ' δ) (D.ovFst γ' γ) =
      pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ (D.ovIso γ γ').hom := by
  unfold tPrime; exact pullback.lift_snd _ _ _

@[reassoc]
theorem tPrime_toX (γ γ' δ : D.cov.J) :
    D.tPrime γ γ' δ ≫ pullback.fst (D.ovFst γ' δ) (D.ovFst γ' γ) ≫ D.ovToX γ' δ =
      pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ D.ovToX γ γ' := by
  rw [← Category.assoc, D.tPrime_fst γ γ' δ,
    show D.ovToX γ' δ = D.ovFst γ' δ ≫ D.chartToX γ' from rfl,
    ← Category.assoc, D.triple_fst γ γ' δ]
  simp only [Category.assoc]
  rw [show D.ovFst γ' γ ≫ D.chartToX γ' = D.ovToX γ' γ from rfl, D.ovIso_over γ γ']

noncomputable def glueData : Scheme.GlueData where
  J := D.cov.J
  U := D.chart
  V p := D.overlap p.1 p.2
  f γ γ' := D.ovFst γ γ'
  f_id γ := by
    show IsIso (D.ovFst γ γ)
    haveI := D.cov.map_prop γ
    unfold ovFst chartToX
    infer_instance
  f_open γ γ' := D.ovFst_isOpenImmersion γ γ'
  t γ γ' := (D.ovIso γ γ').hom
  t_id γ := D.hom_overlap_ext (D.ovIso γ γ).hom (𝟙 _) (D.ovIso_over γ γ) (Category.id_comp _)
  t' γ γ' δ := D.tPrime γ γ' δ
  t_fac γ γ' δ := D.tPrime_snd γ γ' δ
  cocycle γ γ' δ := by
    haveI : Mono (pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ D.ovFst γ γ') :=
      inferInstance
    rw [← cancel_mono (pullback.fst (D.ovFst γ γ') (D.ovFst γ δ) ≫ D.ovFst γ γ'),
      Category.id_comp]
    refine D.hom_chart_triple_ext _ _ ?_ ?_
    · simp only [Category.assoc,
        show D.ovFst γ γ' ≫ D.chartToX γ = D.ovToX γ γ' from rfl]
      rw [D.tPrime_toX δ γ γ', D.tPrime_toX γ' δ γ, D.tPrime_toX γ γ' δ]
    · rw [Category.assoc, show D.ovFst γ γ' ≫ D.chartToX γ = D.ovToX γ γ' from rfl]

noncomputable def glued : Scheme := D.glueData.glued

noncomputable def chartTo (γ : D.cov.J) : D.chart γ ⟶ D.glued := D.glueData.ι γ

instance chartTo_isOpenImmersion (γ : D.cov.J) : IsOpenImmersion (D.chartTo γ) := by
  unfold chartTo; infer_instance

noncomputable def structureMap : D.glued ⟶ X :=
  Multicoequalizer.desc D.glueData.diagram _ (fun γ => D.chartToX γ) <| by
    rintro ⟨γ, γ'⟩
    change D.ovFst γ γ' ≫ D.chartToX γ =
      ((D.ovIso γ γ').hom ≫ D.ovFst γ' γ) ≫ D.chartToX γ'
    rw [Category.assoc]
    exact (D.ovIso_over γ γ').symm

theorem structureMap_chart (γ : D.cov.J) :
    D.chartTo γ ≫ D.structureMap = D.chartToX γ :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem chart_glue (γ γ' : D.cov.J) :
    D.ovFst γ γ' ≫ D.chartTo γ = (D.ovIso γ γ').hom ≫ D.ovFst γ' γ ≫ D.chartTo γ' :=
  (D.glueData.glue_condition γ γ').symm

theorem structureMap_range (γ : D.cov.J) (p : D.glued)
    (hp : D.structureMap.base p ∈ Set.range (D.cov.map γ).base) :
    p ∈ Set.range (D.chartTo γ).base := by
  obtain ⟨γ2, y, hy⟩ := D.glueData.ι_jointly_surjective p
  have hy2 : (D.chartTo γ2).base y = p := hy
  have hsy : (D.chartToX γ2).base y ∈ Set.range (D.cov.map γ).base := by
    have h := congrArg (fun t : D.chart γ2 ⟶ X => t.base y) (D.structureMap_chart γ2)
    simp only [Scheme.comp_base_apply] at h
    rw [← h, hy2]
    exact hp
  have hover : y ∈ (D.chartToX γ2).base ⁻¹' Set.range (D.cov.map γ).base := hsy
  rw [← Scheme.Pullback.range_fst] at hover
  obtain ⟨z, hz⟩ := hover
  refine ⟨(D.ovFst γ γ2).base ((D.ovIso γ2 γ).hom.base z), ?_⟩
  have hglue := congrArg (fun t : D.overlap γ2 γ ⟶ D.glued => t.base z)
    (D.chart_glue γ2 γ)
  simp only [Scheme.comp_base_apply] at hglue
  rw [← hy2, ← hz]
  exact hglue.symm

noncomputable def chartCompare (γ : D.cov.J) :
    D.chart γ ⟶ pullback D.structureMap (D.cov.map γ) :=
  pullback.lift (D.chartTo γ) (D.chartHom γ) (by rw [D.structureMap_chart γ]; rfl)

@[reassoc]
theorem chartCompare_fst (γ : D.cov.J) :
    D.chartCompare γ ≫ pullback.fst D.structureMap (D.cov.map γ) = D.chartTo γ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem chartCompare_snd (γ : D.cov.J) :
    D.chartCompare γ ≫ pullback.snd D.structureMap (D.cov.map γ) = D.chartHom γ :=
  pullback.lift_snd _ _ _

instance chartCompare_isIso (γ : D.cov.J) : IsIso (D.chartCompare γ) := by
  haveI := D.cov.map_prop γ
  haveI : IsOpenImmersion (D.chartCompare γ ≫
      pullback.fst D.structureMap (D.cov.map γ)) := by
    rw [D.chartCompare_fst γ]; infer_instance
  haveI hop : IsOpenImmersion (D.chartCompare γ) :=
    IsOpenImmersion.of_comp _ (pullback.fst D.structureMap (D.cov.map γ))
  haveI : Epi (D.chartCompare γ).base := by
    rw [TopCat.epi_iff_surjective]
    intro q
    have hcond : D.structureMap.base
        ((pullback.fst D.structureMap (D.cov.map γ)).base q) ∈
        Set.range (D.cov.map γ).base := by
      refine ⟨(pullback.snd D.structureMap (D.cov.map γ)).base q, ?_⟩
      have h := congrArg (fun t : pullback D.structureMap (D.cov.map γ) ⟶ X => t.base q)
        (pullback.condition (f := D.structureMap) (g := D.cov.map γ))
      simp only [Scheme.comp_base_apply] at h
      exact h.symm
    obtain ⟨w, hw⟩ := D.structureMap_range γ _ hcond
    refine ⟨w, ?_⟩
    have hinj := (pullback.fst D.structureMap (D.cov.map γ)).isOpenEmbedding.injective
    apply hinj
    have hkw := congrArg (fun t : D.chart γ ⟶ D.glued => t.base w)
      (D.chartCompare_fst γ)
    simp only [Scheme.comp_base_apply] at hkw
    rw [hkw, hw]
  exact IsOpenImmersion.to_iso (D.chartCompare γ)

end ChartDatum

noncomputable def PreClos.sumChartDatum (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) : ChartDatum X where
  cov := W.cov
  idl γ := W.prodIdeal Z e i γ
  compat a b hab := by
    show Ideal.map _ (W.ideal i _ * Z.reindexIdeal W.cov (e i) _) =
      Ideal.map _ (W.ideal i _ * Z.reindexIdeal W.cov (e i) _)
    rw [Ideal.map_mul, Ideal.map_mul]
    congr 1
    · exact chartIdeal_agree W a b hab i
    · exact chartIdeal_agree (Z.reindex W.cov) a b hab (e i)

noncomputable def PreClos.sum (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb) :
    PreClos X where
  indnumb := W.indnumb
  subscheme i := (W.sumChartDatum Z e i).glued
  over i := ⟨(W.sumChartDatum Z e i).structureMap⟩
  cov := W.cov
  ideal i γ := W.prodIdeal Z e i γ
  condiso i γ := asIso ((W.sumChartDatum Z e i).chartCompare γ)
  condover i γ := by
    rw [Scheme.Hom.isOver_iff, pullback_over_right, spec_quotient_ideal_over_eq]
    show (W.sumChartDatum Z e i).chartCompare γ ≫
        pullback.snd ((W.sumChartDatum Z e i).structureMap) (W.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (W.prodIdeal Z e i γ)))
    exact (W.sumChartDatum Z e i).chartCompare_snd γ

theorem PreClos.sum_ideal_eq_mul (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) (γ : W.cov.J) :
    (W.sum Z e).ideal i γ = W.ideal i γ * Z.reindexIdeal W.cov (e i) γ := rfl

namespace ChartDatum

variable {X : Scheme.{u+1}} (D : ChartDatum X)

theorem idl_map_eq_bot (γ : D.cov.J) {T : Scheme.{u+1}} [IsAffine T] (a : T ⟶ D.chart γ) :
    Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a ≫ D.chartHom γ)).hom (D.idl γ) = ⊥ := by
  have hfac : Spec.preimage (T.isoSpec.inv ≫ a ≫ D.chartHom γ) =
      CommRingCat.ofHom (Ideal.Quotient.mk (D.idl γ)) ≫
        Spec.preimage (T.isoSpec.inv ≫ a) := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
    simp only [Category.assoc]
    rfl
  rw [hfac]
  show Ideal.map ((Spec.preimage (T.isoSpec.inv ≫ a)).hom.comp
    (Ideal.Quotient.mk (D.idl γ))) (D.idl γ) = ⊥
  rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]

theorem exists_lift_of_idl_map_eq_bot (δ : D.cov.J) {T : Scheme.{u+1}} [IsAffine T]
    (b : T ⟶ Spec (D.cov.obj δ))
    (hb0 : Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom (D.idl δ) = ⊥) :
    ∃ l : T ⟶ D.chart δ, l ≫ D.chartHom δ = b := by
  have hkill : ∀ x ∈ D.idl δ, (Spec.preimage (T.isoSpec.inv ≫ b)).hom x = 0 := by
    intro x hx
    rw [← Ideal.mem_bot, ← hb0]
    exact Ideal.mem_map_of_mem _ hx
  refine ⟨T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift (D.idl δ) (Spec.preimage (T.isoSpec.inv ≫ b)).hom hkill)), ?_⟩
  show _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.idl δ))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show CommRingCat.ofHom ((Ideal.Quotient.lift (D.idl δ)
      (Spec.preimage (T.isoSpec.inv ≫ b)).hom hkill).comp
      (Ideal.Quotient.mk (D.idl δ))) = Spec.preimage (T.isoSpec.inv ≫ b) from by
    apply CommRingCat.hom_ext
    ext x
    exact Ideal.Quotient.lift_mk (D.idl δ) _ hkill]
  rw [Spec.map_preimage, Iso.hom_inv_id_assoc]

instance structureMap_isClosedImmersion : IsClosedImmersion D.structureMap := by
  rw [IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) D.cov.cover]
  intro γ
  show IsClosedImmersion (pullback.snd D.structureMap (D.cov.map γ))
  rw [show pullback.snd D.structureMap (D.cov.map γ) =
      inv (D.chartCompare γ) ≫ D.chartHom γ from by
    rw [← D.chartCompare_snd γ, IsIso.inv_hom_id_assoc]]
  infer_instance

instance structureMap_mono : Mono D.structureMap := inferInstance

theorem exists_hom_glued_of_idl_map_eq (D' : ChartDatum X)
    (cross : ∀ {T : Scheme.{u+1}} [IsAffine T] {γ : D.cov.J} {δ : D'.cov.J}
      (a : T ⟶ Spec (D.cov.obj γ)) (b : T ⟶ Spec (D'.cov.obj δ)),
      a ≫ D.cov.map γ = b ≫ D'.cov.map δ →
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom (D.idl γ) =
        Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom (D'.idl δ)) :
    ∃ h : D.glued ⟶ D'.glued, h ≫ D'.structureMap = D.structureMap := by
  classical
  have key : ∀ x : D.glued, ∃ (R : CommRingCat.{u+1}) (emb : Spec R ⟶ D.glued)
      (g : Spec R ⟶ D'.glued), IsOpenImmersion emb ∧
      x ∈ Set.range emb.base ∧ g ≫ D'.structureMap = emb ≫ D.structureMap := by
    intro x
    obtain ⟨γ, y, hy⟩ := D.glueData.ι_jointly_surjective x
    set δ := D'.cov.f (D.structureMap.base x) with hδdef
    have hδ := D'.cov.covers (D.structureMap.base x)
    have hU : x ∈ (D.chartTo γ).opensRange ⊓
        (D.structureMap ⁻¹ᵁ (D'.cov.map δ).opensRange) := by
      constructor
      · exact ⟨y, hy⟩
      · exact hδ
    obtain ⟨R, emb, hemb, hxmem, hrange⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset (U := (D.chartTo γ).opensRange ⊓
        (D.structureMap ⁻¹ᵁ (D'.cov.map δ).opensRange)) hU
    haveI : IsOpenImmersion emb := hemb
    have sub₁ : Set.range emb.base ⊆ Set.range (D.chartTo γ).base := by
      intro p hp
      exact (hrange hp).1
    have sub₂ : Set.range (emb ≫ D.structureMap).base ⊆
        Set.range (D'.cov.map δ).base := by
      rintro _ ⟨q, rfl⟩
      have hq := (hrange ⟨q, rfl⟩).2
      rw [Scheme.comp_base_apply]
      exact hq
    set aa := IsOpenImmersion.lift (D.chartTo γ) emb sub₁ with haa
    set bb := IsOpenImmersion.lift (D'.cov.map δ) (emb ≫ D.structureMap) sub₂ with hbb
    have hab : (aa ≫ D.chartHom γ) ≫ D.cov.map γ = bb ≫ D'.cov.map δ := by
      rw [Category.assoc]
      show aa ≫ D.chartToX γ = _
      rw [← D.structureMap_chart γ, ← Category.assoc, haa, IsOpenImmersion.lift_fac,
        hbb, IsOpenImmersion.lift_fac]
    have hb0 : Ideal.map (Spec.preimage ((Spec R).isoSpec.inv ≫ bb)).hom
        (D'.idl δ) = ⊥ := by
      rw [← cross (aa ≫ D.chartHom γ) bb hab]
      exact D.idl_map_eq_bot γ aa
    obtain ⟨l, hl⟩ := D'.exists_lift_of_idl_map_eq_bot δ bb hb0
    refine ⟨R, emb, l ≫ D'.chartTo δ, hemb, hxmem, ?_⟩
    rw [Category.assoc, D'.structureMap_chart δ]
    show l ≫ D'.chartHom δ ≫ D'.cov.map δ = _
    rw [← Category.assoc, hl, hbb, IsOpenImmersion.lift_fac]
  choose R emb g hemb hmem hg using key
  haveI : ∀ x, IsOpenImmersion (emb x) := hemb
  let 𝒰 : D.glued.OpenCover :=
    { J := D.glued, obj := fun x => Spec (R x), map := emb, f := fun t => t,
      covers := hmem, map_prop := hemb }
  have hcompat : ∀ x y : 𝒰.J, pullback.fst (𝒰.map x) (𝒰.map y) ≫ g x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ g y := by
    intro x y
    rw [← cancel_mono D'.structureMap, Category.assoc, Category.assoc, hg x, hg y,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ D.structureMap) pullback.condition
  refine ⟨𝒰.glueMorphisms g hcompat, ?_⟩
  refine 𝒰.hom_ext _ _ (fun x => ?_)
  rw [← Category.assoc, 𝒰.ι_glueMorphisms g hcompat x]
  exact hg x

theorem existsUnique_iso_glued_of_idl_map_eq (D' : ChartDatum X)
    (cross : ∀ {T : Scheme.{u+1}} [IsAffine T] {γ : D.cov.J} {δ : D'.cov.J}
      (a : T ⟶ Spec (D.cov.obj γ)) (b : T ⟶ Spec (D'.cov.obj δ)),
      a ≫ D.cov.map γ = b ≫ D'.cov.map δ →
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom (D.idl γ) =
        Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom (D'.idl δ)) :
    ∃! e2 : D.glued ≅ D'.glued, e2.hom ≫ D'.structureMap = D.structureMap := by
  obtain ⟨h, hh⟩ := D.exists_hom_glued_of_idl_map_eq D' cross
  obtain ⟨h', hh'⟩ := D'.exists_hom_glued_of_idl_map_eq D (fun a b hab => (cross b a hab.symm).symm)
  have h1 : h ≫ h' = 𝟙 _ := by
    rw [← cancel_mono D.structureMap, Category.assoc, hh', hh, Category.id_comp]
  have h2 : h' ≫ h = 𝟙 _ := by
    rw [← cancel_mono D'.structureMap, Category.assoc, hh, hh', Category.id_comp]
  refine ⟨⟨h, h', h1, h2⟩, hh, fun E hE => Iso.ext ?_⟩
  rw [← cancel_mono D'.structureMap, hE, hh]

end ChartDatum

theorem PreClos.prodIdeal_map_eq_of_relStructure (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (RW : relStructure W W₁) (RZ : relStructure Z Z₁)
    (hcomm : ∀ j, RZ.indnumb_equiv (e j) = e₁ (RW.indnumb_equiv j)) (i : W.indnumb)
    {T : Scheme.{u+1}} [IsAffine T] {γ : W.cov.J} {δ : W₁.cov.J}
    (a : T ⟶ Spec (W.cov.obj γ)) (b : T ⟶ Spec (W₁.cov.obj δ))
    (hab : a ≫ W.cov.map γ = b ≫ W₁.cov.map δ) :
    Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom (W.prodIdeal Z e i γ) =
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
        (W₁.prodIdeal Z₁ e₁ (RW.indnumb_equiv i) δ) := by
  show Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom
      (W.ideal i γ * Z.reindexIdeal W.cov (e i) γ) =
    Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
      (W₁.ideal (RW.indnumb_equiv i) δ *
        Z₁.reindexIdeal W₁.cov (e₁ (RW.indnumb_equiv i)) δ)
  rw [Ideal.map_mul, Ideal.map_mul]
  have h1 := chartIdeal_agree_rel W W₁ RW a b hab i
  have h2 : Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom
      (Z.reindexIdeal W.cov (e i) γ) =
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
        (Z₁.reindexIdeal W₁.cov (RZ.indnumb_equiv (e i)) δ) :=
    chartIdeal_agree_rel (Z.reindex W.cov) (Z₁.reindex W₁.cov)
      ((Z.reindex_rel W.cov).trans (RZ.trans (Z₁.reindex_rel W₁.cov).symm)) a b hab (e i)
  rw [hcomm i] at h2
  rw [h1, h2]

noncomputable def PreClos.sumGluedIso (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (RW : relStructure W W₁) (RZ : relStructure Z Z₁)
    (hcomm : ∀ j, RZ.indnumb_equiv (e j) = e₁ (RW.indnumb_equiv j)) (i : W.indnumb) :
    (W.sumChartDatum Z e i).glued ≅
      (W₁.sumChartDatum Z₁ e₁ (RW.indnumb_equiv i)).glued :=
  ((W.sumChartDatum Z e i).existsUnique_iso_glued_of_idl_map_eq (W₁.sumChartDatum Z₁ e₁ (RW.indnumb_equiv i))
    (fun a b hab => W.prodIdeal_map_eq_of_relStructure Z W₁ Z₁ e e₁ RW RZ hcomm i a b hab)).choose

theorem PreClos.sumGluedIso_over (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (RW : relStructure W W₁) (RZ : relStructure Z Z₁)
    (hcomm : ∀ j, RZ.indnumb_equiv (e j) = e₁ (RW.indnumb_equiv j)) (i : W.indnumb) :
    (W.sumGluedIso Z W₁ Z₁ e e₁ RW RZ hcomm i).hom ≫
        (W₁.sumChartDatum Z₁ e₁ (RW.indnumb_equiv i)).structureMap =
      (W.sumChartDatum Z e i).structureMap :=
  ((W.sumChartDatum Z e i).existsUnique_iso_glued_of_idl_map_eq (W₁.sumChartDatum Z₁ e₁ (RW.indnumb_equiv i))
    (fun a b hab => W.prodIdeal_map_eq_of_relStructure Z W₁ Z₁ e e₁ RW RZ hcomm i a b hab)).choose_spec.1

noncomputable def PreClos.sumRel (W Z W₁ Z₁ : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (e₁ : W₁.indnumb ≃ Z₁.indnumb) (RW : relStructure W W₁) (RZ : relStructure Z Z₁)
    (hcomm : ∀ j, RZ.indnumb_equiv (e j) = e₁ (RW.indnumb_equiv j)) :
    relStructure (W.sum Z e) (W₁.sum Z₁ e₁) where
  indnumb_equiv := RW.indnumb_equiv
  subscheme_iso i := W.sumGluedIso Z W₁ Z₁ e e₁ RW RZ hcomm i
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact W.sumGluedIso_over Z W₁ Z₁ e e₁ RW RZ hcomm i

noncomputable def PreClosF.sum {ι : Type} (W Z : PreClosF X ι) : PreClosF X ι :=
  ⟨W.1.sum Z.1 ((Equiv.cast W.2).trans (Equiv.cast Z.2.symm)), W.2⟩

noncomputable def ClosF.sum {ι : Type} (W Z : ClosF X ι) : ClosF X ι :=
  Quotient.lift₂
    (fun W Z => (Quotient.mk'' (PreClosF.sum W Z) : ClosF X ι))
    (fun W Z W₁ Z₁ hW hZ => by
      obtain ⟨RW⟩ := hW
      obtain ⟨RZ⟩ := hZ
      refine Quotient.sound
        ⟨⟨W.1.sumRel Z.1 W₁.1 Z₁.1 _ _ RW.toRel RZ.toRel ?_, ?_⟩⟩
      · intro i
        rw [RZ.rigid, RW.rigid]
        simp only [Equiv.trans_apply, Equiv.cast_apply, cast_cast]
      · intro i
        exact RW.rigid i) W Z

theorem PreClos.prodIdeal_map_eq_comm (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) {T : Scheme.{u+1}} [IsAffine T] {γ : W.cov.J} {δ : Z.cov.J}
    (a : T ⟶ Spec (W.cov.obj γ)) (b : T ⟶ Spec (Z.cov.obj δ))
    (hab : a ≫ W.cov.map γ = b ≫ Z.cov.map δ) :
    Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom (W.prodIdeal Z e i γ) =
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
        (Z.prodIdeal W e.symm (e i) δ) := by
  show Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom
      (W.ideal i γ * Z.reindexIdeal W.cov (e i) γ) =
    Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
      (Z.ideal (e i) δ * W.reindexIdeal Z.cov (e.symm (e i)) δ)
  have h1 : Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom (W.ideal i γ) =
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom
        (W.reindexIdeal Z.cov i δ) :=
    chartIdeal_agree_rel W (W.reindex Z.cov) (W.reindex_rel Z.cov).symm a b hab i
  have h2 : Ideal.map (Spec.preimage (T.isoSpec.inv ≫ a)).hom
      (Z.reindexIdeal W.cov (e i) γ) =
      Ideal.map (Spec.preimage (T.isoSpec.inv ≫ b)).hom (Z.ideal (e i) δ) :=
    chartIdeal_agree_rel (Z.reindex W.cov) Z (Z.reindex_rel W.cov) a b hab (e i)
  rw [Ideal.map_mul, Ideal.map_mul, e.symm_apply_apply, h1, h2, mul_comm]

noncomputable def PreClos.sumGluedCommIso (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    (W.sumChartDatum Z e i).glued ≅ (Z.sumChartDatum W e.symm (e i)).glued :=
  ((W.sumChartDatum Z e i).existsUnique_iso_glued_of_idl_map_eq (Z.sumChartDatum W e.symm (e i))
    (fun a b hab => W.prodIdeal_map_eq_comm Z e i a b hab)).choose

theorem PreClos.sumGluedCommIso_over (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (i : W.indnumb) :
    (W.sumGluedCommIso Z e i).hom ≫ (Z.sumChartDatum W e.symm (e i)).structureMap =
      (W.sumChartDatum Z e i).structureMap :=
  ((W.sumChartDatum Z e i).existsUnique_iso_glued_of_idl_map_eq (Z.sumChartDatum W e.symm (e i))
    (fun a b hab => W.prodIdeal_map_eq_comm Z e i a b hab)).choose_spec.1

noncomputable def PreClos.sumCommRel (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb) :
    relStructure (W.sum Z e) (Z.sum W e.symm) where
  indnumb_equiv := e
  subscheme_iso i := W.sumGluedCommIso Z e i
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact W.sumGluedCommIso_over Z e i

theorem ClosF.sum_comm {ι : Type} (W Z : ClosF X ι) : W.sum Z = Z.sum W := by
  induction W using Quotient.inductionOn with | h W =>
  induction Z using Quotient.inductionOn with | h Z =>
  refine Quotient.sound ⟨⟨W.1.sumCommRel Z.1 _, ?_⟩⟩
  intro i
  show ((Equiv.cast W.2).trans (Equiv.cast Z.2.symm)) i = _
  simp only [Equiv.trans_apply, Equiv.cast_apply, cast_cast]
