import Project.Blowups.UniqueBlowup
import Project.Proj.Sum'

import Project.Blowups.Cars

suppress_compilation

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {ι : Type} [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]
variable {X : Scheme.{u+1}}

set_option maxHeartbeats 3200000 in
open Multicenter in

lemma ProjBlowup_UnivProp_existence_affine_preclo
    (A: CommRingCat.{u + 1}) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : IsCars _ (pullback_Clos (T ↘ Spec A) (loc_to_Clos A L))) :
    ∃ φ : T ⟶ BlMu L, Scheme.Hom.IsOver φ (Spec A) := by
  classical

  have gluing_material (x : T) :
    ∃ (B : CommRingCat)
      (emb : Spec B ⟶ T) (_ : Scheme.Over (Spec B) (Spec A))
      (_ : Scheme.Hom.IsOver emb (Spec A))
      (_ : IsOpenImmersion emb)
      (φ : Spec B ⟶ BlMu L),
      x ∈ Set.range emb.base ∧ Scheme.Hom.IsOver φ (Spec A) := by
    obtain ⟨Z, hZ, eq⟩ := cond
    change Quotient.mk'' _ = Quotient.mk'' _ at eq
    rw [Quotient.eq''] at eq
    obtain ⟨eq⟩ := eq

    let γ := Z.cov.f x
    let B : CommRingCat := Z.cov.obj γ
    let U_γ := Spec B

    let over0 : Scheme.Over U_γ (Spec A) := { hom := Z.cov.map γ ≫ T ↘ Spec A }
    let algebra0 : Algebra A B :=
      RingHom.toAlgebra <|
        ((Scheme.ΓSpecIso _).inv ≫ (U_γ ↘ Spec A).app _ ≫ (Scheme.ΓSpecIso _).hom).hom

    let c (i : ι) : B := hZ.prin (eq.indnumb_equiv.symm i) γ |>.generator

    have specB_over_specA_eq : (U_γ ↘ Spec A) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
      symm
      change Spec.map (_ ≫ _ ≫ _) = _ ≫ _
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        Spec.toLocallyRingedSpace_obj]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    have ideal_eq (i : ι) : Ideal.map (algebraMap A B) (L i) = Ideal.span { c i } := by
      haveI := hZ.prin (eq.indnumb_equiv.symm i) γ
      rw [Ideal.span_singleton_generator,
        PreClos_ideal_eq_of_rel A L Z eq γ (eq.indnumb_equiv.symm i) specB_over_specA_eq,
        Equiv.apply_symm_apply]
    let mc : Multicenter B :=
    { index := ι
      ideal i := Ideal.map (algebraMap A B) (L i)
      elem i := c i }

    have mc_nzd : ∀ i, algebraMap B B (mc.elem i) ∈ nonZeroDivisors B := fun i => by
      simpa using hZ.nonzerodiv (eq.indnumb_equiv.symm i) γ
    have mc_gen : ∀ i, Ideal.span {algebraMap B B (mc.elem i)} =
        Ideal.map (algebraMap B B) (mc.LargeIdeal i) := fun i => by
      have lg : mc.LargeIdeal i = Ideal.span {c i} := by
        show Ideal.map (algebraMap A B) (L i) + Ideal.span {c i} = _
        rw [ideal_eq, Ideal.add_eq_sup, sup_idem]
      rw [lg]
      simp only [Algebra.algebraMap_self, Ideal.map_id, RingHom.id_apply]
      rfl
    let dilaIso : B[mc] ≃ₐ[B] B :=
      (AlgEquiv.ofAlgHom
        (desc _ mc_nzd mc_gen)
        (Algebra.ofId _ _)
        (by ext)
        (by
          refine lemma_exists_unique_morphism' mc (fun i => ?_) (fun i => ?_) _ _
          · have h := Dilatation.nonzerodiv_image (F := mc) (Finsupp.single i 1)
            rw [familyPow_single] at h
            exact h
          · have h := Dilatation.image_elem_LargeIdeal_equal (F := mc) (Finsupp.single i 1)
            rw [familyPow_single, familyPow_single] at h
            exact h))

    let Rees := ReesAlgebra (fun i : ι => Ideal.map (algebraMap A B) (L i))

    let Mu_c : Mu (fun i => Ideal.map (algebraMap A B) (L i)) :=
    { multicenter := mc
      fin := inferInstance
      Ψ := id
      sec := id
      surj := by simp
      cond := by simp [mc, LargeIdeal, ideal_eq] }

    let iso1 : B[mc] ≃ₐ[B] (clo_mu _ Mu_c).Potion := (Mu_mor_iso _ Mu_c)

    have c_mem : ∀ i : ι, c i ∈
        familyPow (fun i ↦ Ideal.map (algebraMap A B) (L i)) (Finsupp.single i 1) := by
      intro i
      rw [show familyPow (fun i ↦ Ideal.map (algebraMap A B) (L i)) (Finsupp.single i 1) =
        Ideal.map (algebraMap A B) (L i) from familyPow_single _ _, ideal_eq]
      exact Ideal.mem_span_singleton_self _

    have hprod :
        (∏ a ∈ (Finset.univ (α := ι)).image
          (fun i => ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
            (Finsupp.single i 1) ⟨c i, c_mem i⟩), a) =
        ∏ i : ι, ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
            (Finsupp.single i 1) ⟨c i, c_mem i⟩ := by
      classical
      by_cases H : ∃ i, c i = 0
      · obtain ⟨i₀, hi₀⟩ := H
        have hz : (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
            (Finsupp.single i₀ 1) ⟨c i₀, c_mem i₀⟩ : Rees) = 0 := by
          rw [ReesAlgebra.single_eq_zero]
          exact Subtype.ext hi₀
        rw [Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ i₀)) hz,
          Finset.prod_eq_zero (Finset.mem_univ i₀) hz]
      · push_neg at H
        rw [Finset.prod_image]
        intro i _ j _ hij
        by_contra hne
        simp only at hij
        have hgi : (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
            (Finsupp.single i 1) ⟨c i, c_mem i⟩ : Rees) ≠ 0 := by
          rw [Ne, ReesAlgebra.single_eq_zero]
          simpa using H i
        have h1 := ReesAlgebra.single_has_degree (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (Finsupp.single i 1) ⟨c i, c_mem i⟩
        have h2 := ReesAlgebra.single_has_degree (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (Finsupp.single j 1) ⟨c j, c_mem j⟩
        rw [hij] at h1
        have hd := DirectSum.degree_eq_of_mem_mem _ h1 h2 (hij ▸ hgi)
        rw [Finsupp.single_eq_single_iff] at hd
        rcases hd with ⟨h, _⟩ | ⟨h, _⟩
        · exact hne h
        · exact absurd h one_ne_zero

    let iso2 : (clo_mu _ Mu_c).Potion ≃ₐ[B] HomogeneousSubmonoid.Potion
      (.closure {∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by simp [ideal_eq]; aesop⟩} (by
          rintro - rfl
          rw [ReesAlgebra.single_prod]
          refine ⟨∑ j, Finsupp.single j 1, ?_⟩
          simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply]
          rw [dif_pos]
          · simp only [ReesAlgebra.grading, LinearMap.mem_range, Subtype.exists]
            refine ⟨∏ x, c x, ?_, ?_⟩
            · rw [show Set.rangeSplitting (ρNatToInt ι) ⟨∑ j, Finsupp.single j 1, _⟩ = ∑ j, Finsupp.single j 1 from
                ρNatToInt_inj (by
                rw [Set.apply_rangeSplitting (ρNatToInt ι)]
                simp), familyPow_sum]
              simp_rw [familyPow_single]
              · apply Ideal.prod_mem_prod
                rintro i -
                rw [ideal_eq]
                exact Ideal.mem_span_singleton_self _
              refine ⟨∑ j, Finsupp.single j 1, ?_⟩
              ext i
              simp
            · fapply ReesAlgebra.single_eq
              refine ρNatToInt_inj ?_
              rw [Set.apply_rangeSplitting (ρNatToInt ι)]
              simp) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))) :=
      AlgEquiv.ofRingEquiv (f := HomogeneousSubmonoid.potionEquivProduct (clo_mu _ Mu_c)
        ((Finset.univ (α := ι)).image fun i => ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by simp [ideal_eq]; aesop⟩) (by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          refine ⟨Finsupp.single i 1, ?_⟩
          simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply]
          rw [dif_pos]
          rw [show Set.rangeSplitting (ρNatToInt ι) ⟨Finsupp.single i 1, _⟩ = Finsupp.single i 1 from
                ρNatToInt_inj (by
                rw [Set.apply_rangeSplitting (ρNatToInt ι)]
                simp)]
          simp only [ReesAlgebra.grading, LinearMap.mem_range, exists_apply_eq_apply]
          refine ⟨Finsupp.single i 1, ?_⟩
          ext i
          simp) (by
          delta clo_mu
          congr 1
          ext x
          simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            Set.mem_range]
          rfl))
        (fun z => HomogeneousSubmonoid.potionEquivProduct_algebraMap _ _ _ _
          (ReesAlgebra.degreeZeroIso' (fun i ↦ Ideal.map (algebraMap A B) (L i)) z)) |>.trans <|
      AlgEquiv.ofRingEquiv
        (f := HomogeneousSubmonoid.potionEquiv (by congr 1; rw [hprod]))
        (fun _ => rfl)

    have mem (i : ι) : c i ∈ Ideal.map (algebraMap A B) (L i) := by
      rw [ideal_eq]
      exact Ideal.mem_span_singleton_self (c i)
    change ∀ i, c i ∈ Submodule.span _ _ at mem
    simp_rw [Submodule.mem_span_iff_exists_finset_subset] at mem

    have c_repr (i : ι) : ∃ (lambda : A → B) (t : Finset A), (t : Set A) ⊆ L i ∧
      Function.support lambda ⊆ t ∧ ∑ a ∈ t, lambda a • algebraMap A B a = c i := by
      obtain ⟨f, t, ht, hf, eq⟩ := mem i
      choose x hx using ht
      let T : Finset A := Finset.image (fun a : t => x a.2) Finset.univ
      let lambda : A → B := fun a => if a ∈ T then f (algebraMap A B a) else 0
      refine ⟨lambda, T, ?_, ?_, ?_⟩
      · intro z hz
        simp only [Finset.univ_eq_attach, Finset.coe_image, Finset.coe_attach, Set.image_univ,
          Set.mem_range, Subtype.exists, T] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        specialize hx ha
        exact hx.1

      · intro z hz
        simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
          Subtype.exists, Function.mem_support, ne_eq, ite_eq_right_iff, forall_exists_index,
          not_forall, Classical.not_imp, exists_and_right, Finset.coe_image, Finset.coe_attach,
          Set.image_univ, Set.mem_range, lambda, T] at hz ⊢
        tauto
      simp only [T]
      rw [← eq]
      conv_rhs => rw [← Finset.sum_attach]
      fapply Finset.sum_image'

      rintro ⟨a, ha⟩ -
      simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists, smul_eq_mul, ite_mul, zero_mul, lambda, T]
      rw [if_pos]
      have ha' := hx ha
      rw [ha'.2]
      symm
      rw [Finset.sum_eq_single ⟨a, ha⟩]
      · rintro ⟨b, hb⟩
        simp only [Finset.mem_filter, Finset.mem_attach, true_and, ne_eq, Subtype.mk.injEq]
        intro eq
        apply_fun algebraMap A B at eq
        have hb' := hx hb
        rw [ha'.2, hb'.2] at eq
        tauto
      · simp only [Finset.mem_filter, Finset.mem_attach, and_self, not_true_eq_false,
        IsEmpty.forall_iff]
      use a, ha

    choose lambda t t_subset lambda_support EQ using c_repr

    have c_repr_rees (i : ι) :
      (∑ a ∈ (t i).attach,
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) 0 ⟨lambda i a.1, by simp⟩ *
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) (Finsupp.single i 1)
          ⟨algebraMap A B a.1, by
            simp only [familyPow_single', pow_one]
            exact Ideal.mem_map_of_mem _ (t_subset i a.2)⟩ : Rees) =
      (ReesAlgebra.single _ (Finsupp.single i 1) ⟨c i, by simp [ideal_eq]; aesop⟩ : Rees) := by
      simp_rw [ReesAlgebra.single_mul]
      rw [← map_sum]
      set X := _
      change ReesAlgebra.single _ _ X = _
      rw [show X = ⟨∑ x ∈ (t i).attach, lambda i x.1 * algebraMap A B x.1, by
        simp only [zero_add, familyPow_single', pow_one]
        apply sum_mem
        intro a _
        apply Ideal.mul_mem_left
        apply Ideal.mem_map_of_mem
        exact t_subset i a.2⟩ by ext; simp [X]]
      fapply ReesAlgebra.single_eq'
      · simp
      rw [Finset.sum_attach (t i) (fun x => lambda i x * algebraMap A B x), ← EQ]
      simp only [smul_eq_mul]

    have eq :
      (∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1) ⟨c i, by simp [ideal_eq]; aesop⟩ : Rees) =
      ∏ i : ι, (∑ a ∈ (t i).attach,
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) 0 ⟨lambda i a.1, by simp⟩ *
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) (Finsupp.single i 1)
          ⟨algebraMap A B a.1, by
            simp only [familyPow_single', pow_one]
            exact Ideal.mem_map_of_mem _ (t_subset i a.2)⟩ : Rees) :=
      Finset.prod_congr rfl fun i _ => (c_repr_rees i).symm

    rw [Finset.prod_sum] at eq

    set rhs_summand : ((a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) → Rees := _
    set rhs :=  ∑ p ∈ Finset.univ.pi (fun i => (t i).attach), rhs_summand p
    change _ = rhs at eq

    have rhs_eq (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
        rhs_summand p =
        ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (∑ j : ι, Finsupp.single j 1)
          ⟨∏ j : ι, lambda j (p j (Finset.mem_univ j)).1 *
              algebraMap A B (p j (Finset.mem_univ j)).1, by
            rw [familyPow_sum]
            refine Ideal.prod_mem_prod fun j _ => ?_
            rw [familyPow_single]
            exact Ideal.mul_mem_left _ _
              (Ideal.mem_map_of_mem _ (t_subset j (p j (Finset.mem_univ j)).2))⟩ := by
      show (∏ x ∈ Finset.univ.attach,
        (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i)) 0
            ⟨lambda x.1 (p x.1 x.2).1, by simp⟩ *
          ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i)) (Finsupp.single x.1 1)
            ⟨algebraMap A B (p x.1 x.2).1, by
              simp only [familyPow_single', pow_one]
              exact Ideal.mem_map_of_mem _ (t_subset x.1 (p x.1 x.2).2)⟩)) = _
      simp_rw [ReesAlgebra.single_mul]
      rw [ReesAlgebra.single_prod]
      fapply ReesAlgebra.single_eq'
      · simp_rw [zero_add]
        exact Finset.sum_attach Finset.univ (fun j => Finsupp.single j 1)
      · exact Finset.prod_attach Finset.univ
          (fun j => lambda j (p j (Finset.mem_univ j)).1 *
            algebraMap A B (p j (Finset.mem_univ j)).1)

    have hrho : (ρNatToInt ι) (∑ j : ι, Finsupp.single j 1) = ∑ i : ι, Finsupp.single i 1 := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext i
      simp [ρNatToInt_apply, Finsupp.single_apply]

    have hdeg' : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        rhs_summand p ∈ (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))
          (∑ i : ι, Finsupp.single i 1) := by
      intro p
      rw [rhs_eq p, ← hrho]
      exact ReesAlgebra.single_has_degree' _ _ _

    have hdeg : ∀ p ∈ Finset.univ.pi (fun i => (t i).attach),
        rhs_summand p ∈ (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))
          (∑ i : ι, Finsupp.single i 1) := fun p _ => hdeg' p

    have rhs_summand_hom : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        SetLike.IsHomogeneousElem
          (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) (rhs_summand p) :=
      fun p => ⟨_, hdeg' p⟩

    have rhs_hom : SetLike.IsHomogeneousElem
        (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) rhs := by
      refine ⟨∑ i : ι, Finsupp.single i 1, ?_⟩
      show (∑ p ∈ Finset.univ.pi (fun i => (t i).attach), rhs_summand p) ∈ _
      exact sum_mem fun p hp => hdeg p hp

    have prod_c_hom : SetLike.IsHomogeneousElem
        (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))
        (∏ i : ι, ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (Finsupp.single i 1) ⟨c i, by
            rw [familyPow_single, ideal_eq]
            exact Ideal.mem_span_singleton_self _⟩ : Rees) := by
      refine ⟨∑ i : ι, Finsupp.single i 1, ?_⟩
      rw [ReesAlgebra.single_prod, ← hrho]
      exact ReesAlgebra.single_has_degree' _ _ _

    have potionEquivB : ∀ {S T : HomogeneousSubmonoid
          (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))}
        (h : S = T) (z : B),
        HomogeneousSubmonoid.potionEquiv h (algebraMap B S.Potion z) =
          algebraMap B T.Potion z := by
      intro S T h z
      subst h
      rfl

    let iso3 : (.closure {∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by
          rw [familyPow_single, ideal_eq]
          exact Ideal.mem_span_singleton_self _⟩} (by rintro - rfl; exact prod_c_hom) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion ≃ₐ[B]
      (.closure {rhs} (by
        intro y hy
        simp only [Set.mem_singleton_iff] at hy
        rw [hy]
        exact rhs_hom) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion :=

      AlgEquiv.ofRingEquiv
        (f := HomogeneousSubmonoid.potionEquiv (by congr 1; rw [eq]))
        (potionEquivB _)

    let ISO := dilaIso.symm.trans <| iso1.trans iso2 |>.trans iso3

    let potionOfSum := (HomogeneousSubmonoid.closure {rhs} (by
        intro y hy
        simp only [Set.mem_singleton_iff] at hy
        rw [hy]
        exact rhs_hom) :
      HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap ↑A ↑B) (L i))).Potion

    let mor3 : Spec B ≅ Spec (CommRingCat.of <| potionOfSum) :=
    { hom := Spec.map <| CommRingCat.ofHom <| ISO.symm
      inv := Spec.map <| CommRingCat.ofHom <| ISO
      hom_inv_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        ext x
        exact ISO.symm_apply_apply x
      inv_hom_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
        refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
        exact RingHom.ext fun x => ISO.apply_symm_apply x }

    have hrel : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a})
        (mem : p ∈ Finset.univ.pi (fun i => (t i).attach)),
        HomogeneousSubmonoid.ElemIsRelevant (rhs_summand p)
          ⟨∑ i : ι, Finsupp.single i 1, hdeg p mem⟩ := by
      intro p mem
      classical
      set e := Fintype.equivFin ι with he
      refine HomogeneousSubmonoid.elemIsRelevant_of_homogeneous_of_factorisation
        (rhs_summand p) ⟨_, hdeg p mem⟩ (Fintype.card ι)
        (fun m => ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (Finsupp.single (e.symm m) 1)
          ⟨lambda (e.symm m) (p (e.symm m) (Finset.mem_univ _)).1 *
            algebraMap A B (p (e.symm m) (Finset.mem_univ _)).1, by
              rw [familyPow_single]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
                (t_subset _ (p (e.symm m) (Finset.mem_univ _)).2))⟩)
        (fun m => ρNatToInt ι (Finsupp.single (e.symm m) 1)) (fun m => ?_) ?_ 1 ?_
      · exact ReesAlgebra.single_has_degree' _ _ _
      · have hclosure : AddSubgroup.closure
            (Set.range (fun m => ρNatToInt ι (Finsupp.single (e.symm m) 1))) = ⊤ := by
          rw [eq_top_iff]
          rintro v -
          rw [← Finsupp.sum_single v]
          refine sum_mem fun j _ => ?_
          rw [show Finsupp.single j (v j) = (v j) • Finsupp.single j (1 : ℤ) by simp]
          refine zsmul_mem (AddSubgroup.subset_closure (Set.mem_range.2 ⟨e j, ?_⟩)) _
          ext i
          simp [ρNatToInt_apply, Finsupp.single_apply]
        rw [hclosure]
        infer_instance
      · rw [pow_one, rhs_eq p, ReesAlgebra.single_prod]
        fapply ReesAlgebra.single_eq'
        · exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
        · exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)

    obtain ⟨F, hF⟩  := sum_open_finset
      (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
      (s := Finset.univ.pi (fun i => (t i).attach)) (f := rhs_summand)
      (d := ∑ i : ι, Finsupp.single i 1) hdeg hrel

    let rhs_summand_simplifed : ((a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) → Rees := fun p =>
      ∏ x ∈ Finset.univ.attach,
    (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap ↑A ↑B) (L i)) (Finsupp.single x.1 1))
        ⟨(algebraMap A B) (p x.1 x.2).1, by
          simp only [familyPow_single', pow_one]
          exact Ideal.mem_map_of_mem _ (t_subset x.1 (p x.1 x.2).2)⟩

    have simplifed_eq : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        rhs_summand_simplifed p =
        ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (∑ j : ι, Finsupp.single j 1)
          ⟨∏ j : ι, algebraMap A B (p j (Finset.mem_univ j)).1, by
            rw [familyPow_sum]
            refine Ideal.prod_mem_prod fun j _ => ?_
            rw [familyPow_single]
            exact Ideal.mem_map_of_mem _ (t_subset j (p j (Finset.mem_univ j)).2)⟩ := by
      intro p
      show (∏ x ∈ Finset.univ.attach,
        (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i)) (Finsupp.single x.1 1))
          ⟨(algebraMap A B) (p x.1 x.2).1, by
            simp only [familyPow_single', pow_one]
            exact Ideal.mem_map_of_mem _ (t_subset x.1 (p x.1 x.2).2)⟩) = _
      rw [ReesAlgebra.single_prod]
      fapply ReesAlgebra.single_eq'
      · exact Finset.sum_attach Finset.univ (fun j => Finsupp.single j 1)
      · exact Finset.prod_attach Finset.univ
          (fun j => algebraMap A B (p j (Finset.mem_univ j)).1)

    have simplifed_hom : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        SetLike.IsHomogeneousElem
          (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))
          (rhs_summand_simplifed p) := by
      intro p
      refine ⟨∑ i : ι, Finsupp.single i 1, ?_⟩
      rw [simplifed_eq p, ← hrho]
      exact ReesAlgebra.single_has_degree' _ _ _

    have hmu : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        rhs_summand_simplifed p *
          ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap A B) (L i)) 0
            ⟨∏ j : ι, lambda j (p j (Finset.mem_univ j)).1, by simp⟩ = rhs_summand p := by
      intro p
      rw [rhs_eq p, simplifed_eq p, ReesAlgebra.single_mul]
      fapply ReesAlgebra.single_eq'
      · simp
      · rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ => mul_comm _ _

    have hbarle : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        (HomogeneousSubmonoid.closure {rhs_summand_simplifed p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact simplifed_hom p)).bar ≤
        (HomogeneousSubmonoid.closure {rhs_summand p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact rhs_summand_hom p)).bar := by
      intro p
      refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
        (le_of_eq (HomogeneousSubmonoid.bar_bar _))
      intro y hy
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hy
      refine pow_mem ?_ n
      exact ⟨simplifed_hom p, ⟨rhs_summand p, Submonoid.subset_closure rfl,
        ⟨_, (hmu p).symm⟩⟩⟩

    let aux0_component (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand p}
          (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact rhs_summand_hom p) :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion) ⟶
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand_simplifed p}
          (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact simplifed_hom p) :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion) :=

      Spec.map <| CommRingCat.ofHom <|
        (HomogeneousSubmonoid.closure {rhs_summand p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact rhs_summand_hom p)).equivBarPotion.symm.toRingHom.comp
          ((HomogeneousSubmonoid.potionMapOfLE _ _ (hbarle p)).comp
            (HomogeneousSubmonoid.closure {rhs_summand_simplifed p} (by
              intro y hy
              simp only [Set.mem_singleton_iff] at hy
              rw [hy]
              exact simplifed_hom p)).equivBarPotion.toRingHom)

    let rhs_summand_ReesA : ((a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) →
        ReesAlgebra fun i ↦ L i := fun p =>
      ∏ x ∈ Finset.univ.attach,
      (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single x.1 1))
        ⟨(p x.1 x.2).1, by
          simp only [familyPow_single', pow_one]
          exact t_subset x.1 (p x.1 x.2).2⟩

    have ReesA_eq : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        rhs_summand_ReesA p =
        ReesAlgebra.single (fun i ↦ L i) (∑ j : ι, Finsupp.single j 1)
          ⟨∏ j : ι, (p j (Finset.mem_univ j)).1, by
            rw [familyPow_sum]
            refine Ideal.prod_mem_prod fun j _ => ?_
            rw [familyPow_single]
            exact t_subset j (p j (Finset.mem_univ j)).2⟩ := by
      intro p
      show (∏ x ∈ Finset.univ.attach,
        (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single x.1 1))
          ⟨(p x.1 x.2).1, by
            simp only [familyPow_single', pow_one]
            exact t_subset x.1 (p x.1 x.2).2⟩) = _
      rw [ReesAlgebra.single_prod]
      fapply ReesAlgebra.single_eq'
      · exact Finset.sum_attach Finset.univ (fun j => Finsupp.single j 1)
      · exact Finset.prod_attach Finset.univ (fun j => (p j (Finset.mem_univ j)).1)

    have ReesA_hom : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        SetLike.IsHomogeneousElem (ReesAlgebra.intGrading fun i ↦ (L i))
          (rhs_summand_ReesA p) := by
      intro p
      refine ⟨∑ i : ι, Finsupp.single i 1, ?_⟩
      rw [ReesA_eq p, ← hrho]
      exact ReesAlgebra.single_has_degree' _ _ _

    let Φ : GradedRingHom (ReesAlgebra.intGrading fun i ↦ L i)
        (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) :=
      ReesAlgebra.mapGraded (fun i ↦ L i) (algebraMap A B)

    have hmapΦ : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        Φ (rhs_summand_ReesA p) = rhs_summand_simplifed p := by
      intro p
      show ReesAlgebra.map (fun i ↦ L i) (algebraMap A B)
        (∏ x ∈ Finset.univ.attach,
          (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single x.1 1))
            ⟨(p x.1 x.2).1, by
              simp only [familyPow_single', pow_one]
              exact t_subset x.1 (p x.1 x.2).2⟩) = _
      rw [map_prod]
      exact Finset.prod_congr rfl fun x _ => ReesAlgebra.map_single _ _ _ _

    have hclos : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        (HomogeneousSubmonoid.closure {rhs_summand_ReesA p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact ReesA_hom p)).map Φ =
        HomogeneousSubmonoid.closure {rhs_summand_simplifed p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact simplifed_hom p) := by
      intro p
      apply HomogeneousSubmonoid.toSubmonoid_injective
      rw [HomogeneousSubmonoid.map_toSubmonoid]
      show Submonoid.map Φ (Submonoid.closure {rhs_summand_ReesA p}) = _
      rw [MonoidHom.map_mclosure, Set.image_singleton, hmapΦ p]
      rfl

    let aux1_component  (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand_simplifed p}
          (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact simplifed_hom p) :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion) ⟶
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand_ReesA p}
          (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact ReesA_hom p) :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ (L i))).Potion) :=

      Spec.map <| CommRingCat.ofHom <|
        HomogeneousSubmonoid.potionToMapOfBase _ _ Φ (fun x hx => by
          have hle : Submonoid.closure {rhs_summand_ReesA p} ≤
              Submonoid.comap Φ (Submonoid.closure {rhs_summand_simplifed p}) := by
            rw [Submonoid.closure_le]
            rintro - rfl
            simp only [Submonoid.coe_comap, Set.mem_preimage, SetLike.mem_coe]
            rw [hmapΦ p]
            exact Submonoid.subset_closure rfl
          exact hle hx)

    let mc' (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) : Multicenter A :=
    { index := ι
      ideal i := L i
      elem i := (p i (by simp)).1 }

    let mu' (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) : Mu L :=
    { multicenter := mc' p
      fin := inferInstance
      Ψ := id
      sec := id
      surj := by simp
      cond := by
        intro i
        show L i + Ideal.span {((p i (by simp)).1 : A)} = L i
        rw [Ideal.add_eq_sup, sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
        exact t_subset i (p i (by simp)).2 }

    let genA (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) (i : ι) :
        ReesAlgebra (fun i ↦ L i) :=
      ReesAlgebra.single (fun i ↦ L i) (Finsupp.single i 1)
        ⟨(p i (Finset.mem_univ i)).1, by
          simp only [familyPow_single', pow_one]
          exact t_subset i (p i (Finset.mem_univ i)).2⟩

    have hgenA : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        rhs_summand_ReesA p = ∏ i : ι, genA p i := by
      intro p
      show (∏ x ∈ Finset.univ.attach,
        (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single x.1 1))
          ⟨(p x.1 x.2).1, by
            simp only [familyPow_single', pow_one]
            exact t_subset x.1 (p x.1 x.2).2⟩) = _
      exact Finset.prod_attach Finset.univ (fun i => genA p i)

    have hprodA : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        (∏ a ∈ Finset.univ.image (genA p), a) = rhs_summand_ReesA p := by
      intro p
      classical
      rw [hgenA p]
      by_cases H : ∃ i, ((p i (Finset.mem_univ i)).1 : A) = 0
      · obtain ⟨i₀, hi₀⟩ := H
        have hz : genA p i₀ = 0 := by
          show ReesAlgebra.single _ _ _ = 0
          rw [ReesAlgebra.single_eq_zero]
          exact Subtype.ext hi₀
        rw [Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ i₀)) hz,
          Finset.prod_eq_zero (Finset.mem_univ i₀) hz]
      · push_neg at H
        rw [Finset.prod_image]
        intro i _ j _ hij
        by_contra hne
        have hgi : genA p i ≠ 0 := by
          show ReesAlgebra.single _ _ _ ≠ 0
          rw [Ne, ReesAlgebra.single_eq_zero]
          simpa using H i
        have h1 := ReesAlgebra.single_has_degree (fun i ↦ L i) (Finsupp.single i 1)
          ⟨(p i (Finset.mem_univ i)).1, by
            simp only [familyPow_single', pow_one]
            exact t_subset i (p i (Finset.mem_univ i)).2⟩
        have h2 := ReesAlgebra.single_has_degree (fun i ↦ L i) (Finsupp.single j 1)
          ⟨(p j (Finset.mem_univ j)).1, by
            simp only [familyPow_single', pow_one]
            exact t_subset j (p j (Finset.mem_univ j)).2⟩
        rw [show (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single i 1)
          ⟨(p i (Finset.mem_univ i)).1, _⟩ : ReesAlgebra fun i ↦ L i) = genA p i from rfl] at h1
        rw [show (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single j 1)
          ⟨(p j (Finset.mem_univ j)).1, _⟩ : ReesAlgebra fun i ↦ L i) = genA p j from rfl] at h2
        rw [hij] at h1
        have hd := DirectSum.degree_eq_of_mem_mem _ h1 h2 (hij ▸ hgi)
        rw [Finsupp.single_eq_single_iff] at hd
        rcases hd with ⟨h, _⟩ | ⟨h, _⟩
        · exact hne h
        · exact absurd h one_ne_zero

    have hcloA : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        clo_mu L (mu' p) = HomogeneousSubmonoid.closure
          (𝒜 := ReesAlgebra.intGrading fun i ↦ L i)
          ↑(Finset.univ.image (genA p)) (by
            intro y hy
            simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
            obtain ⟨i, rfl⟩ := hy
            exact ⟨_, ReesAlgebra.single_has_degree' _ _ _⟩) := by
      intro p
      delta clo_mu
      congr 1
      ext x
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range]
      rfl

    have potionEquivA : ∀ {S T : HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ L i)}
        (h : S = T) (z : A),
        HomogeneousSubmonoid.potionEquiv h (algebraMap A S.Potion z) =
          algebraMap A T.Potion z := by
      intro S T h z
      subst h
      rfl

    have hbarA : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ L i)) (z : A),
        S.equivBarPotion (algebraMap A S.Potion z) = algebraMap A S.bar.Potion z := by
      intro S z
      rw [HomogeneousSubmonoid.equivBarPotion_apply]
      rfl

    have hprodEquivA : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ L i))
        (s : Finset (ReesAlgebra fun i ↦ L i)) (s_hom) (S_eq) (z : A),
        S.potionEquivProduct s s_hom S_eq (algebraMap A S.Potion z) = algebraMap A _ z := by
      intro S s s_hom S_eq z
      simp only [HomogeneousSubmonoid.potionEquivProduct, RingEquiv.coe_trans, Function.comp_apply]
      rw [hbarA, potionEquivA, ← hbarA]
      exact RingEquiv.symm_apply_apply _ _

    let aux2_ring_version (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
      (.closure (𝒜 := ReesAlgebra.intGrading fun i ↦ (L i))
          {rhs_summand_ReesA p} (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact ReesA_hom p) :
            HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ (L i))).Potion ≃ₐ[A]
      (clo_mu L (mu' p)).Potion :=
      AlgEquiv.ofRingEquiv
        (f := (HomogeneousSubmonoid.potionEquiv (by
            congr 1
            rw [← hprodA p])).trans
          ((clo_mu L (mu' p)).potionEquivProduct _ _ (hcloA p)).symm)
        (by
          intro z
          simp only [RingEquiv.coe_trans, Function.comp_apply]
          rw [potionEquivA, ← hprodEquivA (clo_mu L (mu' p)) _ _ (hcloA p) z]
          exact RingEquiv.symm_apply_apply _ _)

    let aux2_component (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand_ReesA p}
          (by
            intro y hy
            simp only [Set.mem_singleton_iff] at hy
            rw [hy]
            exact ReesA_hom p) :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ (L i))).Potion) ≅
      Spec (CommRingCat.of <| (clo_mu L (mu' p)).Potion) :=
      { hom := Spec.map <| CommRingCat.ofHom <| (aux2_ring_version p).symm.toRingHom
        inv := Spec.map <| CommRingCat.ofHom <| (aux2_ring_version p).toRingHom
        hom_inv_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
          refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
          exact RingHom.ext fun x => (aux2_ring_version p).symm_apply_apply x
        inv_hom_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
          refine Eq.trans (congrArg CommRingCat.ofHom ?_) CommRingCat.ofHom_id
          exact RingHom.ext fun x => (aux2_ring_version p).apply_symm_apply x }

    let aux3_component (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}) :
        Spec (CommRingCat.of <| (clo_mu L (mu' p)).Potion) ⟶ BlMu L :=
      (GoodPotionIngredient.glueData (τ := Mu L) (map_index L)).ι (mu' p)

    letI algAPotion : ∀ (S : HomogeneousSubmonoid
        (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))),
        Algebra A (CommRingCat.of S.Potion) :=
      fun S => RingHom.toAlgebra ((algebraMap B S.Potion).comp (algebraMap A B))

    letI potionOverSpecA : ∀ (S : HomogeneousSubmonoid
        (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))),
        (Spec (CommRingCat.of S.Potion)).Over (Spec A) :=
      fun S => ⟨Spec.map (CommRingCat.ofHom
        ((algebraMap B S.Potion).comp (algebraMap A B)))⟩

    have hmapA : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading
        fun i ↦ Ideal.map (algebraMap A B) (L i))) (i : ι),
        Ideal.map (algebraMap A (CommRingCat.of S.Potion)) (L i) =
          Ideal.span {algebraMap B S.Potion (c i)} := by
      intro S i
      show Ideal.map ((algebraMap B S.Potion).comp (algebraMap A B)) (L i) = _
      rw [← Ideal.map_map, ideal_eq i, Ideal.map_span, Set.image_singleton]

    have hnzdA : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading
        fun i ↦ Ideal.map (algebraMap A B) (L i))) (i : ι),
        algebraMap B S.Potion (c i) ∈ nonZeroDivisors S.Potion := fun S i =>
      ReesAlgebra.potion_algebraMap_mem_nonZeroDivisors _ S (by simpa using mc_nzd i)

    have potionOver_eq : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading
        fun i ↦ Ideal.map (algebraMap A B) (L i))),
        (Spec (CommRingCat.of S.Potion) ↘ Spec A) =
          Spec.map (CommRingCat.ofHom ((algebraMap B S.Potion).comp (algebraMap A B))) :=
      fun _ => rfl

    have aux3_over : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        aux3_component p ≫ (BlMu L ↘ Spec A) =
          Spec.map (CommRingCat.ofHom (algebraMap A (clo_mu L (mu' p)).Potion)) :=
      fun p => BlMu_ι_over A L (mu' p)

    have halgA : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ L i)) (z : A),
        algebraMap A S.Potion z =
          algebraMap ((ReesAlgebra.intGrading fun i ↦ L i) 0) S.Potion
            (ReesAlgebra.degreeZeroIso' (fun i ↦ L i) z) := fun _ _ => rfl

    have halgB : ∀ (S : HomogeneousSubmonoid (ReesAlgebra.intGrading
          fun i ↦ Ideal.map (algebraMap A B) (L i))) (w : B),
        algebraMap B S.Potion w =
          algebraMap ((ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) 0) S.Potion
            (ReesAlgebra.degreeZeroIso' (fun i ↦ Ideal.map (algebraMap A B) (L i)) w) :=
      fun _ _ => rfl

    have hΦ0 : ∀ (z : A),
        (⟨Φ (ReesAlgebra.degreeZeroIso' (fun i ↦ L i) z).1,
            Φ.map_mem (ReesAlgebra.degreeZeroIso' (fun i ↦ L i) z).2⟩ :
          (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) 0) =
        ReesAlgebra.degreeZeroIso' (fun i ↦ Ideal.map (algebraMap A B) (L i))
          (algebraMap A B z) := by
      intro z
      apply Subtype.ext
      show ReesAlgebra.map (fun i ↦ L i) (algebraMap A B)
        (ReesAlgebra.single (fun i ↦ L i) 0 ⟨z, by simp⟩) = _
      simp only [ReesAlgebra.map_single, ReesAlgebra.degreeZeroIso'_apply]

    have chart_over : ∀ (p : (a : ι) → a ∈ Finset.univ → {x : A // x ∈ t a}),
        Scheme.Hom.IsOver (aux0_component p ≫ aux1_component p ≫ (aux2_component p).hom ≫
          aux3_component p) (Spec A) := by
      intro p
      refine ⟨?_⟩
      rw [Category.assoc, Category.assoc, Category.assoc, aux3_over p]
      simp only [aux0_component, aux1_component, aux2_component, potionOverSpecA,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
      simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
        AlgEquiv.coe_ringEquiv']
      rw [AlgEquiv.commutes, halgA, HomogeneousSubmonoid.potionToMapOfBase_algebraMap,
        hΦ0 z, HomogeneousSubmonoid.equivBarPotion_algebraMap,
        HomogeneousSubmonoid.potionMapOfLE_algebraMap,
        HomogeneousSubmonoid.equivBarPotion_symm_algebraMap, halgB]

    let glued :
        unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand) (s := Finset.univ.pi (fun i => (t i).attach)) hdeg hrel ⟶ BlMu L :=
      Multicoequalizer.desc _ _
        (fun p => aux0_component p.1  ≫
          aux1_component p.1 ≫
          (aux2_component p.1).hom ≫
          aux3_component p.1)

        (by
          rintro ⟨p, q⟩
          refine @ProjBlowup_UnivProp_unicity_affine ι _ _ A L fin _ (potionOverSpecA _)
            (loc_isCars_of_principal A _ L (fun i => algebraMap B _ (c i))
              (hmapA _) (hnzdA _)) _ _ ⟨?_⟩ ⟨?_⟩
          · simp only [MultispanShape.prod_fst]
            rw [Category.assoc, (chart_over p.1).comp_over, potionOver_eq, potionOver_eq]
            simp only [CategoryTheory.GlueData.diagram_fst, GoodPotionIngredient.glueData_f,
              ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun w => rfl))
          · simp only [MultispanShape.prod_snd]
            rw [Category.assoc, (chart_over q.1).comp_over, potionOver_eq, potionOver_eq]
            simp only [CategoryTheory.GlueData.diagram_snd, GoodPotionIngredient.glueData_f,
              GoodPotionIngredient.glueData_t, Category.assoc,
              ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun w => rfl)))

    let final : Spec B ⟶ BlMu L :=
      Spec.map (CommRingCat.ofHom <| ISO.symm.toRingHom) ≫ F ≫ glued

    have glued_over : glued ≫ (BlMu L ↘ Spec A) =
        ((unionSpecFinset
            (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
            (d := ∑ i : ι, Finsupp.single i 1) (f := rhs_summand)
            (s := Finset.univ.pi (fun i => (t i).attach)) hdeg hrel) ↘
          Spec (CommRingCat.of
            ((ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)) 0))) ≫
        Spec.map (CommRingCat.ofHom (ReesAlgebra.degreeZeroIso'
          (fun i ↦ Ideal.map (algebraMap A B) (L i)) : B →+* _)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
      refine Multicoequalizer.hom_ext _ _ _ (fun p => ?_)
      rw [← Category.assoc]
      erw [Multicoequalizer.π_desc]
      rw [(chart_over p.1).comp_over, potionOver_eq, ← Category.assoc, ← Category.assoc]
      erw [Multicoequalizer.π_desc]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun w => rfl))

    have final_over : Scheme.Hom.IsOver final (Spec A) := by
      refine ⟨?_⟩
      show (Spec.map (CommRingCat.ofHom <| ISO.symm.toRingHom) ≫ F ≫ glued) ≫
        (BlMu L ↘ Spec A) = _
      have hsum : (Spec (CommRingCat.of (sum_potion_finset
            (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
            rhs_summand (Finset.univ.pi fun i ↦ (t i).attach) hdeg hrel)) ↘
          Spec (CommRingCat.of ((ReesAlgebra.intGrading
            fun i ↦ Ideal.map (algebraMap A B) (L i)) 0))) =
          Spec.map (CommRingCat.ofHom (algebraMap _ _)) := rfl
      rw [Category.assoc, Category.assoc, glued_over, ← Category.assoc F, hF.comp_over, hsum,
        specB_over_specA_eq]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
      exact ISO.symm.commutes (algebraMap A B z)

    exact ⟨B, Z.cov.map γ, over0, ⟨rfl⟩, Z.cov.map_prop γ, final, Z.cov.covers x, final_over⟩

  choose B emb oB emb_over_A o_emb φ mem over using gluing_material

  let TCover : Scheme.AffineCover (IsOpenImmersion) T :=
  { J := T
    obj x := B x
    map x := emb x
    f := id
    covers := mem
    map_prop := o_emb }

  let (x y : T) : (pullback (emb x) (emb y)).Over (Spec A) :=
  ⟨pullback.fst _ _ ≫ _ ↘ Spec A⟩

  let φGlobal : T ⟶ BlMu L :=
    TCover.cover.glueMorphisms
      (fun x => φ x)
      (by
        rintro (x y : T)
        simp only [Scheme.AffineCover.cover_obj, Scheme.AffineCover.cover_map, TCover]
        haveI : IsOpenImmersion (emb x) := o_emb x
        haveI : IsOpenImmersion (emb y) := o_emb y
        refine ProjBlowup_UnivProp_unicity_affine A L (φ := pullback.fst (emb x) (emb y) ≫ φ x)
          (φ' := pullback.snd (emb x) (emb y) ≫ φ y)
          ?_ ?_ ?_
        ·
          haveI : Flat ((pullback.fst _ _ ≫ emb x: pullback (emb x) (emb y)  ⟶ T)) :=
            AlgebraicGeometry.Flat.comp _ _
          have car2 := pullback_IsCars
            (f := (pullback.fst _ _ ≫ emb x : pullback (emb x) (emb y)  ⟶ T)) _ _ cond
          rw [← pullback_assoc] at car2
          convert car2 using 2
          rw [Category.assoc, (emb_over_A x).comp_over]
          rfl
        · exact ⟨by rw [Category.assoc, (over x).comp_over]; rfl⟩
        · refine ⟨?_⟩
          rw [Category.assoc, (over y).comp_over]
          show pullback.snd (emb x) (emb y) ≫ (Spec (B y) ↘ Spec A) =
            pullback.fst (emb x) (emb y) ≫ (Spec (B x) ↘ Spec A)
          rw [← (emb_over_A x).comp_over, ← (emb_over_A y).comp_over,
            ← Category.assoc, ← Category.assoc, pullback.condition])
  use φGlobal

  refine ⟨TCover.cover.hom_ext _ _ (fun x => ?_)⟩
  rw [← Category.assoc, show TCover.cover.map x ≫ φGlobal = φ x from
    TCover.cover.ι_glueMorphisms _ _ x]
  exact ((over x).comp_over).trans ((emb_over_A x).comp_over).symm

lemma ProjBlowup_UnivProp_existence_affine
    (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃ φ : T ⟶ BlMu L, Scheme.Hom.IsOver φ (Spec A) := by

  exact ProjBlowup_UnivProp_existence_affine_preclo A L cond

lemma ProjBlowup_UnivProp_existence_affine_restrict
    (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T)
    {T' : Scheme} [T'.Over (Spec A)] (j : T' ⟶ T) [IsOpenImmersion j]
    (hj : Scheme.Hom.IsOver j (Spec A))
    (cond' : pullback_Clos (T' ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T') :
    j ≫ (ProjBlowup_UnivProp_existence_affine A L cond).choose =
      (ProjBlowup_UnivProp_existence_affine A L cond').choose := by
  apply ProjBlowup_UnivProp_unicity_affine A L cond'
  · rw [Scheme.Hom.isOver_iff, Category.assoc]
    have h1 := (ProjBlowup_UnivProp_existence_affine A L cond).choose_spec
    rw [Scheme.Hom.isOver_iff] at h1
    rw [h1]
    exact hj.1
  · exact (ProjBlowup_UnivProp_existence_affine A L cond').choose_spec

lemma ProjBlowup_UnivProp_affine
  (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃! φ :  T ⟶ BlMu L,  Scheme.Hom.IsOver φ (Spec A) := by
  obtain ⟨φ, hφ⟩ := ProjBlowup_UnivProp_existence_affine A L cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact ProjBlowup_UnivProp_unicity_affine A L cond φ φ' hφ hφ' |>.symm

def ProjBlowup_φ (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    T ⟶ BlMu L :=
  Classical.choose (ProjBlowup_UnivProp_affine A L cond)

def ProjBlowup_φ_over (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    Scheme.Hom.IsOver (ProjBlowup_φ A L cond) (Spec A) :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.1

def ProjBlowup_φ_uniq (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∀ φ' : T ⟶ BlMu L, Scheme.Hom.IsOver φ' (Spec A) → φ' = ProjBlowup_φ A L cond :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.2

def  ProjBlowup_is_conceptual_blowups_affine (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι] :
    conceptual_blowup (loc_to_Clos A L) where
  scheme := BlMu L
  over := inferInstance
  in_cars := blowups_Cars A L
  φ T _ cond := ProjBlowup_φ A L cond
  φ_over T _ cond := ProjBlowup_φ_over A L cond
  φ_uniq T _ cond φ' hφ' := ProjBlowup_φ_uniq A L cond φ' hφ'

open Multicenter

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

lemma dilatation_ring_flat_base_change (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B] (F: Multicenter A)
    (flat : RingHom.Flat (algebraMap A B)) : Subsingleton ((B ⊗[A] A[F]) ≃ₐ[B] B[image_mult F]) := by

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

    (F: Multicenter A) :
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

lemma loc_to_Clos_baseChange (A R : CommRingCat.{u+1}) [Algebra A R] (L : ι → Ideal A) :
    loc_to_Clos R (fun i => Ideal.map (algebraMap A R) (L i)) =
      pullback_Clos (Spec R ↘ Spec A) (loc_to_Clos A L) :=
  Quotient.sound ⟨loc_to_PreClos_baseChange A R L⟩

set_option maxHeartbeats 3200000 in
lemma base_change_Bl_open [Fintype ι] (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] (L: ι → Ideal A) :
    ∃! (e : pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A) ≅

    BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))), Scheme.Hom.IsOver e.hom (Spec B) := by
  classical
  set L' : ι → Ideal B := fun i => Ideal.map (algebraMap A B) (L i) with hL'
  letI : (BlMu L').Over (Spec A) := ⟨(BlMu L' ↘ Spec B) ≫ (Spec B ↘ Spec A)⟩

  have condPA : IsCars _ (pullback_Clos
      ((pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A)) ↘ Spec A) (loc_to_Clos A L)) := by
    rw [pullback_over_base, pullback_assoc]
    exact pullback_IsCars _ _ _ (blowups_Cars A L)

  have condPB : IsCars _ (pullback_Clos
      ((pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A)) ↘ Spec B) (loc_to_Clos B L')) := by
    rw [pullback_over_right, hL', loc_to_Clos_baseChange A B L, ← pullback_assoc,
      ← pullback.condition, ← pullback_over_base]
    exact condPA

  have condBlA : IsCars _ (pullback_Clos ((BlMu L') ↘ Spec A) (loc_to_Clos A L)) := by
    show IsCars _ (pullback_Clos ((BlMu L' ↘ Spec B) ≫ (Spec B ↘ Spec A)) _)
    rw [pullback_assoc, ← loc_to_Clos_baseChange A B L]
    exact blowups_Cars B L'
  obtain ⟨φ, hφ, hφuniq⟩ := ProjBlowup_UnivProp_affine B L' condPB
  obtain ⟨ψ₀, hψ₀, -⟩ := ProjBlowup_UnivProp_affine A L condBlA
  have hψ₀' : ψ₀ ≫ (BlMu L ↘ Spec A) = (BlMu L' ↘ Spec B) ≫ (Spec B ↘ Spec A) := by
    rw [hψ₀.comp_over]
    rfl
  refine ⟨⟨φ, pullback.lift ψ₀ (BlMu L' ↘ Spec B) hψ₀', ?_, ?_⟩, ⟨?_⟩, ?_⟩
  ·
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine ProjBlowup_UnivProp_unicity_affine A L condPA _ _ ⟨?_⟩ ⟨rfl⟩
      rw [Category.assoc, hψ₀.comp_over]
      show φ ≫ ((BlMu L' ↘ Spec B) ≫ (Spec B ↘ Spec A)) = _
      rw [← Category.assoc, hφ.comp_over, pullback_over_right, ← pullback.condition,
        ← pullback_over_base]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact hφ.comp_over
  ·
    refine (ProjBlowup_UnivProp_affine B L' (blowups_Cars B L')).unique ⟨?_⟩ ⟨Category.id_comp _⟩
    rw [Category.assoc, hφ.comp_over, pullback_over_right, pullback.lift_snd]
  · exact hφ.1
  · intro e he
    ext1
    exact hφuniq e.hom he

lemma lemma_open_eq (U : Scheme) (i : U ⟶ X) [IsOpenImmersion i]

  (f: U ⟶ U) (hi : i = f ≫ i) : f = 𝟙 _:= by

  haveI : Mono i := inferInstance
  rw [← cancel_mono i, Category.id_comp]
  exact hi.symm

def ideal_loc (X: Scheme) (Z: PreClos X) (γ : Z.cov.J) : Z.indnumb → Ideal (Z.cov.obj γ) :=
  fun (i : Z.indnumb) => Z.ideal i γ

def Proj_loc  (X: Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  BlMu (A := Z.cov.obj γ) (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) (Spec (Z.cov.obj γ)) :=
  BlMuOverSpec (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) X where
  hom := (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) ≫
    Z.cov.map γ

def open_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : Scheme :=
  pullback (Z.cov.map γ) (Z.cov.map δ)

def open_pair_map (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : open_pair X Z  γ δ  ⟶ X :=
  (pullback.fst  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map γ)

lemma open_pair_map_equal (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
    open_pair_map X Z  γ δ  =
    (pullback.snd  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map δ)  := by

  exact pullback.condition

lemma open_pair_map_is_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
  IsOpenImmersion <| open_pair_map X Z γ δ := by

    delta open_pair_map
    haveI : IsOpenImmersion (Z.cov.map γ) := Z.cov.map_prop γ
    haveI : IsOpenImmersion (Z.cov.map δ) := Z.cov.map_prop δ
    infer_instance

def Proj_loc_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  : Scheme :=
    pullback (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))

abbrev restrictToOpen {X X' U S : Scheme} [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
  (i : U ⟶ S) : (pullback (X ↘ S) i) ⟶ (pullback (X' ↘ S) i) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

instance (X X' U S : Scheme) [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
    (i : U ⟶ S) :
    Scheme.Hom.IsOver (restrictToOpen f i) U := by
  simp only [Scheme.Hom.isOver_iff]
  delta restrictToOpen
  change _ ≫ (pullback.snd _ _) = pullback.snd _ _
  simp

@[reassoc]
lemma restrictToOpen_fst {X X' U S : Scheme} [X.Over S] [X'.Over S] (f : X ⟶ X')
    [Scheme.Hom.IsOver f S] (i : U ⟶ S) :
    restrictToOpen f i ≫ pullback.fst (X' ↘ S) i = pullback.fst (X ↘ S) i ≫ f := by
  delta restrictToOpen
  rw [pullback.lift_fst]

@[reassoc]
lemma restrictToOpen_snd {X X' U S : Scheme} [X.Over S] [X'.Over S] (f : X ⟶ X')
    [Scheme.Hom.IsOver f S] (i : U ⟶ S) :
    restrictToOpen f i ≫ pullback.snd (X' ↘ S) i = pullback.snd (X ↘ S) i := by
  delta restrictToOpen
  rw [pullback.lift_snd, Category.comp_id]

noncomputable def pullbackCompIso {W X Y Z : Scheme} (k : W ⟶ Z) (a : X ⟶ Y) (e : Y ≅ Z) :
    pullback k (a ≫ e.hom) ≅ pullback (k ≫ e.inv) a where
  hom := pullback.lift (pullback.fst k (a ≫ e.hom)) (pullback.snd k (a ≫ e.hom))
    (by
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
        e.hom_inv_id, Category.comp_id])
  inv := pullback.lift (pullback.fst (k ≫ e.inv) a) (pullback.snd (k ≫ e.inv) a)
    (by
      have h := pullback.condition (f := k ≫ e.inv) (g := a)
      have h2 := congrArg (· ≫ e.hom) h
      simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h2
      exact h2)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_ <;> simp

set_option maxHeartbeats 1000000 in

noncomputable def pullbackDoubleFstIso {A B D S : Scheme} (f : A ⟶ S) (g : B ⟶ S) (h : D ⟶ S) :
    pullback (pullback.fst f g) (pullback.fst f h) ≅
      pullback f (pullback.fst g h ≫ g) where
  hom := pullback.lift
    (pullback.fst _ _ ≫ pullback.fst f g)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd f g) (pullback.snd _ _ ≫ pullback.snd f h)
      (by
        have c1 := pullback.condition (f := f) (g := g)
        have c2 := pullback.condition (f := f) (g := h)
        have c3 := pullback.condition (f := pullback.fst f g) (g := pullback.fst f h)
        calc (pullback.fst (pullback.fst f g) (pullback.fst f h) ≫ pullback.snd f g) ≫ g
            = pullback.fst (pullback.fst f g) (pullback.fst f h) ≫ (pullback.fst f g ≫ f) := by
              rw [Category.assoc, ← c1]
          _ = (pullback.fst (pullback.fst f g) (pullback.fst f h) ≫ pullback.fst f g) ≫ f := by
              rw [Category.assoc]
          _ = (pullback.snd (pullback.fst f g) (pullback.fst f h) ≫ pullback.fst f h) ≫ f := by
              rw [c3]
          _ = pullback.snd (pullback.fst f g) (pullback.fst f h) ≫ (pullback.fst f h ≫ f) := by
              rw [Category.assoc]
          _ = pullback.snd (pullback.fst f g) (pullback.fst f h) ≫ (pullback.snd f h ≫ h) := by
              rw [c2]
          _ = (pullback.snd (pullback.fst f g) (pullback.fst f h) ≫ pullback.snd f h) ≫ h := by
              rw [Category.assoc]))
    (by
      rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])
  inv := pullback.lift
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst g h)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd g h)
      (by
        rw [Category.assoc,
          show pullback.snd g h ≫ h = pullback.fst g h ≫ g from
            (pullback.condition (f := g) (g := h)).symm]
        exact pullback.condition))
    (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · apply pullback.hom_ext <;>
        simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · apply pullback.hom_ext <;>
        simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]

set_option maxHeartbeats 1000000 in

noncomputable def pullbackSndCompIso {X Y Z W : Scheme} (f : X ⟶ Z) (a : Y ⟶ Z) (b : W ⟶ Y) :
    pullback f (b ≫ a) ≅ pullback (pullback.snd f a) b where
  hom := pullback.lift
    (pullback.lift (pullback.fst f (b ≫ a)) (pullback.snd f (b ≫ a) ≫ b)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.snd f (b ≫ a))
    (by rw [pullback.lift_snd])
  inv := pullback.lift
    (pullback.fst (pullback.snd f a) b ≫ pullback.fst f a)
    (pullback.snd (pullback.snd f a) b)
    (by
      have c1 := pullback.condition (f := f) (g := a)
      have c2 := pullback.condition (f := pullback.snd f a) (g := b)
      calc (pullback.fst (pullback.snd f a) b ≫ pullback.fst f a) ≫ f
          = pullback.fst (pullback.snd f a) b ≫ (pullback.fst f a ≫ f) := by rw [Category.assoc]
        _ = pullback.fst (pullback.snd f a) b ≫ (pullback.snd f a ≫ a) := by rw [c1]
        _ = (pullback.fst (pullback.snd f a) b ≫ pullback.snd f a) ≫ a := by rw [Category.assoc]
        _ = (pullback.snd (pullback.snd f a) b ≫ b) ≫ a := by rw [c2]
        _ = pullback.snd (pullback.snd f a) b ≫ b ≫ a := by rw [Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    all_goals first
      | (apply pullback.hom_ext <;>
          simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc])
      | simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    all_goals first
      | (apply pullback.hom_ext <;>
          simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc])
      | simp [pullback.condition, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]

lemma existsUnique_iso_transport {F F' G S : Scheme} [F.Over S] [F'.Over S] [G.Over S]
    (σ : F' ≅ F) (hσ : Scheme.Hom.IsOver σ.hom S)
    (h : ∃! (e : F ≅ G), Scheme.Hom.IsOver e.hom S) :
    ∃! (e' : F' ≅ G), Scheme.Hom.IsOver e'.hom S := by
  obtain ⟨e, he, hu⟩ := h
  have hσinv : Scheme.Hom.IsOver σ.inv S := ⟨by
    rw [← hσ.1, ← Category.assoc, σ.inv_hom_id, Category.id_comp]⟩
  refine ⟨σ.trans e, ⟨?_⟩, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he.1, hσ.1]
  · intro e' he'
    have hcomp : Scheme.Hom.IsOver (σ.symm.trans e').hom S :=
      ⟨by rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he'.1, hσinv.1]⟩
    have h2 := hu (σ.symm.trans e') hcomp
    have h3 : σ.trans (σ.symm.trans e') = σ.trans e := by rw [h2]
    rwa [σ.self_symm_id_assoc] at h3

lemma Iso.inv_isOver_of_isOver {F G S : Scheme} [F.Over S] [G.Over S] (σ : F ≅ G)
    (hσ : Scheme.Hom.IsOver σ.hom S) : Scheme.Hom.IsOver σ.inv S :=
  ⟨by rw [← hσ.1, ← Category.assoc, σ.inv_hom_id, Category.id_comp]⟩

lemma existsUnique_iso_transport_target {F G G' S : Scheme} [F.Over S] [G.Over S] [G'.Over S]
    (τ : G ≅ G') (hτ : Scheme.Hom.IsOver τ.hom S)
    (h : ∃! (e : F ≅ G), Scheme.Hom.IsOver e.hom S) :
    ∃! (e' : F ≅ G'), Scheme.Hom.IsOver e'.hom S := by
  obtain ⟨e, he, hu⟩ := h
  have hτinv : Scheme.Hom.IsOver τ.inv S := ⟨by
    rw [← hτ.1, ← Category.assoc, τ.inv_hom_id, Category.id_comp]⟩
  refine ⟨e.trans τ, ⟨?_⟩, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hτ.1, he.1]
  · intro e' he'
    have hcomp : Scheme.Hom.IsOver (e'.trans τ.symm).hom S := ⟨by
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hτinv.1]; exact he'.1⟩
    have h2 := hu (e'.trans τ.symm) hcomp
    have h4 : e' = (e'.trans τ.symm).trans τ := by ext1; simp
    rw [h4, h2]

def Proj_loc_pair_mor (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  Proj_loc_pair X Z γ δ ⟶ open_pair X Z γ δ  :=
    pullback.fst (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))

instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z γ δ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _

instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z δ γ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _ ≫ (pullbackSymmetry _ _).hom

lemma loc_to_Clos_chart (X : Scheme) (Z : PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    loc_to_Clos (Z.cov.obj γ) (ideal_loc X Z γ) =
      pullback_Clos (Z.cov.map γ) (Quotient.mk' Z) :=
  Quotient.sound ⟨{ indnumb_equiv := Equiv.refl _
                    subscheme_iso := fun i => Z.condiso i γ
                    subscheme_iso_over := fun i => Z.condover i γ }⟩

lemma Proj_loc_pair_open_chart (X : Scheme) (Z : PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (C : CommRingCat) (k : Spec C ⟶ Spec (Z.cov.obj γ)) [IsOpenImmersion k] :
    ∃! (e : pullback (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)) k ≅
        BlMu (fun j => Ideal.map (Spec.preimage k).hom (ideal_loc X Z γ j))),
      Scheme.Hom.IsOver e.hom (Spec C) := by
  letI : Algebra (Z.cov.obj γ) C := RingHom.toAlgebra (Spec.preimage k).hom
  have hk : (Spec C ↘ Spec (Z.cov.obj γ)) = k := by
    show Spec.map (CommRingCat.ofHom (algebraMap (Z.cov.obj γ) C)) = k
    exact Spec.map_preimage k
  haveI : IsOpenImmersion (Spec C ↘ Spec (Z.cov.obj γ)) := hk ▸ ‹IsOpenImmersion k›
  have h := base_change_Bl_open (Z.cov.obj γ) C (ideal_loc X Z γ)
  rwa [hk] at h

lemma Proj_loc_pair_open_gamma (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (C : CommRingCat) (k : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion k] :
    ∃! (e : pullback k (Proj_loc_pair_mor X Z γ δ) ≅
        BlMu (fun j => Ideal.map
          (Spec.preimage (k ≫ pullback.fst (Z.cov.map γ) (Z.cov.map δ))).hom
          (ideal_loc X Z γ j))),
      Scheme.Hom.IsOver e.hom (Spec C) := by
  haveI : IsOpenImmersion (Z.cov.map δ) := Z.cov.map_prop δ
  haveI hFγ : IsOpenImmersion (pullback.fst (Z.cov.map γ) (Z.cov.map δ)) := inferInstance
  set F_γ := pullback.fst (Z.cov.map γ) (Z.cov.map δ) with hFγdef
  set G_γ := Proj_loc X Z γ ↘ Spec (Z.cov.obj γ) with hGγdef
  haveI : IsOpenImmersion (k ≫ F_γ) := inferInstance
  have h1 := Proj_loc_pair_open_chart X Z γ C (k ≫ F_γ)
  have hσ1 : Scheme.Hom.IsOver (pullbackSymmetry (k ≫ F_γ) G_γ).hom (Spec C) := by
    refine ⟨?_⟩
    show (pullbackSymmetry (k ≫ F_γ) G_γ).hom ≫ pullback.snd G_γ (k ≫ F_γ) =
      pullback.fst (k ≫ F_γ) G_γ
    exact pullbackSymmetry_hom_comp_snd (k ≫ F_γ) G_γ
  have h2 := existsUnique_iso_transport (S := Spec C)
    (pullbackSymmetry (k ≫ F_γ) G_γ) hσ1 h1
  have hσ2 : Scheme.Hom.IsOver (pullbackRightPullbackFstIso F_γ G_γ k).hom (Spec C) := by
    refine ⟨?_⟩
    show (pullbackRightPullbackFstIso F_γ G_γ k).hom ≫ pullback.fst (k ≫ F_γ) G_γ =
      pullback.fst k (pullback.fst F_γ G_γ)
    exact pullbackRightPullbackFstIso_hom_fst F_γ G_γ k
  exact existsUnique_iso_transport (S := Spec C)
    (pullbackRightPullbackFstIso F_γ G_γ k) hσ2 h2

lemma Proj_loc_pair_open_delta (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (C : CommRingCat) (k : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion k] :
    ∃! (e : pullback k (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom) ≅
        BlMu (fun j => Ideal.map
          (Spec.preimage (k ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
            pullback.fst (Z.cov.map δ) (Z.cov.map γ))).hom
          (ideal_loc X Z δ j))),
      Scheme.Hom.IsOver e.hom (Spec C) := by
  set e := pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)
  haveI : IsOpenImmersion (k ≫ e.inv) := inferInstance
  have h1 := Proj_loc_pair_open_gamma X Z δ γ C (k ≫ e.inv)
  have hσ : Scheme.Hom.IsOver (pullbackCompIso k (Proj_loc_pair_mor X Z δ γ) e).hom (Spec C) := by
    refine ⟨?_⟩
    show (pullbackCompIso k (Proj_loc_pair_mor X Z δ γ) e).hom ≫
        pullback.fst (k ≫ e.inv) (Proj_loc_pair_mor X Z δ γ) =
      pullback.fst k (Proj_loc_pair_mor X Z δ γ ≫ e.hom)
    show pullback.lift _ _ _ ≫ pullback.fst (k ≫ e.inv) (Proj_loc_pair_mor X Z δ γ) = _
    rw [pullback.lift_fst]
  exact existsUnique_iso_transport (S := Spec C) (pullbackCompIso k (Proj_loc_pair_mor X Z δ γ) e)
    hσ h1

lemma Proj_loc_pair_open_map_eq (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J) :
    pullback.fst (Z.cov.map γ) (Z.cov.map δ) ≫ Z.cov.map γ =
      (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
        pullback.fst (Z.cov.map δ) (Z.cov.map γ) ≫ Z.cov.map δ := by
  rw [show pullback.fst (Z.cov.map δ) (Z.cov.map γ) ≫ Z.cov.map δ = open_pair_map X Z δ γ from rfl,
    open_pair_map_equal X Z δ γ, ← Category.assoc, pullbackSymmetry_inv_comp_snd]

lemma Proj_loc_pair_open_centres_eq (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i] :
    loc_to_Clos C (fun j => Ideal.map
        (Spec.preimage (i ≫ pullback.fst (Z.cov.map γ) (Z.cov.map δ))).hom (ideal_loc X Z γ j)) =
      loc_to_Clos C (fun j => Ideal.map
        (Spec.preimage (i ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
          pullback.fst (Z.cov.map δ) (Z.cov.map γ))).hom (ideal_loc X Z δ j)) := by
  set k_γ := i ≫ pullback.fst (Z.cov.map γ) (Z.cov.map δ) with hkγ
  set k_δ := i ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
    pullback.fst (Z.cov.map δ) (Z.cov.map γ) with hkδ
  letI : Algebra (Z.cov.obj γ) C := RingHom.toAlgebra (Spec.preimage k_γ).hom
  letI : Algebra (Z.cov.obj δ) C := RingHom.toAlgebra (Spec.preimage k_δ).hom
  have halg_γ : (Spec.preimage k_γ).hom = algebraMap (Z.cov.obj γ) C := rfl
  have halg_δ : (Spec.preimage k_δ).hom = algebraMap (Z.cov.obj δ) C := rfl
  have hkγ' : (Spec C ↘ Spec (Z.cov.obj γ)) = k_γ := Spec.map_preimage k_γ
  have hkδ' : (Spec C ↘ Spec (Z.cov.obj δ)) = k_δ := Spec.map_preimage k_δ
  have hmap : k_γ ≫ Z.cov.map γ = k_δ ≫ Z.cov.map δ := by
    rw [hkγ, hkδ, Category.assoc]
    simp only [Category.assoc]
    rw [Proj_loc_pair_open_map_eq]
  rw [halg_γ, halg_δ, loc_to_Clos_baseChange (Z.cov.obj γ) C (ideal_loc X Z γ),
    loc_to_Clos_baseChange (Z.cov.obj δ) C (ideal_loc X Z δ), hkγ', hkδ',
    loc_to_Clos_chart X Z γ, loc_to_Clos_chart X Z δ, ← pullback_assoc, ← pullback_assoc,
    hmap]

lemma ProjBlowup_iso_of_centre_eq [Fintype ι] (C : CommRingCat) (L L' : ι → Ideal C)
    (h : loc_to_Clos C L = loc_to_Clos C L') :
    ∃! (e : BlMu L ≅ BlMu L'), Scheme.Hom.IsOver e.hom (Spec C) := by
  have condL : IsCars _ (pullback_Clos (BlMu L ↘ Spec C) (loc_to_Clos C L')) := by
    rw [← h]; exact blowups_Cars C L
  have condL' : IsCars _ (pullback_Clos (BlMu L' ↘ Spec C) (loc_to_Clos C L)) := by
    rw [h]; exact blowups_Cars C L'
  obtain ⟨φ, hφ, hφuniq⟩ := ProjBlowup_UnivProp_affine C L' condL
  obtain ⟨ψ, hψ, hψuniq⟩ := ProjBlowup_UnivProp_affine C L condL'
  refine ⟨⟨φ, ψ, ?_, ?_⟩, ⟨?_⟩, ?_⟩
  · exact ProjBlowup_UnivProp_unicity_affine C L (blowups_Cars C L) _ _
      ⟨by rw [Category.assoc, hψ.comp_over]; exact hφ.comp_over⟩ ⟨rfl⟩
  · exact ProjBlowup_UnivProp_unicity_affine C L' (blowups_Cars C L') _ _
      ⟨by rw [Category.assoc, hφ.comp_over]; exact hψ.comp_over⟩ ⟨rfl⟩
  · exact hφ.1
  · intro e' he'
    ext1
    exact hφuniq e'.hom he'

lemma Proj_loc_pair_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  ∃! (φ : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom)),
      Scheme.Hom.IsOver φ (Spec C) := by
  classical
  set T_γ := pullback i (Proj_loc_pair_mor X Z γ δ) with hTγ
  set T_δ := pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom) with hTδ
  obtain ⟨e_γ, he_γ, -⟩ := Proj_loc_pair_open_gamma X Z γ δ C i
  obtain ⟨e_δ, he_δ, -⟩ := Proj_loc_pair_open_delta X Z γ δ C i
  obtain ⟨e_c, he_c, -⟩ := ProjBlowup_iso_of_centre_eq C _ _
    (Proj_loc_pair_open_centres_eq X Z γ δ C i)

  have condTγ : IsCars _ (pullback_Clos (T_γ ↘ Spec C) (loc_to_Clos C
      (fun j => Ideal.map (Spec.preimage
        (i ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
          pullback.fst (Z.cov.map δ) (Z.cov.map γ))).hom (ideal_loc X Z δ j)))) := by
    rw [← Proj_loc_pair_open_centres_eq X Z γ δ C i]
    haveI : IsIso e_γ.hom := e_γ.isIso_hom
    have h := pullback_IsCars T_γ e_γ.hom _ (blowups_Cars C _)
    rwa [← pullback_assoc, he_γ.comp_over] at h
  have he_δinv : e_δ.inv ≫ (T_δ ↘ Spec C) =
      ((BlMu (fun j => Ideal.map (Spec.preimage
        (i ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
          pullback.fst (Z.cov.map δ) (Z.cov.map γ))).hom (ideal_loc X Z δ j))) ↘ Spec C) := by
    rw [Iso.inv_comp_eq]
    exact he_δ.1.symm
  refine ⟨e_γ.hom ≫ e_c.hom ≫ e_δ.inv, ⟨?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, he_δinv, he_c.comp_over, he_γ.comp_over]
  · intro φ' hφ'
    have huniq := ProjBlowup_UnivProp_unicity_affine C _ condTγ (φ' ≫ e_δ.hom) (e_γ.hom ≫ e_c.hom)
      ⟨by rw [Category.assoc, he_δ.comp_over]; exact hφ'.comp_over⟩
      ⟨by rw [Category.assoc, he_c.comp_over]; exact he_γ.comp_over⟩
    calc φ' = φ' ≫ e_δ.hom ≫ e_δ.inv := by rw [Iso.hom_inv_id, Category.comp_id]
      _ = (e_γ.hom ≫ e_c.hom) ≫ e_δ.inv := by rw [← Category.assoc, huniq]
      _ = e_γ.hom ≫ e_c.hom ≫ e_δ.inv := by rw [Category.assoc]

def Proj_loc_pair_open_φ (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom) :=
  Classical.choose (Proj_loc_pair_open X Z γ δ C i)

lemma Proj_loc_pair_open_φ_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_open_φ X Z γ δ C i) (Spec C) :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.1

lemma Proj_loc_pair_open_φ_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    ∀ φ' : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom),
      Scheme.Hom.IsOver φ' (Spec C) → φ' = Proj_loc_pair_open_φ X Z γ δ C i :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.2

lemma Proj_loc_pair_open_φ_isIso (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    IsIso (Proj_loc_pair_open_φ X Z γ δ C i) := by
  classical
  obtain ⟨e_γ, he_γ, -⟩ := Proj_loc_pair_open_gamma X Z γ δ C i
  obtain ⟨e_δ, he_δ, -⟩ := Proj_loc_pair_open_delta X Z γ δ C i
  obtain ⟨e_c, he_c, -⟩ := ProjBlowup_iso_of_centre_eq C _ _
    (Proj_loc_pair_open_centres_eq X Z γ δ C i)
  have he_δinv : e_δ.inv ≫ (pullback i (Proj_loc_pair_mor X Z δ γ ≫
      (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) ↘ Spec C) =
      ((BlMu (fun j => Ideal.map (Spec.preimage
        (i ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫
          pullback.fst (Z.cov.map δ) (Z.cov.map γ))).hom (ideal_loc X Z δ j))) ↘ Spec C) := by
    rw [Iso.inv_comp_eq]
    exact he_δ.1.symm
  have hisOver : Scheme.Hom.IsOver (e_γ.hom ≫ e_c.hom ≫ e_δ.inv) (Spec C) :=
    ⟨by rw [Category.assoc, Category.assoc, he_δinv, he_c.comp_over, he_γ.comp_over]⟩
  rw [← Proj_loc_pair_open_φ_uniq X Z γ δ C i (e_γ.hom ≫ e_c.hom ≫ e_δ.inv) hisOver]
  infer_instance

noncomputable def transportIso {X S : Scheme} (f : X ⟶ S) {T C : Scheme} (i : C ⟶ S) (j : T ⟶ C) :
    pullback (pullback.fst i f) j ≅ pullback (j ≫ i) f :=
  (pullbackSymmetry (pullback.fst i f) j) ≪≫ (pullbackRightPullbackFstIso i f j)

@[reassoc]
lemma transportIso_hom_fst {X S : Scheme} (f : X ⟶ S) {T C : Scheme} (i : C ⟶ S) (j : T ⟶ C) :
    (transportIso f i j).hom ≫ pullback.fst (j ≫ i) f = pullback.snd (pullback.fst i f) j := by
  show ((pullbackSymmetry (pullback.fst i f) j).hom ≫ (pullbackRightPullbackFstIso i f j).hom) ≫
    pullback.fst (j ≫ i) f = _
  rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst]

@[reassoc]
lemma transportIso_hom_snd {X S : Scheme} (f : X ⟶ S) {T C : Scheme} (i : C ⟶ S) (j : T ⟶ C) :
    (transportIso f i j).hom ≫ pullback.snd (j ≫ i) f =
      pullback.fst (pullback.fst i f) j ≫ pullback.snd i f := by
  show ((pullbackSymmetry (pullback.fst i f) j).hom ≫ (pullbackRightPullbackFstIso i f j).hom) ≫
    pullback.snd (j ≫ i) f = _
  rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc,
    pullbackSymmetry_hom_comp_snd]

noncomputable def restrictRaw {A B S U : Scheme} (fA : A ⟶ S) (fB : B ⟶ S) (φ : A ⟶ B)
    (hφ : φ ≫ fB = fA) (j : U ⟶ S) :
    pullback fA j ⟶ pullback fB j :=
  pullback.map fA j fB j φ (𝟙 _) (𝟙 _) (by simpa using hφ.symm) (by simp)

@[reassoc]
lemma restrictRaw_snd {A B S U : Scheme} (fA : A ⟶ S) (fB : B ⟶ S) (φ : A ⟶ B)
    (hφ : φ ≫ fB = fA) (j : U ⟶ S) :
    restrictRaw fA fB φ hφ j ≫ pullback.snd fB j = pullback.snd fA j := by
  show pullback.lift _ _ _ ≫ pullback.snd fB j = _
  rw [pullback.lift_snd, Category.comp_id]

@[reassoc]
lemma restrictRaw_fst {A B S U : Scheme} (fA : A ⟶ S) (fB : B ⟶ S) (φ : A ⟶ B)
    (hφ : φ ≫ fB = fA) (j : U ⟶ S) :
    restrictRaw fA fB φ hφ j ≫ pullback.fst fB j = pullback.fst fA j ≫ φ := by
  show pullback.lift _ _ _ ≫ pullback.fst fB j = _
  rw [pullback.lift_fst]

@[reassoc]
lemma pullbackDoubleFstIso_inv_fst {A B D S : Scheme} (f : A ⟶ S) (g : B ⟶ S) (h : D ⟶ S) :
    (pullbackDoubleFstIso f g h).inv ≫ pullback.fst (pullback.fst f g) (pullback.fst f h) =
      pullback.lift (pullback.fst f (pullback.fst g h ≫ g))
        (pullback.snd f (pullback.fst g h ≫ g) ≫ pullback.fst g h)
        (by rw [Category.assoc]; exact pullback.condition) := by
  show pullback.lift _ _ _ ≫ pullback.fst (pullback.fst f g) (pullback.fst f h) = _
  rw [pullback.lift_fst]

@[reassoc]
lemma pullbackDoubleFstIso_inv_snd {A B D S : Scheme} (f : A ⟶ S) (g : B ⟶ S) (h : D ⟶ S) :
    (pullbackDoubleFstIso f g h).inv ≫ pullback.snd (pullback.fst f g) (pullback.fst f h) =
      pullback.lift (pullback.fst f (pullback.fst g h ≫ g))
        (pullback.snd f (pullback.fst g h ≫ g) ≫ pullback.snd g h)
        (by
          rw [Category.assoc,
            show pullback.snd g h ≫ h = pullback.fst g h ≫ g from
              (pullback.condition (f := g) (g := h)).symm]
          exact pullback.condition) := by
  show pullback.lift _ _ _ ≫ pullback.snd (pullback.fst f g) (pullback.fst f h) = _
  rw [pullback.lift_snd]

@[reassoc]
lemma pullbackSndCompIso_hom_fst {X Y Z W : Scheme} (f : X ⟶ Z) (a : Y ⟶ Z) (b : W ⟶ Y) :
    (pullbackSndCompIso f a b).hom ≫ pullback.fst (pullback.snd f a) b =
      pullback.lift (pullback.fst f (b ≫ a)) (pullback.snd f (b ≫ a) ≫ b)
        (by rw [Category.assoc]; exact pullback.condition) := by
  show pullback.lift _ _ _ ≫ pullback.fst (pullback.snd f a) b = _
  rw [pullback.lift_fst]

@[reassoc]
lemma pullbackSndCompIso_hom_snd {X Y Z W : Scheme} (f : X ⟶ Z) (a : Y ⟶ Z) (b : W ⟶ Y) :
    (pullbackSndCompIso f a b).hom ≫ pullback.snd (pullback.snd f a) b = pullback.snd f (b ≫ a) := by
  show pullback.lift _ _ _ ≫ pullback.snd (pullback.snd f a) b = _
  rw [pullback.lift_snd]

lemma Proj_loc_pair_open_φ_restrict (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  (C' : CommRingCat) (j : Spec C' ⟶ Spec C) [IsOpenImmersion j] :
    (transportIso (Proj_loc_pair_mor X Z γ δ) i j).inv ≫
      restrictRaw (pullback.fst i (Proj_loc_pair_mor X Z γ δ))
        (pullback.fst i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom))
        (Proj_loc_pair_open_φ X Z γ δ C i)
        (Proj_loc_pair_open_φ_isOver X Z γ δ C i).1 j ≫
      (transportIso (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) i j).hom =
      Proj_loc_pair_open_φ X Z γ δ C' (j ≫ i) := by
  apply Proj_loc_pair_open_φ_uniq
  refine ⟨?_⟩
  show ((transportIso (Proj_loc_pair_mor X Z γ δ) i j).inv ≫
      restrictRaw (pullback.fst i (Proj_loc_pair_mor X Z γ δ))
        (pullback.fst i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom))
        (Proj_loc_pair_open_φ X Z γ δ C i)
        (Proj_loc_pair_open_φ_isOver X Z γ δ C i).1 j) ≫
      (transportIso (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) i j).hom ≫
      pullback.fst (j ≫ i) (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) =
      pullback.fst (j ≫ i) (Proj_loc_pair_mor X Z γ δ)
  simp only [Category.assoc]
  rw [transportIso_hom_fst, restrictRaw_snd]
  have hfinal : (transportIso (Proj_loc_pair_mor X Z γ δ) i j).inv ≫
      pullback.snd (pullback.fst i (Proj_loc_pair_mor X Z γ δ)) j =
      pullback.fst (j ≫ i) (Proj_loc_pair_mor X Z γ δ) := by
    rw [Iso.inv_comp_eq]
    exact (transportIso_hom_fst (Proj_loc_pair_mor X Z γ δ) i j).symm
  exact hfinal

def Proj_loc_pair_lemm (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  ∃! (f : (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ)),

  (∃ (pf : Scheme.Hom.IsOver f (open_pair X Z γ δ)),
    ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
      restrictToOpen f i =
      (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
      (pullbackSymmetry _ _).hom) := by
  classical
  set S := open_pair X Z γ δ with hS
  set 𝒰 := S.affineCover with h𝒰
  set fmor := Proj_loc_pair_mor X Z γ δ with hfmor
  set 𝒱 := 𝒰.pullbackCover fmor with h𝒱

  let g : ∀ x : 𝒰.J, 𝒱.obj x ⟶ Proj_loc_pair X Z δ γ := fun x =>
    (pullbackSymmetry fmor (𝒰.map x)).hom ≫
      Proj_loc_pair_open_φ X Z γ δ ((S.local_affine x).choose_spec.choose) (𝒰.map x) ≫
      pullback.snd (𝒰.map x) (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom)
  have hg : ∀ x y, pullback.fst (𝒱.map x) (𝒱.map y) ≫ g x =
      pullback.snd (𝒱.map x) (𝒱.map y) ≫ g y := by
    intro x y
    set W := pullback (𝒰.map x) (𝒰.map y) with hW
    set ℓ := pullback.fst (𝒰.map x) (𝒰.map y) ≫ 𝒰.map x with hℓ
    set e := pullbackDoubleFstIso fmor (𝒰.map x) (𝒰.map y) with he
    set 𝒲 := W.affineCover with h𝒲
    set 𝒬 := 𝒲.pullbackCover (pullback.snd fmor ℓ) with h𝒬
    rw [show pullback.fst (𝒱.map x) (𝒱.map y) ≫ g x =
          e.hom ≫ e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y) ≫ g x by
        rw [Iso.hom_inv_id_assoc],
      show pullback.snd (𝒱.map x) (𝒱.map y) ≫ g y =
          e.hom ≫ e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y) ≫ g y by
        rw [Iso.hom_inv_id_assoc]]
    congr 1
    refine 𝒬.hom_ext _ _ (fun w => ?_)
    set b := 𝒲.map w with hb
    set qw := pullback.snd (pullback.snd fmor ℓ) b with hqw
    have hqcond : 𝒬.map w ≫ pullback.snd fmor ℓ = qw ≫ b :=
      pullback.condition (f := pullback.snd fmor ℓ) (g := b)
    set jx := b ≫ pullback.fst (𝒰.map x) (𝒰.map y) with hjx
    set jy := b ≫ pullback.snd (𝒰.map x) (𝒰.map y) with hjy
    set ρx : pullback fmor ℓ ⟶ pullback fmor (𝒰.map x) :=
      pullback.lift (pullback.fst fmor ℓ)
        (pullback.snd fmor ℓ ≫ pullback.fst (𝒰.map x) (𝒰.map y))
        (by rw [Category.assoc]; exact pullback.condition) with hρxdef
    have hρxfst : ρx ≫ pullback.fst fmor (𝒰.map x) = pullback.fst fmor ℓ := by
      rw [hρxdef, pullback.lift_fst]
    have hρxsnd : ρx ≫ pullback.snd fmor (𝒰.map x) =
        pullback.snd fmor ℓ ≫ pullback.fst (𝒰.map x) (𝒰.map y) := by
      rw [hρxdef, pullback.lift_snd]
    have hρx : e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y) = ρx :=
      pullbackDoubleFstIso_inv_fst fmor (𝒰.map x) (𝒰.map y)
    set kw := b ≫ ℓ with hkw
    have hjxk : jx ≫ 𝒰.map x = kw := by rw [hjx, hkw, hℓ, Category.assoc]
    haveI : IsOpenImmersion jx := by rw [hjx]; infer_instance
    haveI : IsOpenImmersion kw := by rw [hkw, hℓ]; infer_instance
    haveI : IsOpenImmersion (jx ≫ 𝒰.map x) := hjxk ▸ ‹IsOpenImmersion kw›
    have hψxproof : qw ≫ kw = (𝒬.map w ≫ pullback.fst fmor ℓ) ≫ fmor := by
      rw [hkw, ← Category.assoc, ← hqcond, Category.assoc, Category.assoc,
        show pullback.fst fmor ℓ ≫ fmor = pullback.snd fmor ℓ ≫ ℓ from
          pullback.condition (f := fmor) (g := ℓ), ← Category.assoc]
    set ψ : 𝒬.obj w ⟶ pullback kw fmor :=
      pullback.lift qw (𝒬.map w ≫ pullback.fst fmor ℓ) hψxproof with hψdef
    set ρy : pullback fmor ℓ ⟶ pullback fmor (𝒰.map y) :=
      pullback.lift (pullback.fst fmor ℓ)
        (pullback.snd fmor ℓ ≫ pullback.snd (𝒰.map x) (𝒰.map y))
        (by
          rw [Category.assoc,
            show pullback.snd (𝒰.map x) (𝒰.map y) ≫ 𝒰.map y =
              pullback.fst (𝒰.map x) (𝒰.map y) ≫ 𝒰.map x from
              (pullback.condition (f := 𝒰.map x) (g := 𝒰.map y)).symm]
          exact pullback.condition) with hρydef
    have hρyfst : ρy ≫ pullback.fst fmor (𝒰.map y) = pullback.fst fmor ℓ := by
      rw [hρydef, pullback.lift_fst]
    have hρysnd : ρy ≫ pullback.snd fmor (𝒰.map y) =
        pullback.snd fmor ℓ ≫ pullback.snd (𝒰.map x) (𝒰.map y) := by
      rw [hρydef, pullback.lift_snd]
    have hρy : e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y) = ρy :=
      pullbackDoubleFstIso_inv_snd fmor (𝒰.map x) (𝒰.map y)
    have hjyk : jy ≫ 𝒰.map y = kw := by
      rw [hjy, hkw, hℓ, Category.assoc,
        pullback.condition (f := 𝒰.map x) (g := 𝒰.map y)]
    haveI : IsOpenImmersion jy := by rw [hjy]; infer_instance
    haveI : IsOpenImmersion (jy ≫ 𝒰.map y) := hjyk ▸ ‹IsOpenImmersion kw›
    set Cx := (S.local_affine x).choose_spec.choose with hCx
    set Cw := (W.local_affine w).choose_spec.choose with hCw'
    set σx : 𝒬.obj w ⟶ pullback (𝒰.map x) fmor :=
      𝒬.map w ≫ ρx ≫ (pullbackSymmetry fmor (𝒰.map x)).hom with hσx
    have hσxfst : σx ≫ pullback.fst (𝒰.map x) fmor = qw ≫ jx := by
      have step1 : σx ≫ pullback.fst (𝒰.map x) fmor =
          𝒬.map w ≫ (ρx ≫ pullback.snd fmor (𝒰.map x)) := by
        rw [hσx, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
      rw [step1, hρxsnd, ← Category.assoc, hqcond, Category.assoc, hjx]
    have hσxsnd : σx ≫ pullback.snd (𝒰.map x) fmor = 𝒬.map w ≫ pullback.fst fmor ℓ := by
      have step1' : σx ≫ pullback.snd (𝒰.map x) fmor =
          𝒬.map w ≫ (ρx ≫ pullback.fst fmor (𝒰.map x)) := by
        rw [hσx, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
      rw [step1', hρxfst]
    set μx : 𝒬.obj w ⟶ pullback (pullback.fst (𝒰.map x) fmor) jx :=
      pullback.lift σx qw hσxfst with hμx
    set castx : pullback (jx ≫ 𝒰.map x) fmor ≅ pullback kw fmor :=
      pullback.congrHom hjxk rfl with hcastx
    have hcastx_fst : castx.hom ≫ pullback.fst kw fmor = pullback.fst (jx ≫ 𝒰.map x) fmor := by
      rw [hcastx]; simp
    have hcastx_snd : castx.hom ≫ pullback.snd kw fmor = pullback.snd (jx ≫ 𝒰.map x) fmor := by
      rw [hcastx]; simp
    have hψeq_x : ψ = μx ≫ (transportIso fmor (𝒰.map x) jx).hom ≫ castx.hom := by
      apply pullback.hom_ext
      · rw [hψdef, Category.assoc, Category.assoc, hcastx_fst, transportIso_hom_fst,
          pullback.lift_fst, hμx, pullback.lift_snd]
      · rw [hψdef, Category.assoc, Category.assoc, hcastx_snd, transportIso_hom_snd,
          pullback.lift_snd, hμx, ← Category.assoc, pullback.lift_fst, hσxsnd]
    set σy : 𝒬.obj w ⟶ pullback (𝒰.map y) fmor :=
      𝒬.map w ≫ ρy ≫ (pullbackSymmetry fmor (𝒰.map y)).hom with hσy
    have hσyfst : σy ≫ pullback.fst (𝒰.map y) fmor = qw ≫ jy := by
      have step1 : σy ≫ pullback.fst (𝒰.map y) fmor =
          𝒬.map w ≫ (ρy ≫ pullback.snd fmor (𝒰.map y)) := by
        rw [hσy, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
      rw [step1, hρysnd, ← Category.assoc, hqcond, Category.assoc, hjy]
    have hσysnd : σy ≫ pullback.snd (𝒰.map y) fmor = 𝒬.map w ≫ pullback.fst fmor ℓ := by
      have step1' : σy ≫ pullback.snd (𝒰.map y) fmor =
          𝒬.map w ≫ (ρy ≫ pullback.fst fmor (𝒰.map y)) := by
        rw [hσy, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
      rw [step1', hρyfst]
    set μy : 𝒬.obj w ⟶ pullback (pullback.fst (𝒰.map y) fmor) jy :=
      pullback.lift σy qw hσyfst with hμy
    set casty : pullback (jy ≫ 𝒰.map y) fmor ≅ pullback kw fmor :=
      pullback.congrHom hjyk rfl with hcasty
    have hcasty_fst : casty.hom ≫ pullback.fst kw fmor = pullback.fst (jy ≫ 𝒰.map y) fmor := by
      rw [hcasty]; simp
    have hcasty_snd : casty.hom ≫ pullback.snd kw fmor = pullback.snd (jy ≫ 𝒰.map y) fmor := by
      rw [hcasty]; simp
    have hψeq_y : ψ = μy ≫ (transportIso fmor (𝒰.map y) jy).hom ≫ casty.hom := by
      apply pullback.hom_ext
      · rw [hψdef, Category.assoc, Category.assoc, hcasty_fst, transportIso_hom_fst,
          pullback.lift_fst, hμy, pullback.lift_snd]
      · rw [hψdef, Category.assoc, Category.assoc, hcasty_snd, transportIso_hom_snd,
          pullback.lift_snd, hμy, ← Category.assoc, pullback.lift_fst, hσysnd]
    set Cy := (S.local_affine y).choose_spec.choose with hCy
    set gmor := Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom with
      hgmor
    have hrestrict_x : (transportIso fmor (𝒰.map x) jx).inv ≫
        restrictRaw (pullback.fst (𝒰.map x) fmor) (pullback.fst (𝒰.map x) gmor)
          (Proj_loc_pair_open_φ X Z γ δ Cx (𝒰.map x))
          (Proj_loc_pair_open_φ_isOver X Z γ δ Cx (𝒰.map x)).1 jx ≫
        (transportIso gmor (𝒰.map x) jx).hom = Proj_loc_pair_open_φ X Z γ δ Cw (jx ≫ 𝒰.map x) :=
      Proj_loc_pair_open_φ_restrict X Z γ δ Cx (𝒰.map x) Cw jx
    have hrestrict_y : (transportIso fmor (𝒰.map y) jy).inv ≫
        restrictRaw (pullback.fst (𝒰.map y) fmor) (pullback.fst (𝒰.map y) gmor)
          (Proj_loc_pair_open_φ X Z γ δ Cy (𝒰.map y))
          (Proj_loc_pair_open_φ_isOver X Z γ δ Cy (𝒰.map y)).1 jy ≫
        (transportIso gmor (𝒰.map y) jy).hom = Proj_loc_pair_open_φ X Z γ δ Cw (jy ≫ 𝒰.map y) :=
      Proj_loc_pair_open_φ_restrict X Z γ δ Cy (𝒰.map y) Cw jy
    set castx_g : pullback (jx ≫ 𝒰.map x) gmor ≅ pullback kw gmor :=
      pullback.congrHom hjxk rfl with hcastx_g
    set casty_g : pullback (jy ≫ 𝒰.map y) gmor ≅ pullback kw gmor :=
      pullback.congrHom hjyk rfl with hcasty_g
    have hcastx_g_snd : castx_g.hom ≫ pullback.snd kw gmor = pullback.snd (jx ≫ 𝒰.map x) gmor := by
      rw [hcastx_g]; simp
    have hcasty_g_snd : casty_g.hom ≫ pullback.snd kw gmor = pullback.snd (jy ≫ 𝒰.map y) gmor := by
      rw [hcasty_g]; simp
    set Φkw : pullback kw fmor ⟶ pullback kw gmor := castx.inv ≫
        Proj_loc_pair_open_φ X Z γ δ Cw (jx ≫ 𝒰.map x) ≫ castx_g.hom with hΦkw
    have keyx : castx.inv ≫ Proj_loc_pair_open_φ X Z γ δ Cw (jx ≫ 𝒰.map x) ≫ castx_g.hom =
        Proj_loc_pair_open_φ X Z γ δ Cw kw := by
      clear_value kw
      subst hjxk
      simp only [hcastx, hcastx_g, pullback.congrHom_hom, pullback.congrHom_inv,
        pullback.map_id, Category.id_comp]
      exact Category.comp_id _
    have keyy : casty.inv ≫ Proj_loc_pair_open_φ X Z γ δ Cw (jy ≫ 𝒰.map y) ≫ casty_g.hom =
        Proj_loc_pair_open_φ X Z γ δ Cw kw := by
      clear_value kw
      subst hjyk
      simp only [hcasty, hcasty_g, pullback.congrHom_hom, pullback.congrHom_inv,
        pullback.map_id, Category.id_comp]
      exact Category.comp_id _
    have hΦkw_eq_y : Φkw = casty.inv ≫ Proj_loc_pair_open_φ X Z γ δ Cw (jy ≫ 𝒰.map y) ≫
        casty_g.hom := by
      rw [hΦkw, keyx, keyy]
    have hfinal_x : 𝒬.map w ≫ ρx ≫ g x = ψ ≫ Φkw ≫ pullback.snd kw gmor := by
      have hstep0 : 𝒬.map w ≫ ρx ≫ g x =
          σx ≫ Proj_loc_pair_open_φ X Z γ δ Cx (𝒰.map x) ≫ pullback.snd (𝒰.map x) gmor := by
        show 𝒬.map w ≫ ρx ≫ ((pullbackSymmetry fmor (𝒰.map x)).hom ≫
          Proj_loc_pair_open_φ X Z γ δ Cx (𝒰.map x) ≫ pullback.snd (𝒰.map x) gmor) = _
        rw [hσx]; simp only [Category.assoc]
      rw [hstep0, hΦkw]
      have hψcastx : ψ ≫ castx.inv = μx ≫ (transportIso fmor (𝒰.map x) jx).hom := by
        conv_lhs => rw [hψeq_x]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hcombine : ψ ≫ (castx.inv ≫ Proj_loc_pair_open_φ X Z γ δ Cw (jx ≫ 𝒰.map x) ≫
            castx_g.hom) ≫ pullback.snd kw gmor =
          μx ≫ (transportIso fmor (𝒰.map x) jx).hom ≫
            Proj_loc_pair_open_φ X Z γ δ Cw (jx ≫ 𝒰.map x) ≫ pullback.snd (jx ≫ 𝒰.map x) gmor := by
        simp only [← Category.assoc]
        rw [show ψ ≫ castx.inv = μx ≫ (transportIso fmor (𝒰.map x) jx).hom from hψcastx]
        simp only [Category.assoc, hcastx_g_snd]
      rw [hcombine, ← hrestrict_x]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, transportIso_hom_snd,
        restrictRaw_fst_assoc, hμx, pullback.lift_fst_assoc]
    have hfinal_y : 𝒬.map w ≫ ρy ≫ g y = ψ ≫ Φkw ≫ pullback.snd kw gmor := by
      have hstep0 : 𝒬.map w ≫ ρy ≫ g y =
          σy ≫ Proj_loc_pair_open_φ X Z γ δ Cy (𝒰.map y) ≫ pullback.snd (𝒰.map y) gmor := by
        show 𝒬.map w ≫ ρy ≫ ((pullbackSymmetry fmor (𝒰.map y)).hom ≫
          Proj_loc_pair_open_φ X Z γ δ Cy (𝒰.map y) ≫ pullback.snd (𝒰.map y) gmor) = _
        rw [hσy]; simp only [Category.assoc]
      rw [hstep0, hΦkw_eq_y]
      have hψcasty : ψ ≫ casty.inv = μy ≫ (transportIso fmor (𝒰.map y) jy).hom := by
        conv_lhs => rw [hψeq_y]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hcombine : ψ ≫ (casty.inv ≫ Proj_loc_pair_open_φ X Z γ δ Cw (jy ≫ 𝒰.map y) ≫
            casty_g.hom) ≫ pullback.snd kw gmor =
          μy ≫ (transportIso fmor (𝒰.map y) jy).hom ≫
            Proj_loc_pair_open_φ X Z γ δ Cw (jy ≫ 𝒰.map y) ≫ pullback.snd (jy ≫ 𝒰.map y) gmor := by
        simp only [← Category.assoc]
        rw [show ψ ≫ casty.inv = μy ≫ (transportIso fmor (𝒰.map y) jy).hom from hψcasty]
        simp only [Category.assoc, hcasty_g_snd]
      rw [hcombine, ← hrestrict_y]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, transportIso_hom_snd,
        restrictRaw_fst_assoc, hμy, pullback.lift_fst_assoc]
    conv_lhs => rw [show 𝒬.map w ≫ e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y) ≫ g x =
        𝒬.map w ≫ (e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y)) ≫ g x from by
      simp only [Category.assoc]]
    conv_rhs => rw [show 𝒬.map w ≫ e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y) ≫ g y =
        𝒬.map w ≫ (e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y)) ≫ g y from by
      simp only [Category.assoc]]
    rw [hρx, hρy, hfinal_x, hfinal_y]
  set gmor := Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom with
    hgmor
  have hisOver : Scheme.Hom.IsOver (𝒱.glueMorphisms g hg) S := by
    rw [Scheme.Hom.isOver_iff]
    refine 𝒱.hom_ext _ _ (fun x => ?_)
    show 𝒱.map x ≫ 𝒱.glueMorphisms g hg ≫ gmor = 𝒱.map x ≫ fmor
    rw [← Category.assoc, 𝒱.ι_glueMorphisms, Category.assoc]
    show (pullbackSymmetry fmor (𝒰.map x)).hom ≫
        Proj_loc_pair_open_φ X Z γ δ ((S.local_affine x).choose_spec.choose) (𝒰.map x) ≫
        (pullback.snd (𝒰.map x) gmor ≫ gmor) = 𝒱.map x ≫ fmor
    have hcond : pullback.snd (𝒰.map x) gmor ≫ gmor =
        pullback.fst (𝒰.map x) gmor ≫ 𝒰.map x :=
      (pullback.condition (f := 𝒰.map x) (g := gmor)).symm
    rw [hcond, ← Category.assoc, Category.assoc (pullbackSymmetry fmor (𝒰.map x)).hom]
    have hφ1 : Proj_loc_pair_open_φ X Z γ δ ((S.local_affine x).choose_spec.choose) (𝒰.map x) ≫
        pullback.fst (𝒰.map x) gmor =
        pullback.fst (𝒰.map x) fmor :=
      (Proj_loc_pair_open_φ_isOver X Z γ δ ((S.local_affine x).choose_spec.choose)
        (𝒰.map x)).1
    rw [show Proj_loc_pair_open_φ X Z γ δ ((S.local_affine x).choose_spec.choose) (𝒰.map x) ≫
        pullback.fst (𝒰.map x) gmor ≫
        𝒰.map x = pullback.fst (𝒰.map x) fmor ≫ 𝒰.map x by rw [← Category.assoc, hφ1],
      ← Category.assoc, pullbackSymmetry_hom_comp_fst]
    show pullback.snd fmor (𝒰.map x) ≫ 𝒰.map x = 𝒱.map x ≫ fmor
    exact (pullback.condition (f := fmor) (g := 𝒰.map x)).symm
  haveI := hisOver
  refine ⟨𝒱.glueMorphisms g hg, ⟨hisOver, ?_⟩, ?_⟩
  ·
    intro C i _
    have hrto : restrictToOpen (𝒱.glueMorphisms g hg) i ≫ pullback.snd gmor i =
        pullback.snd fmor i := by
      delta restrictToOpen
      change _ ≫ pullback.snd _ _ = pullback.snd _ _
      simp
    have hkey : (pullbackSymmetry fmor i).inv ≫ restrictToOpen (𝒱.glueMorphisms g hg) i ≫
        (pullbackSymmetry i gmor).inv = Proj_loc_pair_open_φ X Z γ δ C i := by
      apply Proj_loc_pair_open_φ_uniq
      rw [Scheme.Hom.isOver_iff]
      show ((pullbackSymmetry fmor i).inv ≫ restrictToOpen (𝒱.glueMorphisms g hg) i ≫
        (pullbackSymmetry i gmor).inv) ≫ pullback.fst i gmor = pullback.fst i fmor
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst, hrto,
        pullbackSymmetry_inv_comp_snd]
    rw [show restrictToOpen (𝒱.glueMorphisms g hg) i = (pullbackSymmetry fmor i).hom ≫
        ((pullbackSymmetry fmor i).inv ≫ restrictToOpen (𝒱.glueMorphisms g hg) i ≫
          (pullbackSymmetry i gmor).inv) ≫ (pullbackSymmetry i gmor).hom by simp, hkey]
  ·
    rintro f' ⟨pf', hrestrict'⟩
    haveI := pf'
    refine 𝒱.hom_ext _ _ (fun x => ?_)
    show 𝒱.map x ≫ f' = 𝒱.map x ≫ 𝒱.glueMorphisms g hg
    rw [𝒱.ι_glueMorphisms]
    have hcomp : restrictToOpen f' (𝒰.map x) ≫ pullback.fst gmor (𝒰.map x) =
        pullback.fst fmor (𝒰.map x) ≫ f' := by
      delta restrictToOpen
      change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      rw [pullback.lift_fst]
      rfl
    show pullback.fst fmor (𝒰.map x) ≫ f' = g x
    rw [← hcomp]
    have heq : restrictToOpen f' (𝒰.map x) = (pullbackSymmetry fmor (𝒰.map x)).hom ≫
        Proj_loc_pair_open_φ X Z γ δ ((S.local_affine x).choose_spec.choose) (𝒰.map x) ≫
        (pullbackSymmetry (𝒰.map x) gmor).hom :=
      hrestrict' ((S.local_affine x).choose_spec.choose) (𝒰.map x)
    rw [heq]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
    rfl

def Proj_loc_pair_swap (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ) :=
  Classical.choose (Proj_loc_pair_lemm X Z γ δ)

instance Proj_loc_pair_swap_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_swap X Z γ δ) (open_pair X Z γ δ) :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.1

lemma Proj_loc_pair_swap_restrict (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i] :
    restrictToOpen (Proj_loc_pair_swap X Z γ δ) i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.2 C i

lemma Proj_loc_pair_swap_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (f : Proj_loc_pair X Z γ δ ⟶ Proj_loc_pair X Z δ γ)
  (is_over : Scheme.Hom.IsOver f (open_pair X Z γ δ))
  (affine : ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
    restrictToOpen f i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom) :
    f = Proj_loc_pair_swap X Z γ δ :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.2 f ⟨is_over, affine⟩

lemma Proj_loc_pair_iso (X:Scheme)  (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  IsIso (Proj_loc_pair_swap X Z γ δ) := by

  classical
  set S := open_pair X Z γ δ with hS
  set f := Proj_loc_pair_swap X Z γ δ with hfdef
  set fmor := (Proj_loc_pair X Z γ δ) ↘ S with hfmor
  set gmor := (Proj_loc_pair X Z δ γ) ↘ S with hgmor
  set 𝒰 := S.affineCover with h𝒰
  set 𝒱' := 𝒰.pullbackCover gmor with h𝒱'
  apply IsLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) 𝒱'
  intro x
  show IsIso (pullback.snd f (𝒱'.map x))
  set i := 𝒰.map x with hi
  set e := pullbackRightPullbackFstIso gmor i f with he
  have hfIsOver : f ≫ gmor = fmor := (Proj_loc_pair_swap_isOver X Z γ δ).1
  set castfg : pullback fmor i ≅ pullback (f ≫ gmor) i :=
    pullback.congrHom hfIsOver.symm rfl with hcastfg
  have hcastfg_fst : castfg.inv ≫ pullback.fst fmor i = pullback.fst (f ≫ gmor) i := by
    rw [hcastfg]; simp
  have hcastfg_snd : castfg.inv ≫ pullback.snd fmor i = pullback.snd (f ≫ gmor) i := by
    rw [hcastfg]; simp
  have hrfst : restrictToOpen f i ≫ pullback.fst gmor i = pullback.fst fmor i ≫ f :=
    restrictToOpen_fst f i
  have hrsnd : restrictToOpen f i ≫ pullback.snd gmor i = pullback.snd fmor i :=
    restrictToOpen_snd f i
  have key : e.inv ≫ pullback.snd f (𝒱'.map x) = castfg.inv ≫ restrictToOpen f i := by
    show e.inv ≫ pullback.snd f (pullback.fst gmor i) = castfg.inv ≫ restrictToOpen f i
    apply pullback.hom_ext
    · have hpc : pullback.fst f (pullback.fst gmor i) ≫ f =
          pullback.snd f (pullback.fst gmor i) ≫ pullback.fst gmor i :=
        pullback.condition (f := f) (g := pullback.fst gmor i)
      calc e.inv ≫ pullback.snd f (pullback.fst gmor i) ≫ pullback.fst gmor i
          = e.inv ≫ pullback.fst f (pullback.fst gmor i) ≫ f := by rw [← hpc]
        _ = (e.inv ≫ pullback.fst f (pullback.fst gmor i)) ≫ f := by rw [Category.assoc]
        _ = pullback.fst (f ≫ gmor) i ≫ f := by rw [pullbackRightPullbackFstIso_inv_fst]
        _ = (castfg.inv ≫ pullback.fst fmor i) ≫ f := by rw [hcastfg_fst]
        _ = castfg.inv ≫ (pullback.fst fmor i ≫ f) := by rw [Category.assoc]
        _ = castfg.inv ≫ (restrictToOpen f i ≫ pullback.fst gmor i) := by rw [← hrfst]
        _ = (castfg.inv ≫ restrictToOpen f i) ≫ pullback.fst gmor i := by rw [Category.assoc]
    · calc e.inv ≫ pullback.snd f (pullback.fst gmor i) ≫ pullback.snd gmor i
          = pullback.snd (f ≫ gmor) i := pullbackRightPullbackFstIso_inv_snd_snd gmor i f
        _ = castfg.inv ≫ pullback.snd fmor i := hcastfg_snd.symm
        _ = castfg.inv ≫ (restrictToOpen f i ≫ pullback.snd gmor i) := by rw [hrsnd]
        _ = (castfg.inv ≫ restrictToOpen f i) ≫ pullback.snd gmor i := by rw [Category.assoc]
  set Cx := (S.local_affine x).choose_spec.choose with hCx
  haveI : IsIso (Proj_loc_pair_open_φ X Z γ δ Cx i) := Proj_loc_pair_open_φ_isIso X Z γ δ Cx i
  have hrestrict : restrictToOpen f i = (pullbackSymmetry fmor i).hom ≫
      Proj_loc_pair_open_φ X Z γ δ Cx i ≫ (pullbackSymmetry i gmor).hom :=
    Proj_loc_pair_swap_restrict X Z γ δ Cx i
  haveI : IsIso (restrictToOpen f i) := by rw [hrestrict]; infer_instance
  haveI : IsIso (castfg.inv ≫ restrictToOpen f i) := inferInstance
  exact IsIso.of_isIso_fac_left key

abbrev Proj_loc_pair_incl (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair X Z γ δ ⟶ Proj_loc X Z γ :=
  pullback.snd (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
    (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))

instance Proj_loc_pair_incl_isOpenImmersion (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    IsOpenImmersion (Proj_loc_pair_incl X Z γ δ) := by
  haveI : IsOpenImmersion (Z.cov.map δ) := Z.cov.map_prop δ
  haveI : IsOpenImmersion (pullback.fst (Z.cov.map γ) (Z.cov.map δ)) := inferInstance
  exact inferInstanceAs
    (IsOpenImmersion (pullback.snd (pullback.fst (Z.cov.map γ) (Z.cov.map δ)) _))

@[reassoc]
lemma Proj_loc_pair_condition (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_mor X Z γ δ ≫ pullback.fst (Z.cov.map γ) (Z.cov.map δ) =
      Proj_loc_pair_incl X Z γ δ ≫ (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)) :=
  pullback.condition

@[reassoc]
lemma Proj_loc_pair_swap_mor (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_mor X Z δ γ =
      Proj_loc_pair_mor X Z γ δ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv := by
  have hswap : Proj_loc_pair_swap X Z γ δ ≫
      (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) =
      Proj_loc_pair_mor X Z γ δ := (Proj_loc_pair_swap_isOver X Z γ δ).1
  have h := congrArg (· ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv) hswap
  simpa [Category.assoc] using h

@[reassoc]
lemma Proj_loc_pair_swap_incl_over (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_incl X Z δ γ ≫
        (Proj_loc X Z δ ↘ Spec (Z.cov.obj δ)) ≫ Z.cov.map δ =
      Proj_loc_pair_incl X Z γ δ ≫ (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)) ≫ Z.cov.map γ := by
  rw [← Proj_loc_pair_condition_assoc X Z δ γ, ← Proj_loc_pair_condition_assoc X Z γ δ,
    ← Category.assoc (Proj_loc_pair_swap X Z γ δ), Proj_loc_pair_swap_mor, Category.assoc,
    ← Category.assoc (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv,
    pullbackSymmetry_inv_comp_fst, pullback.condition]

lemma pullbackSymmetry_inv_comp_inv {P Q R : Scheme} (f : P ⟶ R) (g : Q ⟶ R) :
    (pullbackSymmetry g f).inv ≫ (pullbackSymmetry f g).inv = 𝟙 (pullback f g) := by
  apply pullback.hom_ext <;> simp

lemma Proj_loc_pair_swap_comp_swap (X : Scheme) (Z : PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_swap X Z δ γ = 𝟙 _ := by

  have hmor : (Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_swap X Z δ γ) ≫
      Proj_loc_pair_mor X Z γ δ = Proj_loc_pair_mor X Z γ δ := by
    rw [Category.assoc, Proj_loc_pair_swap_mor X Z δ γ, ← Category.assoc,
      Proj_loc_pair_swap_mor X Z γ δ, Category.assoc, pullbackSymmetry_inv_comp_inv]

    exact Category.comp_id _

  letI : (Proj_loc_pair X Z γ δ).Over (Spec (Z.cov.obj γ)) :=
    ⟨Proj_loc_pair_incl X Z γ δ ≫ (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))⟩
  have hCars := open_of_blowup_IsCars (Z.cov.obj γ) (ideal_loc X Z γ)
    (Proj_loc_pair_incl X Z γ δ) ⟨rfl⟩
  have key : (Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_swap X Z δ γ) ≫
      Proj_loc_pair_incl X Z γ δ = Proj_loc_pair_incl X Z γ δ :=
    ProjBlowup_UnivProp_unicity_affine (Z.cov.obj γ) (ideal_loc X Z γ) hCars _ _
      ⟨show (Proj_loc_pair_swap X Z γ δ ≫ Proj_loc_pair_swap X Z δ γ) ≫
            Proj_loc_pair_incl X Z γ δ ≫ (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)) =
          Proj_loc_pair_incl X Z γ δ ≫ (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)) by
        rw [← Proj_loc_pair_condition X Z γ δ, ← Category.assoc, hmor]⟩
      ⟨rfl⟩
  haveI : Mono (Proj_loc_pair_incl X Z γ δ) := inferInstance
  rw [← cancel_mono (Proj_loc_pair_incl X Z γ δ), Category.id_comp]
  exact key

noncomputable def Proj_loc_pair_t' (X : Scheme) (Z : PreClos X) (i j k : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    pullback (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ⟶
      pullback (Proj_loc_pair_incl X Z j k) (Proj_loc_pair_incl X Z j i) :=
  pullback.lift
    (pullback.lift
      (pullback.lift
        (pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
          Proj_loc_pair_swap X Z i j ≫ Proj_loc_pair_incl X Z j i ≫
          (Proj_loc X Z j ↘ Spec (Z.cov.obj j)))
        (pullback.snd (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
          Proj_loc_pair_swap X Z i k ≫ Proj_loc_pair_incl X Z k i ≫
          (Proj_loc X Z k ↘ Spec (Z.cov.obj k)))
        (by
          simp only [Category.assoc]
          rw [Proj_loc_pair_swap_incl_over X Z i j, Proj_loc_pair_swap_incl_over X Z i k,
            ← Category.assoc (pullback.fst (Proj_loc_pair_incl X Z i j)
              (Proj_loc_pair_incl X Z i k)),
            ← Category.assoc (pullback.snd (Proj_loc_pair_incl X Z i j)
              (Proj_loc_pair_incl X Z i k)),
            pullback.condition]))
      (pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
        Proj_loc_pair_swap X Z i j ≫ Proj_loc_pair_incl X Z j i)
      (by simp only [pullback.lift_fst, Category.assoc]))
    (pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
      Proj_loc_pair_swap X Z i j)
    (by simp only [pullback.lift_snd, Category.assoc])

@[reassoc]
lemma Proj_loc_pair_t'_snd (X : Scheme) (Z : PreClos X) (i j k : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_t' X Z i j k ≫
        pullback.snd (Proj_loc_pair_incl X Z j k) (Proj_loc_pair_incl X Z j i) =
      pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
        Proj_loc_pair_swap X Z i j := by
  delta Proj_loc_pair_t'
  exact pullback.lift_snd _ _ _

@[reassoc]
lemma Proj_loc_pair_t'_fst_incl (X : Scheme) (Z : PreClos X) (i j k : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_t' X Z i j k ≫
        pullback.fst (Proj_loc_pair_incl X Z j k) (Proj_loc_pair_incl X Z j i) ≫
        Proj_loc_pair_incl X Z j k =
      pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
        Proj_loc_pair_swap X Z i j ≫ Proj_loc_pair_incl X Z j i := by
  delta Proj_loc_pair_t'
  rw [pullback.lift_fst_assoc]
  exact pullback.lift_snd _ _ _

@[reassoc]
lemma Proj_loc_pair_t'_fst_mor_snd (X : Scheme) (Z : PreClos X) (i j k : Z.cov.J)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Proj_loc_pair_t' X Z i j k ≫
        pullback.fst (Proj_loc_pair_incl X Z j k) (Proj_loc_pair_incl X Z j i) ≫
        Proj_loc_pair_mor X Z j k ≫ pullback.snd (Z.cov.map j) (Z.cov.map k) =
      pullback.snd (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
        Proj_loc_pair_swap X Z i k ≫ Proj_loc_pair_incl X Z k i ≫
        (Proj_loc X Z k ↘ Spec (Z.cov.obj k)) := by
  delta Proj_loc_pair_t' Proj_loc_pair_mor
  rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  exact pullback.lift_snd _ _ _

def PreBlGlob  (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme.GlueData where
  J := Z.cov.J
  U γ := Proj_loc X Z γ
  V pair := Proj_loc_pair X Z pair.1 pair.2
  f γ δ := pullback.snd _ _
  f_mono γ δ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by infer_instance
  t γ δ := Proj_loc_pair_swap X Z γ δ
  t_id i := by
    dsimp
    symm
    apply Proj_loc_pair_swap_uniq

    ·

      intro C k _
      haveI : Mono (Z.cov.map i) := by
        haveI : IsOpenImmersion (Z.cov.map i) := Z.cov.map_prop i
        infer_instance
      have monofact : Proj_loc_pair_mor X Z i i ≫
          (pullbackSymmetry (Z.cov.map i) (Z.cov.map i)).hom = Proj_loc_pair_mor X Z i i := by
        rw [pullbackSymmetry_hom_of_mono_eq]; exact Category.comp_id _
      set castk2 : pullback (Proj_loc_pair_mor X Z i i) k ≅
          pullback (Proj_loc_pair_mor X Z i i ≫
            (pullbackSymmetry (Z.cov.map i) (Z.cov.map i)).hom) k :=
        pullback.congrHom monofact.symm rfl with hcastk2
      delta restrictToOpen
      show castk2.hom = _
      set castk : pullback k (Proj_loc_pair_mor X Z i i) ≅
          pullback k (Proj_loc_pair_mor X Z i i ≫
            (pullbackSymmetry (Z.cov.map i) (Z.cov.map i)).hom) :=
        pullback.congrHom rfl monofact.symm with hcastk
      have hcastk_fst : castk.hom ≫ pullback.fst k (Proj_loc_pair_mor X Z i i ≫
          (pullbackSymmetry (Z.cov.map i) (Z.cov.map i)).hom) = pullback.fst k
          (Proj_loc_pair_mor X Z i i) := by rw [hcastk]; simp
      have hcastk_isOver : Scheme.Hom.IsOver castk.hom (Spec C) := ⟨hcastk_fst⟩
      have huniq := Proj_loc_pair_open_φ_uniq X Z i i C k castk.hom hcastk_isOver
      rw [← huniq]
      apply pullback.hom_ext
      · rw [hcastk2]; simp [hcastk]
      · rw [hcastk2]; simp [hcastk]
    ·

      haveI : Mono (Z.cov.map i) := by
        haveI : IsOpenImmersion (Z.cov.map i) := Z.cov.map_prop i
        infer_instance
      rw [Scheme.Hom.isOver_iff, Category.id_comp]
      show Proj_loc_pair_mor X Z i i ≫ (pullbackSymmetry _ _).hom =
        Proj_loc_pair_mor X Z i i
      rw [pullbackSymmetry_hom_of_mono_eq]
      exact Category.comp_id _
  t' i j k := Proj_loc_pair_t' X Z i j k
  t_fac i j k := Proj_loc_pair_t'_snd X Z i j k
  cocycle i j k := by

    set m := pullback.fst (Proj_loc_pair_incl X Z i j) (Proj_loc_pair_incl X Z i k) ≫
      Proj_loc_pair_incl X Z i j with hm
    haveI : IsOpenImmersion m := by rw [hm]; infer_instance
    haveI : Mono m := inferInstance

    letI : (pullback (Proj_loc_pair_incl X Z i j)
        (Proj_loc_pair_incl X Z i k)).Over (Spec (Z.cov.obj i)) :=
      ⟨m ≫ (Proj_loc X Z i ↘ Spec (Z.cov.obj i))⟩
    have hCars := open_of_blowup_IsCars (Z.cov.obj i) (ideal_loc X Z i) m ⟨rfl⟩

    have hover : (Proj_loc_pair_t' X Z i j k ≫ Proj_loc_pair_t' X Z j k i ≫
        Proj_loc_pair_t' X Z k i j) ≫ m ≫ (Proj_loc X Z i ↘ Spec (Z.cov.obj i)) =
        m ≫ (Proj_loc X Z i ↘ Spec (Z.cov.obj i)) := by
      rw [hm]
      simp only [Category.assoc]
      rw [Proj_loc_pair_t'_fst_incl_assoc X Z k i j, ← Proj_loc_pair_condition X Z i k,
        Proj_loc_pair_swap_mor_assoc X Z k i, pullbackSymmetry_inv_comp_fst,
        Proj_loc_pair_t'_fst_mor_snd X Z j k i, Proj_loc_pair_t'_snd_assoc X Z i j k,
        ← Category.assoc (Proj_loc_pair_swap X Z i j), Proj_loc_pair_swap_comp_swap,
        Category.id_comp]
    have key : (Proj_loc_pair_t' X Z i j k ≫ Proj_loc_pair_t' X Z j k i ≫
        Proj_loc_pair_t' X Z k i j) ≫ m = m :=
      ProjBlowup_UnivProp_unicity_affine (Z.cov.obj i) (ideal_loc X Z i) hCars _ _
        ⟨by rw [Category.assoc]; exact hover⟩ ⟨rfl⟩
    rw [← cancel_mono m, Category.id_comp]
    exact key
  f_open := inferInstance

abbrev BlGlob (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  Scheme.GlueData.glued (PreBlGlob Z)

instance (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  Scheme.Over (BlGlob Z) X where
  hom := Multicoequalizer.desc _ _
    (fun γ : Z.cov.J => Proj_loc X Z γ ↘ X) <| by
    rintro ⟨γ, δ⟩
    simp only [MultispanShape.prod_L, GlueData.diagram_left, MultispanShape.prod_fst,
      GlueData.diagram_right,
      MultispanShape.prod_snd] at γ ⊢
    change pullback.snd _ _ ≫ _ = (Proj_loc_pair_swap X Z γ δ ≫ pullback.snd _ _) ≫ _
    simp only [Category.assoc]
    set Fγ := pullback.fst (Z.cov.map γ) (Z.cov.map δ) with hFγ
    set Fδ := pullback.fst (Z.cov.map δ) (Z.cov.map γ) with hFδ
    set Gγ := (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) with hGγ
    set Gδ := (Proj_loc X Z δ) ↘ (Spec (Z.cov.obj δ)) with hGδ
    have hcond_γ : Proj_loc_pair_mor X Z γ δ ≫ Fγ = pullback.snd Fγ Gγ ≫ Gγ := by
      show pullback.fst Fγ Gγ ≫ Fγ = _
      exact pullback.condition
    have hcond_δ : Proj_loc_pair_mor X Z δ γ ≫ Fδ = pullback.snd Fδ Gδ ≫ Gδ := by
      show pullback.fst Fδ Gδ ≫ Fδ = _
      exact pullback.condition
    set fmor := Proj_loc_pair_mor X Z γ δ with hfmor
    set fδγ := Proj_loc_pair_mor X Z δ γ with hfδγ
    have hswap : Proj_loc_pair_swap X Z γ δ ≫
        (fδγ ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).hom) = fmor :=
      (Proj_loc_pair_swap_isOver X Z γ δ).1
    have hswap2 : Proj_loc_pair_swap X Z γ δ ≫ fδγ =
        fmor ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv := by
      have h := congrArg (· ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv) hswap
      simpa [Category.assoc] using h
    have hFγeq : Fγ ≫ Z.cov.map γ =
        pullback.snd (Z.cov.map γ) (Z.cov.map δ) ≫ Z.cov.map δ := by
      show open_pair_map X Z γ δ = _
      exact open_pair_map_equal X Z γ δ
    have hsym : (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫ (Fδ ≫ Z.cov.map δ) =
        pullback.snd (Z.cov.map γ) (Z.cov.map δ) ≫ Z.cov.map δ := by
      rw [← Category.assoc, hFδ, pullbackSymmetry_inv_comp_fst]
    calc pullback.snd Fγ Gγ ≫ (Gγ ≫ Z.cov.map γ)
        = (pullback.snd Fγ Gγ ≫ Gγ) ≫ Z.cov.map γ := by rw [Category.assoc]
      _ = (fmor ≫ Fγ) ≫ Z.cov.map γ := by rw [← hcond_γ]
      _ = fmor ≫ (Fγ ≫ Z.cov.map γ) := by rw [Category.assoc]
      _ = fmor ≫ (pullback.snd (Z.cov.map γ) (Z.cov.map δ) ≫ Z.cov.map δ) := by rw [hFγeq]
      _ = fmor ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv ≫ (Fδ ≫ Z.cov.map δ) := by
          rw [hsym]
      _ = (fmor ≫ (pullbackSymmetry (Z.cov.map δ) (Z.cov.map γ)).inv) ≫ (Fδ ≫ Z.cov.map δ) := by
          rw [Category.assoc]
      _ = (Proj_loc_pair_swap X Z γ δ ≫ fδγ) ≫ (Fδ ≫ Z.cov.map δ) := by rw [← hswap2]
      _ = Proj_loc_pair_swap X Z γ δ ≫ (fδγ ≫ Fδ) ≫ Z.cov.map δ := by
          rw [Category.assoc, Category.assoc]
      _ = Proj_loc_pair_swap X Z γ δ ≫ (pullback.snd Fδ Gδ ≫ Gδ) ≫ Z.cov.map δ := by rw [hcond_δ]
      _ = (Proj_loc_pair_swap X Z γ δ ≫ pullback.snd Fδ Gδ) ≫ (Gδ ≫ Z.cov.map δ) := by
          rw [Category.assoc, Category.assoc]

noncomputable def Proj_loc_pullback_over (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (γ : Z.cov.J) :
    Proj_loc X Z γ ≅ pullback ((BlGlob Z) ↘ X) (Z.cov.map γ) := by
  set D := PreBlGlob Z with hD
  set σ := (BlGlob Z) ↘ X with hσ
  have hισ : ∀ δ, D.ι δ ≫ σ = (Proj_loc X Z δ) ↘ X := by
    intro δ
    show D.ι δ ≫ Multicoequalizer.desc _ _ (fun δ => Proj_loc X Z δ ↘ X) _ = _
    exact Multicoequalizer.π_desc _ _ _ _ _
  apply IsOpenImmersion.isoOfRangeEq (D.ι γ) (pullback.fst σ (Z.cov.map γ))
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    have hz : σ.base ((D.ι γ).base y) =
        (Z.cov.map γ).base ((Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)).base y) := by
      rw [← Scheme.comp_base_apply, hισ γ]; rfl
    obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback
      ((D.ι γ).base y) ((Proj_loc X Z γ ↘ Spec (Z.cov.obj γ)).base y) hz
    exact ⟨q, hq1⟩
  · rintro z ⟨q, rfl⟩
    have hσz : σ.base ((pullback.fst σ (Z.cov.map γ)).base q) =
        (Z.cov.map γ).base ((pullback.snd σ (Z.cov.map γ)).base q) := by
      rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, pullback.condition]
    set p := (pullback.snd σ (Z.cov.map γ)).base q with hpdef
    obtain ⟨δ, w, hw⟩ := D.ι_jointly_surjective ((pullback.fst σ (Z.cov.map γ)).base q)
    have hmem : σ.base ((D.ι δ).base w) = (Z.cov.map γ).base p := by rw [hw]; exact hσz
    rw [← Scheme.comp_base_apply, hισ δ] at hmem
    have hmem' : (Z.cov.map δ).base ((Proj_loc X Z δ ↘ Spec (Z.cov.obj δ)).base w) =
        (Z.cov.map γ).base p := by
      rw [← Scheme.comp_base_apply]; exact hmem
    obtain ⟨q', hq1', hq2'⟩ := Scheme.Pullback.exists_preimage_pullback
      ((Proj_loc X Z δ ↘ Spec (Z.cov.obj δ)).base w) p hmem'
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst (Z.cov.map δ) (Z.cov.map γ))
      (g := Proj_loc X Z δ ↘ Spec (Z.cov.obj δ)) q' w hq1'
    refine ⟨(D.f γ δ).base ((D.t δ γ).base r), ?_⟩
    show (D.f γ δ ≫ D.ι γ).base ((D.t δ γ).base r) = _
    rw [← Scheme.comp_base_apply]
    rw [show D.t δ γ ≫ D.f γ δ ≫ D.ι γ = D.f δ γ ≫ D.ι δ from D.glue_condition δ γ]
    rw [Scheme.comp_base_apply]
    show (D.ι δ).base ((D.f δ γ).base r) = _
    have : (D.f δ γ).base r = w := hr2
    rw [this, ← hw]

@[reassoc]
lemma Proj_loc_pullback_over_hom_fst (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (γ : Z.cov.J) :
    (Proj_loc_pullback_over Z γ).hom ≫ pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      (PreBlGlob Z).ι γ := by
  simp [Proj_loc_pullback_over]

@[reassoc]
lemma Proj_loc_pullback_over_hom_snd (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (γ : Z.cov.J) :
    (Proj_loc_pullback_over Z γ).hom ≫ pullback.snd ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) := by
  have hισγ : (PreBlGlob Z).ι γ ≫ ((BlGlob Z) ↘ X) = (Proj_loc X Z γ) ↘ X := by
    show (PreBlGlob Z).ι γ ≫ Multicoequalizer.desc _ _ (fun γ => Proj_loc X Z γ ↘ X) _ = _
    exact Multicoequalizer.π_desc _ _ _ _ _
  have h1 : (Proj_loc_pullback_over Z γ).hom ≫
      pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) ≫ ((BlGlob Z) ↘ X) =
      (PreBlGlob Z).ι γ ≫ ((BlGlob Z) ↘ X) := by
    rw [← Category.assoc, Proj_loc_pullback_over_hom_fst]
  rw [pullback.condition, hισγ] at h1
  have h2 : ((Proj_loc X Z γ) ↘ X : Proj_loc X Z γ ⟶ X) =
      ((Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ))) ≫ Z.cov.map γ := rfl
  rw [h2, ← Category.assoc] at h1
  exact (cancel_mono (Z.cov.map γ)).mp h1

lemma PreProjBlowup_UnivProp_unicity_Cars (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsCars _ <| pullback_Clos (T ↘ X) (Quotient.mk'' Z))
    (φ φ' : T ⟶ BlGlob Z)
    (φ_over : Scheme.Hom.IsOver φ X)
    (φ'_over : Scheme.Hom.IsOver φ' X)
    : φ = φ'  := by
  haveI := φ_over
  haveI := φ'_over
  set π := T ↘ X with hπ
  set D := PreBlGlob Z with hD
  set 𝒱 := Z.cov.cover.pullbackCover π with h𝒱
  refine 𝒱.hom_ext _ _ (fun γ => ?_)
  set e := Proj_loc_pullback_over Z γ with he
  have hekey : e.hom ≫ pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) = D.ι γ := by
    rw [he]; simp [Proj_loc_pullback_over]; rfl

  have hCars : IsCars _ (pullback_Clos ((pullback π (Z.cov.map γ)) ↘ Spec (Z.cov.obj γ))
      (loc_to_Clos (Z.cov.obj γ) (ideal_loc X Z γ))) := by
    rw [loc_to_Clos_chart X Z γ, ← pullback_assoc]
    have heq : ((pullback π (Z.cov.map γ)) ↘ Spec (Z.cov.obj γ)) ≫ Z.cov.map γ =
        pullback.fst π (Z.cov.map γ) ≫ π := pullback.condition.symm
    rw [heq, pullback_assoc]
    exact pullback_IsCars _ (pullback.fst π (Z.cov.map γ)) _ cond

  have hισγ : D.ι γ ≫ ((BlGlob Z) ↘ X) = (Proj_loc X Z γ) ↘ X := by
    show D.ι γ ≫ Multicoequalizer.desc _ _ (fun γ => Proj_loc X Z γ ↘ X) _ = _
    exact Multicoequalizer.π_desc _ _ _ _ _
  have hesnd : e.hom ≫ pullback.snd ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) := by
    have h1 : e.hom ≫ pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) ≫ ((BlGlob Z) ↘ X) =
        D.ι γ ≫ ((BlGlob Z) ↘ X) := by rw [← Category.assoc, hekey]
    rw [pullback.condition, hισγ] at h1
    have h2 : ((Proj_loc X Z γ) ↘ X : Proj_loc X Z γ ⟶ X) =
        ((Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ))) ≫ Z.cov.map γ := rfl
    rw [h2, ← Category.assoc] at h1
    exact (cancel_mono (Z.cov.map γ)).mp h1
  have hekey2snd : pullback.snd ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      e.inv ≫ (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) := by
    rw [← hesnd, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hφ_over_γ : Scheme.Hom.IsOver (restrictToOpen φ (Z.cov.map γ) ≫ e.inv)
      (Spec (Z.cov.obj γ)) := by
    rw [Scheme.Hom.isOver_iff]
    show restrictToOpen φ (Z.cov.map γ) ≫ e.inv ≫ (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) = _
    rw [← hekey2snd]
    exact restrictToOpen_snd φ (Z.cov.map γ)
  have hφ'_over_γ : Scheme.Hom.IsOver (restrictToOpen φ' (Z.cov.map γ) ≫ e.inv)
      (Spec (Z.cov.obj γ)) := by
    rw [Scheme.Hom.isOver_iff]
    show restrictToOpen φ' (Z.cov.map γ) ≫ e.inv ≫ (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) = _
    rw [← hekey2snd]
    exact restrictToOpen_snd φ' (Z.cov.map γ)
  have hrγ := ProjBlowup_UnivProp_unicity_affine (Z.cov.obj γ) (ideal_loc X Z γ) hCars
    (restrictToOpen φ (Z.cov.map γ) ≫ e.inv) (restrictToOpen φ' (Z.cov.map γ) ≫ e.inv)
    hφ_over_γ hφ'_over_γ
  have hrfst : restrictToOpen φ (Z.cov.map γ) ≫ pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      pullback.fst π (Z.cov.map γ) ≫ φ := restrictToOpen_fst φ (Z.cov.map γ)
  have hr'fst : restrictToOpen φ' (Z.cov.map γ) ≫ pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) =
      pullback.fst π (Z.cov.map γ) ≫ φ' := restrictToOpen_fst φ' (Z.cov.map γ)
  have hekey2 : pullback.fst ((BlGlob Z) ↘ X) (Z.cov.map γ) = e.inv ≫ D.ι γ := by
    rw [← hekey, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  show 𝒱.map γ ≫ φ = 𝒱.map γ ≫ φ'
  show pullback.fst π (Z.cov.map γ) ≫ φ = pullback.fst π (Z.cov.map γ) ≫ φ'
  rw [← hrfst, ← hr'fst, hekey2, ← Category.assoc, ← Category.assoc, hrγ]

lemma PreProjBlowup_UnivProp_existence_Cars
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsCars _ <| pullback_Clos (T ↘ X) (Quotient.mk'' Z)) :
    ∃  φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
  set π := T ↘ X with hπ
  set 𝒱 := Z.cov.cover.pullbackCover π with h𝒱
  have hCars : ∀ γ : Z.cov.J, IsCars _ (pullback_Clos
      ((pullback π (Z.cov.map γ)) ↘ Spec (Z.cov.obj γ))
      (loc_to_Clos (Z.cov.obj γ) (ideal_loc X Z γ))) := by
    intro γ
    rw [loc_to_Clos_chart X Z γ, ← pullback_assoc]
    have heq : ((pullback π (Z.cov.map γ)) ↘ Spec (Z.cov.obj γ)) ≫ Z.cov.map γ =
        pullback.fst π (Z.cov.map γ) ≫ π := pullback.condition.symm
    rw [heq, pullback_assoc]
    exact pullback_IsCars _ (pullback.fst π (Z.cov.map γ)) _ cond
  set D := PreBlGlob Z with hD
  let choice : ∀ γ : Z.cov.J, 𝒱.obj γ ⟶ Proj_loc X Z γ := fun γ =>
    (ProjBlowup_UnivProp_existence_affine (Z.cov.obj γ) (ideal_loc X Z γ) (hCars γ)).choose
  have hchoice_over : ∀ γ : Z.cov.J, choice γ ≫ ((Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ))) =
      (pullback π (Z.cov.map γ)) ↘ (Spec (Z.cov.obj γ)) := fun γ =>
    (ProjBlowup_UnivProp_existence_affine (Z.cov.obj γ) (ideal_loc X Z γ)
      (hCars γ)).choose_spec.1

  let φ_loc : ∀ γ : Z.cov.J, 𝒱.obj γ ⟶ BlGlob Z := fun γ => choice γ ≫ D.ι γ
  have hφ_loc_over : ∀ γ : Z.cov.J, φ_loc γ ≫ ((BlGlob Z) ↘ X) =
      pullback.fst π (Z.cov.map γ) ≫ π := by
    intro γ
    show (choice γ ≫ D.ι γ) ≫ ((BlGlob Z) ↘ X) = _
    have hισγ : D.ι γ ≫ ((BlGlob Z) ↘ X) = (Proj_loc X Z γ) ↘ X := by
      show D.ι γ ≫ Multicoequalizer.desc _ _ (fun γ => Proj_loc X Z γ ↘ X) _ = _
      exact Multicoequalizer.π_desc _ _ _ _ _
    rw [Category.assoc, hισγ]
    have h2 : ((Proj_loc X Z γ) ↘ X : Proj_loc X Z γ ⟶ X) =
        ((Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ))) ≫ Z.cov.map γ := rfl
    rw [h2, ← Category.assoc, hchoice_over γ]
    exact (pullback.condition (f := π) (g := Z.cov.map γ)).symm

  have hcocycle : ∀ x y : Z.cov.J, pullback.fst (𝒱.map x) (𝒱.map y) ≫ φ_loc x =
      pullback.snd (𝒱.map x) (𝒱.map y) ≫ φ_loc y := by
    intro x y
    set ℓ := open_pair_map X Z x y with hℓ
    set e := pullbackDoubleFstIso π (Z.cov.map x) (Z.cov.map y) with he
    rw [show pullback.fst (𝒱.map x) (𝒱.map y) ≫ φ_loc x =
          e.hom ≫ e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y) ≫ φ_loc x by
        rw [Iso.hom_inv_id_assoc],
      show pullback.snd (𝒱.map x) (𝒱.map y) ≫ φ_loc y =
          e.hom ≫ e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y) ≫ φ_loc y by
        rw [Iso.hom_inv_id_assoc]]
    congr 1
    haveI : IsOpenImmersion (Z.cov.map x) := Z.cov.map_prop x
    haveI : IsOpenImmersion (Z.cov.map y) := Z.cov.map_prop y

    set W := pullback π ℓ with hW
    set ρx : W ⟶ pullback π (Z.cov.map x) :=
      pullback.lift (pullback.fst π ℓ)
        (pullback.snd π ℓ ≫ pullback.fst (Z.cov.map x) (Z.cov.map y))
        (by rw [Category.assoc]; exact pullback.condition) with hρxdef
    have hρxfst : ρx ≫ pullback.fst π (Z.cov.map x) = pullback.fst π ℓ := by
      rw [hρxdef, pullback.lift_fst]
    have hρxsnd : ρx ≫ pullback.snd π (Z.cov.map x) =
        pullback.snd π ℓ ≫ pullback.fst (Z.cov.map x) (Z.cov.map y) := by
      rw [hρxdef, pullback.lift_snd]
    have hρx : e.inv ≫ pullback.fst (𝒱.map x) (𝒱.map y) = ρx :=
      pullbackDoubleFstIso_inv_fst π (Z.cov.map x) (Z.cov.map y)
    set ρy : W ⟶ pullback π (Z.cov.map y) :=
      pullback.lift (pullback.fst π ℓ)
        (pullback.snd π ℓ ≫ pullback.snd (Z.cov.map x) (Z.cov.map y))
        (by
          rw [Category.assoc,
            show pullback.snd (Z.cov.map x) (Z.cov.map y) ≫ Z.cov.map y =
              pullback.fst (Z.cov.map x) (Z.cov.map y) ≫ Z.cov.map x from
              (pullback.condition (f := Z.cov.map x) (g := Z.cov.map y)).symm]
          exact pullback.condition) with hρydef
    have hρyfst : ρy ≫ pullback.fst π (Z.cov.map y) = pullback.fst π ℓ := by
      rw [hρydef, pullback.lift_fst]
    have hρysnd : ρy ≫ pullback.snd π (Z.cov.map y) =
        pullback.snd π ℓ ≫ pullback.snd (Z.cov.map x) (Z.cov.map y) := by
      rw [hρydef, pullback.lift_snd]
    have hρy : e.inv ≫ pullback.snd (𝒱.map x) (𝒱.map y) = ρy :=
      pullbackDoubleFstIso_inv_snd π (Z.cov.map x) (Z.cov.map y)
    simp only [← Category.assoc, hρx, hρy]

    haveI : IsOpenImmersion ρx := by rw [← hρx]; infer_instance
    haveI : IsOpenImmersion ρy := by rw [← hρy]; infer_instance

    letI hTx : W.Over (Spec (Z.cov.obj x)) :=
      ⟨pullback.snd π ℓ ≫ pullback.fst (Z.cov.map x) (Z.cov.map y)⟩
    letI hTy : W.Over (Spec (Z.cov.obj y)) :=
      ⟨pullback.snd π ℓ ≫ pullback.snd (Z.cov.map x) (Z.cov.map y)⟩
    have hρx_over : Scheme.Hom.IsOver ρx (Spec (Z.cov.obj x)) := ⟨hρxsnd⟩
    have hρy_over : Scheme.Hom.IsOver ρy (Spec (Z.cov.obj y)) := ⟨hρysnd⟩
    have heqx : ρx ≫ ((pullback π (Z.cov.map x)) ↘ Spec (Z.cov.obj x)) =
        W ↘ Spec (Z.cov.obj x) := by
      have h := hρx_over; rw [Scheme.Hom.isOver_iff] at h; exact h
    have heqy : ρy ≫ ((pullback π (Z.cov.map y)) ↘ Spec (Z.cov.obj y)) =
        W ↘ Spec (Z.cov.obj y) := by
      have h := hρy_over; rw [Scheme.Hom.isOver_iff] at h; exact h
    have hCarsx' : IsCars _ (pullback_Clos (W ↘ Spec (Z.cov.obj x))
        (loc_to_Clos (Z.cov.obj x) (ideal_loc X Z x))) := by
      rw [← heqx, pullback_assoc]
      exact pullback_IsCars _ ρx _ (hCars x)
    have hCarsy' : IsCars _ (pullback_Clos (W ↘ Spec (Z.cov.obj y))
        (loc_to_Clos (Z.cov.obj y) (ideal_loc X Z y))) := by
      rw [← heqy, pullback_assoc]
      exact pullback_IsCars _ ρy _ (hCars y)
    have hrestrict_x : ρx ≫ choice x =
        (ProjBlowup_UnivProp_existence_affine (Z.cov.obj x) (ideal_loc X Z x) hCarsx').choose :=
      ProjBlowup_UnivProp_existence_affine_restrict (Z.cov.obj x) (ideal_loc X Z x) (hCars x)
        ρx hρx_over hCarsx'
    have hrestrict_y : ρy ≫ choice y =
        (ProjBlowup_UnivProp_existence_affine (Z.cov.obj y) (ideal_loc X Z y) hCarsy').choose :=
      ProjBlowup_UnivProp_existence_affine_restrict (Z.cov.obj y) (ideal_loc X Z y) (hCars y)
        ρy hρy_over hCarsy'
    set choice_finer_x := (ProjBlowup_UnivProp_existence_affine (Z.cov.obj x) (ideal_loc X Z x)
      hCarsx').choose with hcfx
    set choice_finer_y := (ProjBlowup_UnivProp_existence_affine (Z.cov.obj y) (ideal_loc X Z y)
      hCarsy').choose with hcfy
    have hκ_compat : pullback.snd π ℓ ≫ pullback.fst (Z.cov.map x) (Z.cov.map y) =
        choice_finer_x ≫ ((Proj_loc X Z x) ↘ Spec (Z.cov.obj x)) := by
      rw [← hrestrict_x, Category.assoc, hchoice_over x]
      exact hρxsnd.symm
    set κ2 : W ⟶ Proj_loc_pair X Z x y :=
      pullback.lift (pullback.snd π ℓ) choice_finer_x hκ_compat with hκ2
    have hκ2_f : κ2 ≫ D.f x y = choice_finer_x := by
      show κ2 ≫ pullback.snd _ _ = _
      rw [hκ2, pullback.lift_snd]
    have hκ2_mor : κ2 ≫ Proj_loc_pair_mor X Z x y = pullback.snd π ℓ := by
      show κ2 ≫ pullback.fst _ _ = _
      rw [hκ2, pullback.lift_fst]

    have hswap_mor : D.t x y ≫ Proj_loc_pair_mor X Z y x =
        Proj_loc_pair_mor X Z x y ≫ (pullbackSymmetry (Z.cov.map y) (Z.cov.map x)).inv := by
      have hswap : Proj_loc_pair_swap X Z x y ≫
          (Proj_loc_pair_mor X Z y x ≫ (pullbackSymmetry (Z.cov.map y) (Z.cov.map x)).hom) =
          Proj_loc_pair_mor X Z x y := (Proj_loc_pair_swap_isOver X Z x y).1
      show Proj_loc_pair_swap X Z x y ≫ Proj_loc_pair_mor X Z y x = _
      have h := congrArg (· ≫ (pullbackSymmetry (Z.cov.map y) (Z.cov.map x)).inv) hswap
      simpa [Category.assoc] using h
    have hfy : D.f y x ≫ ((Proj_loc X Z y) ↘ Spec (Z.cov.obj y)) =
        Proj_loc_pair_mor X Z y x ≫ pullback.fst (Z.cov.map y) (Z.cov.map x) := by
      show pullback.snd (pullback.fst (Z.cov.map y) (Z.cov.map x))
        ((Proj_loc X Z y) ↘ Spec (Z.cov.obj y)) ≫ _ = _
      exact pullback.condition.symm

    let μ : W ⟶ Proj_loc X Z y := κ2 ≫ D.t x y ≫ D.f y x
    have hμ : μ = κ2 ≫ D.t x y ≫ D.f y x := rfl
    have ha : μ ≫ ((Proj_loc X Z y) ↘ Spec (Z.cov.obj y)) = W ↘ (Spec (Z.cov.obj y)) := by
      rw [hμ]
      calc (κ2 ≫ D.t x y ≫ D.f y x) ≫ ((Proj_loc X Z y) ↘ Spec (Z.cov.obj y))
          = κ2 ≫ D.t x y ≫ (D.f y x ≫ ((Proj_loc X Z y) ↘ Spec (Z.cov.obj y))) := by
            simp only [Category.assoc]
        _ = κ2 ≫ D.t x y ≫
              (Proj_loc_pair_mor X Z y x ≫ pullback.fst (Z.cov.map y) (Z.cov.map x)) := by
            rw [hfy]
        _ = κ2 ≫ (D.t x y ≫ Proj_loc_pair_mor X Z y x) ≫
              pullback.fst (Z.cov.map y) (Z.cov.map x) := by
            simp only [Category.assoc]
        _ = κ2 ≫ (Proj_loc_pair_mor X Z x y ≫
              (pullbackSymmetry (Z.cov.map y) (Z.cov.map x)).inv) ≫
              pullback.fst (Z.cov.map y) (Z.cov.map x) := by rw [hswap_mor]
        _ = κ2 ≫ Proj_loc_pair_mor X Z x y ≫
              ((pullbackSymmetry (Z.cov.map y) (Z.cov.map x)).inv ≫
                pullback.fst (Z.cov.map y) (Z.cov.map x)) := by
            simp only [Category.assoc]
        _ = κ2 ≫ Proj_loc_pair_mor X Z x y ≫ pullback.snd (Z.cov.map x) (Z.cov.map y) := by
            rw [pullbackSymmetry_inv_comp_fst]
        _ = (κ2 ≫ Proj_loc_pair_mor X Z x y) ≫ pullback.snd (Z.cov.map x) (Z.cov.map y) := by
            simp only [Category.assoc]
        _ = pullback.snd π ℓ ≫ pullback.snd (Z.cov.map x) (Z.cov.map y) := by rw [hκ2_mor]
        _ = W ↘ (Spec (Z.cov.obj y)) := rfl
    have hb : Scheme.Hom.IsOver μ (Spec (Z.cov.obj y)) := ⟨ha⟩
    have hStep2 : μ = choice_finer_y :=
      ProjBlowup_UnivProp_unicity_affine (Z.cov.obj y) (ideal_loc X Z y) hCarsy'
        μ choice_finer_y hb
        (ProjBlowup_UnivProp_existence_affine (Z.cov.obj y) (ideal_loc X Z y)
          hCarsy').choose_spec
    have hglue := D.glue_condition x y

    have hfinal : choice_finer_x ≫ D.ι x = choice_finer_y ≫ D.ι y := by
      rw [← hκ2_f]
      calc (κ2 ≫ D.f x y) ≫ D.ι x = κ2 ≫ (D.f x y ≫ D.ι x) := by rw [Category.assoc]
        _ = κ2 ≫ (D.t x y ≫ D.f y x ≫ D.ι y) := by rw [← hglue]
        _ = (κ2 ≫ D.t x y ≫ D.f y x) ≫ D.ι y := by simp only [Category.assoc]
        _ = choice_finer_y ≫ D.ι y := by rw [← hμ, hStep2]
    show ρx ≫ (choice x ≫ D.ι x) = ρy ≫ (choice y ≫ D.ι y)
    rw [← Category.assoc, ← Category.assoc, hrestrict_x, hrestrict_y]
    exact hfinal
  refine ⟨𝒱.glueMorphisms φ_loc hcocycle, ?_⟩
  rw [Scheme.Hom.isOver_iff]
  refine 𝒱.hom_ext _ _ (fun γ => ?_)
  rw [← Category.assoc, 𝒱.ι_glueMorphisms]
  exact hφ_loc_over γ

lemma PreProjBlowup_UnivProp_unicity (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z)
    (φ φ' : T ⟶ BlGlob Z)
    (φ_over : Scheme.Hom.IsOver φ X)
    (φ'_over : Scheme.Hom.IsOver φ' X)
    : φ = φ'  :=
  PreProjBlowup_UnivProp_unicity_Cars Z ⟨_, cond, rfl⟩ φ φ' φ_over φ'_over

lemma PreProjBlowup_UnivProp_existence
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃  φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X :=
  PreProjBlowup_UnivProp_existence_Cars Z ⟨_, cond, rfl⟩

lemma PreProjBlowup_UnivProp
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃! φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
  obtain ⟨φ, hφ⟩ := PreProjBlowup_UnivProp_existence Z cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact PreProjBlowup_UnivProp_unicity Z cond φ φ' hφ hφ' |>.symm

lemma centres_eq_of_rel (Z' Z'' : PreClos X) (eq : Quotient.mk' Z' = Quotient.mk' Z'')
    [DecidableEq Z'.indnumb]
    [DecidableEq Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (γ' : Z'.cov.J) (γ'' : Z''.cov.J)
    (C : CommRingCat)
    (k' : Spec C ⟶ Spec (Z'.cov.obj γ')) (k'' : Spec C ⟶ Spec (Z''.cov.obj γ''))
    (hmap : k' ≫ Z'.cov.map γ' = k'' ≫ Z''.cov.map γ'') :
    loc_to_Clos C (fun j => Ideal.map (Spec.preimage k').hom (ideal_loc X Z' γ' j)) =
      loc_to_Clos C (fun j => Ideal.map (Spec.preimage k'').hom (ideal_loc X Z'' γ'' j)) := by
  letI : Algebra (Z'.cov.obj γ') C := RingHom.toAlgebra (Spec.preimage k').hom
  letI : Algebra (Z''.cov.obj γ'') C := RingHom.toAlgebra (Spec.preimage k'').hom
  have halg' : (Spec.preimage k').hom = algebraMap (Z'.cov.obj γ') C := rfl
  have halg'' : (Spec.preimage k'').hom = algebraMap (Z''.cov.obj γ'') C := rfl
  have hk' : (Spec C ↘ Spec (Z'.cov.obj γ')) = k' := Spec.map_preimage k'
  have hk'' : (Spec C ↘ Spec (Z''.cov.obj γ'')) = k'' := Spec.map_preimage k''
  rw [halg', halg'', loc_to_Clos_baseChange (Z'.cov.obj γ') C (ideal_loc X Z' γ'),
    loc_to_Clos_baseChange (Z''.cov.obj γ'') C (ideal_loc X Z'' γ''), hk', hk'',
    loc_to_Clos_chart X Z' γ', loc_to_Clos_chart X Z'' γ'', ← pullback_assoc, ← pullback_assoc,
    hmap, eq]

lemma BlGlob_chart_iso (Z : PreClos X)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (γ : Z.cov.J) (C : CommRingCat) (k : Spec C ⟶ Spec (Z.cov.obj γ)) [IsOpenImmersion k] :
    ∃! (e : pullback ((BlGlob Z) ↘ X) (k ≫ Z.cov.map γ) ≅
        BlMu (fun j => Ideal.map (Spec.preimage k).hom (ideal_loc X Z γ j))),
      Scheme.Hom.IsOver e.hom (Spec C) := by
  set σ := (BlGlob Z) ↘ X with hσ
  set e0 := Proj_loc_pullback_over Z γ with he0
  have h0 : e0.hom ≫ pullback.snd σ (Z.cov.map γ) =
      (Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ) := Proj_loc_pullback_over_hom_snd Z γ
  have h0' : e0.inv ≫ ((Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ)) =
      pullback.snd σ (Z.cov.map γ) := by rw [← h0, Iso.inv_hom_id_assoc]

  set E2 : pullback ((Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ)) k ≅
      pullback (pullback.snd σ (Z.cov.map γ)) k :=
    { hom := restrictRaw _ _ e0.hom h0 k
      inv := restrictRaw _ _ e0.inv h0' k
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, restrictRaw_fst, restrictRaw_fst_assoc,
            e0.hom_inv_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, restrictRaw_snd, restrictRaw_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, restrictRaw_fst, restrictRaw_fst_assoc,
            e0.inv_hom_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, restrictRaw_snd, restrictRaw_snd, Category.id_comp] }
    with hE2

  set E1 := pullbackSndCompIso σ (Z.cov.map γ) k with hE1
  have hE1over : Scheme.Hom.IsOver E1.hom (Spec C) := by
    rw [Scheme.Hom.isOver_iff]
    show E1.hom ≫ pullback.snd (pullback.snd σ (Z.cov.map γ)) k = pullback.snd σ (k ≫ Z.cov.map γ)
    exact pullbackSndCompIso_hom_snd σ (Z.cov.map γ) k

  have hE2inv_snd : E2.inv ≫ pullback.snd ((Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ)) k =
      pullback.snd (pullback.snd σ (Z.cov.map γ)) k := by
    rw [hE2]
    exact restrictRaw_snd (pullback.snd σ (Z.cov.map γ))
      ((Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ)) e0.inv h0' k
  have hE1_snd : E1.hom ≫ pullback.snd (pullback.snd σ (Z.cov.map γ)) k =
      pullback.snd σ (k ≫ Z.cov.map γ) := pullbackSndCompIso_hom_snd σ (Z.cov.map γ) k
  refine existsUnique_iso_transport (E1 ≪≫ E2.symm) ⟨?_⟩ (Proj_loc_pair_open_chart X Z γ C k)
  show (E1.hom ≫ E2.inv) ≫ pullback.snd ((Proj_loc X Z γ) ↘ Spec (Z.cov.obj γ)) k =
    pullback.snd σ (k ≫ Z.cov.map γ)
  rw [Category.assoc, hE2inv_snd, hE1_snd]

lemma ProjBlowup_iso_of_centre_eq' {ι' : Type} [DecidableEq ι']
    [(i : ι' →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι'))]
    [Fintype ι] [Fintype ι'] (C : CommRingCat) (L : ι → Ideal C) (L' : ι' → Ideal C)
    (h : loc_to_Clos C L = loc_to_Clos C L') :
    ∃! (e : BlMu L ≅ BlMu L'), Scheme.Hom.IsOver e.hom (Spec C) := by
  have condL : IsCars _ (pullback_Clos (BlMu L ↘ Spec C) (loc_to_Clos C L')) := by
    rw [← h]; exact blowups_Cars C L
  have condL' : IsCars _ (pullback_Clos (BlMu L' ↘ Spec C) (loc_to_Clos C L)) := by
    rw [h]; exact blowups_Cars C L'
  obtain ⟨φ, hφ, hφuniq⟩ := ProjBlowup_UnivProp_affine C L' condL
  obtain ⟨ψ, hψ, hψuniq⟩ := ProjBlowup_UnivProp_affine C L condL'
  refine ⟨⟨φ, ψ, ?_, ?_⟩, ⟨?_⟩, ?_⟩
  · exact ProjBlowup_UnivProp_unicity_affine C L (blowups_Cars C L) _ _
      ⟨by rw [Category.assoc, hψ.comp_over]; exact hφ.comp_over⟩ ⟨rfl⟩
  · exact ProjBlowup_UnivProp_unicity_affine C L' (blowups_Cars C L') _ _
      ⟨by rw [Category.assoc, hφ.comp_over]; exact hψ.comp_over⟩ ⟨rfl⟩
  · exact hφ.1
  · intro e' he'
    ext1
    exact hφuniq e'.hom he'

noncomputable def jointPoint (Z' Z'' : PreClos X) (x : X) :
    ↑(pullback (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))) :=
  (Scheme.Pullback.exists_preimage_pullback (Z'.cov.covers x).choose (Z''.cov.covers x).choose
    (by rw [(Z'.cov.covers x).choose_spec, (Z''.cov.covers x).choose_spec])).choose

lemma jointPoint_fst (Z' Z'' : PreClos X) (x : X) :
    (Z'.cov.map (Z'.cov.f x)).base
      ((pullback.fst (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))).base
        (jointPoint Z' Z'' x)) = x :=
  (congrArg (Z'.cov.map (Z'.cov.f x)).base
    (Scheme.Pullback.exists_preimage_pullback (Z'.cov.covers x).choose (Z''.cov.covers x).choose
      (by rw [(Z'.cov.covers x).choose_spec,
        (Z''.cov.covers x).choose_spec])).choose_spec.1).trans (Z'.cov.covers x).choose_spec

lemma jointPoint_snd (Z' Z'' : PreClos X) (x : X) :
    (Z''.cov.map (Z''.cov.f x)).base
      ((pullback.snd (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))).base
        (jointPoint Z' Z'' x)) = x :=
  (congrArg (Z''.cov.map (Z''.cov.f x)).base
    (Scheme.Pullback.exists_preimage_pullback (Z'.cov.covers x).choose (Z''.cov.covers x).choose
      (by rw [(Z'.cov.covers x).choose_spec,
        (Z''.cov.covers x).choose_spec])).choose_spec.2).trans (Z''.cov.covers x).choose_spec

set_option maxHeartbeats 1000000 in
def joint_cov (Z' Z'' : PreClos X) : Scheme.AffineCover.{u+1, u+1} (P := @IsOpenImmersion) X where
  J := Σ (γ' : Z'.cov.J) (γ'' : Z''.cov.J),
    (pullback (Z'.cov.map γ') (Z''.cov.map γ'')).affineOpenCover.J
  obj p := (pullback (Z'.cov.map p.1) (Z''.cov.map p.2.1)).affineOpenCover.obj p.2.2
  map p := (pullback (Z'.cov.map p.1) (Z''.cov.map p.2.1)).affineOpenCover.map p.2.2 ≫
    pullback.fst (Z'.cov.map p.1) (Z''.cov.map p.2.1) ≫ Z'.cov.map p.1
  f x := ⟨Z'.cov.f x, Z''.cov.f x,
    (pullback (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))).affineOpenCover.f
      (jointPoint Z' Z'' x)⟩
  covers x := by
    obtain ⟨y, hy⟩ :=
      (pullback (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))).affineOpenCover.covers
        (jointPoint Z' Z'' x)
    refine ⟨y, ?_⟩
    show ((pullback (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x))).affineOpenCover.map _ ≫
      pullback.fst (Z'.cov.map (Z'.cov.f x)) (Z''.cov.map (Z''.cov.f x)) ≫
      Z'.cov.map (Z'.cov.f x)).base y = x
    rw [Scheme.comp_base_apply, Scheme.comp_base_apply, hy]
    exact jointPoint_fst Z' Z'' x
  map_prop p := by
    haveI h1 := Z'.cov.map_prop p.1
    haveI h2 := Z''.cov.map_prop p.2.1
    haveI h3 := (pullback (Z'.cov.map p.1) (Z''.cov.map p.2.1)).affineOpenCover.map_prop p.2.2
    haveI h4 : IsOpenImmersion (pullback.fst (Z'.cov.map p.1) (Z''.cov.map p.2.1)) :=
      inferInstance
    haveI h5 : IsOpenImmersion
        (pullback.fst (Z'.cov.map p.1) (Z''.cov.map p.2.1) ≫ Z'.cov.map p.1) :=
      IsOpenImmersion.comp _ _
    exact IsOpenImmersion.comp _ _

set_option maxHeartbeats 1000000 in

lemma BlGlob_local_iso (Z' Z'' : PreClos X) (eq : Quotient.mk' Z' = Quotient.mk' Z'')
    [DecidableEq Z'.indnumb] [Fintype Z'.indnumb]
    [DecidableEq Z''.indnumb] [Fintype Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (γ' : Z'.cov.J) (γ'' : Z''.cov.J) (C : CommRingCat)
    (k' : Spec C ⟶ Spec (Z'.cov.obj γ')) (k'' : Spec C ⟶ Spec (Z''.cov.obj γ''))
    [IsOpenImmersion k'] [IsOpenImmersion k'']
    (hmap : k' ≫ Z'.cov.map γ' = k'' ≫ Z''.cov.map γ'') :
    ∃! (e : pullback ((BlGlob Z') ↘ X) (k' ≫ Z'.cov.map γ') ≅
        pullback ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ')),
      Scheme.Hom.IsOver e.hom (Spec C) := by
  have hcen := centres_eq_of_rel Z' Z'' eq γ' γ'' C k' k'' hmap
  have e0 := ProjBlowup_iso_of_centre_eq' C
    (fun j => Ideal.map (Spec.preimage k').hom (ideal_loc X Z' γ' j))
    (fun j => Ideal.map (Spec.preimage k'').hom (ideal_loc X Z'' γ'' j)) hcen
  letI : (pullback ((BlGlob Z') ↘ X) (k' ≫ Z'.cov.map γ')).Over (Spec C) :=
    ⟨pullback.snd ((BlGlob Z') ↘ X) (k' ≫ Z'.cov.map γ')⟩
  letI : (pullback ((BlGlob Z'') ↘ X) (k'' ≫ Z''.cov.map γ'')).Over (Spec C) :=
    ⟨pullback.snd ((BlGlob Z'') ↘ X) (k'' ≫ Z''.cov.map γ'')⟩
  letI : (pullback ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ')).Over (Spec C) :=
    ⟨pullback.snd ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ')⟩
  have e1 := BlGlob_chart_iso Z' γ' C k'
  have e2 := BlGlob_chart_iso Z'' γ'' C k''
  have he2inv : Scheme.Hom.IsOver e2.choose.inv (Spec C) :=
    Iso.inv_isOver_of_isOver e2.choose e2.choose_spec.1

  set castCongr : pullback ((BlGlob Z'') ↘ X) (k'' ≫ Z''.cov.map γ'') ≅
      pullback ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ') :=
    pullback.congrHom rfl hmap.symm with hcastCongr
  have hcastCongr_snd : castCongr.hom ≫ pullback.snd ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ') =
      pullback.snd ((BlGlob Z'') ↘ X) (k'' ≫ Z''.cov.map γ'') := by
    rw [hcastCongr]; simp
  have hcastCongr_over : Scheme.Hom.IsOver castCongr.hom (Spec C) := ⟨hcastCongr_snd⟩
  exact existsUnique_iso_transport_target castCongr hcastCongr_over
    (existsUnique_iso_transport_target e2.choose.symm he2inv
      (existsUnique_iso_transport e1.choose e1.choose_spec.1 e0))

set_option maxHeartbeats 1000000 in

lemma joint_local_iso (Z' Z'' : PreClos X) (eq : Quotient.mk' Z' = Quotient.mk' Z'')
    [DecidableEq Z'.indnumb] [Fintype Z'.indnumb]
    [DecidableEq Z''.indnumb] [Fintype Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (p : (joint_cov Z' Z'').J) :
    ∃! (e : pullback ((BlGlob Z') ↘ X) ((joint_cov Z' Z'').map p) ≅
        pullback ((BlGlob Z'') ↘ X) ((joint_cov Z' Z'').map p)),
      Scheme.Hom.IsOver e.hom (Spec ((joint_cov Z' Z'').obj p)) := by
  obtain ⟨γ', γ'', w⟩ := p
  set b := (pullback (Z'.cov.map γ') (Z''.cov.map γ'')).affineOpenCover.map w with hb
  set k' := b ≫ pullback.fst (Z'.cov.map γ') (Z''.cov.map γ'') with hk'
  set k'' := b ≫ pullback.snd (Z'.cov.map γ') (Z''.cov.map γ'') with hk''
  haveI : IsOpenImmersion (Z'.cov.map γ') := Z'.cov.map_prop γ'
  haveI : IsOpenImmersion (Z''.cov.map γ'') := Z''.cov.map_prop γ''
  haveI : IsOpenImmersion b :=
    (pullback (Z'.cov.map γ') (Z''.cov.map γ'')).affineOpenCover.map_prop w
  haveI hk'open : IsOpenImmersion k' := IsOpenImmersion.comp _ _
  haveI hk''open : IsOpenImmersion k'' := IsOpenImmersion.comp _ _
  have hmap : k' ≫ Z'.cov.map γ' = k'' ≫ Z''.cov.map γ'' := by
    rw [hk', hk'', Category.assoc, Category.assoc, pullback.condition]
  have hkeq : (joint_cov Z' Z'').map ⟨γ', γ'', w⟩ = k' ≫ Z'.cov.map γ' := by
    show b ≫ pullback.fst (Z'.cov.map γ') (Z''.cov.map γ'') ≫ Z'.cov.map γ' = _
    rw [hk', Category.assoc]
  show ∃! (e : pullback ((BlGlob Z') ↘ X) (k' ≫ Z'.cov.map γ') ≅
      pullback ((BlGlob Z'') ↘ X) (k' ≫ Z'.cov.map γ')), _
  exact BlGlob_local_iso Z' Z'' eq γ' γ'' _ k' k'' hmap

@[reassoc]
lemma PreBlGlob_ι_over (Z : PreClos X)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    (γ : Z.cov.J) :
    (PreBlGlob Z).ι γ ≫ ((BlGlob Z) ↘ X) = (Proj_loc X Z γ) ↘ X := by
  show (PreBlGlob Z).ι γ ≫ Multicoequalizer.desc _ _ (fun γ => Proj_loc X Z γ ↘ X) _ = _
  exact Multicoequalizer.π_desc _ _ _ _ _

def pullbackCongrIsoLeft {P Q R S : Scheme} (e : P ≅ Q) {q : Q ⟶ R} {f : P ⟶ R}
    (h : e.hom ≫ q = f) (m : S ⟶ R) : pullback f m ≅ pullback q m where
  hom := pullback.lift (pullback.fst f m ≫ e.hom) (pullback.snd f m)
    (by rw [Category.assoc, h]; exact pullback.condition)
  inv := pullback.lift (pullback.fst q m ≫ e.inv) (pullback.snd q m)
    (by rw [Category.assoc, ← h, e.inv_hom_id_assoc]; exact pullback.condition)
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma pullbackCongrIsoLeft_hom_snd {P Q R S : Scheme} (e : P ≅ Q) {q : Q ⟶ R} {f : P ⟶ R}
    (h : e.hom ≫ q = f) (m : S ⟶ R) :
    (pullbackCongrIsoLeft e h m).hom ≫ pullback.snd q m = pullback.snd f m :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma pullback_congrHom_hom_snd {P Q R : Scheme} {f₁ f₂ : P ⟶ R} {g₁ g₂ : Q ⟶ R}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst h₁; subst h₂; simp

def BlGlobAffineCover (Z : PreClos X)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.AffineCover (P := @IsOpenImmersion) (BlGlob Z) where
  J := (γ : Z.cov.J) × (BlMuAffineCover (Z.cov.obj γ) (ideal_loc X Z γ)).J
  obj p := (BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).obj p.2
  map p := (BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2 ≫ (PreBlGlob Z).ι p.1
  f x := ⟨((PreBlGlob Z).ι_jointly_surjective x).choose,
    (BlMuAffineCover (Z.cov.obj ((PreBlGlob Z).ι_jointly_surjective x).choose)
        (ideal_loc X Z ((PreBlGlob Z).ι_jointly_surjective x).choose)).f
      ((PreBlGlob Z).ι_jointly_surjective x).choose_spec.choose⟩
  covers x := by
    obtain ⟨z, hz⟩ :=
      (BlMuAffineCover (Z.cov.obj ((PreBlGlob Z).ι_jointly_surjective x).choose)
        (ideal_loc X Z ((PreBlGlob Z).ι_jointly_surjective x).choose)).covers
        ((PreBlGlob Z).ι_jointly_surjective x).choose_spec.choose
    refine ⟨z, ?_⟩
    rw [Scheme.comp_base_apply, hz]
    exact ((PreBlGlob Z).ι_jointly_surjective x).choose_spec.choose_spec
  map_prop p := by
    haveI : IsOpenImmersion ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2) :=
      (BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map_prop p.2
    haveI : IsOpenImmersion ((PreBlGlob Z).ι p.1) := inferInstance
    exact IsOpenImmersion.comp _ _

set_option maxHeartbeats 1600000 in

def BlGlobPreClos (Z : PreClos X)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    PreClos (BlGlob Z) where
  indnumb := Z.indnumb
  subscheme i := pullback (Z.subscheme i ↘ X) ((BlGlob Z) ↘ X)
  over i := ⟨pullback.snd _ _⟩
  cov := BlGlobAffineCover Z
  ideal i p := (BlMuPreClos (Z.cov.obj p.1) (ideal_loc X Z p.1)).ideal i p.2
  condiso i p :=
    (BlMuPreClos (Z.cov.obj p.1) (ideal_loc X Z p.1)).condiso i p.2 ≪≫
      pullbackLeftPullbackSndIso
        ((loc_to_PreClos (Z.cov.obj p.1) (ideal_loc X Z p.1)).subscheme i ↘ Spec (Z.cov.obj p.1))
        (Proj_loc X Z p.1 ↘ Spec (Z.cov.obj p.1))
        ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2) ≪≫

      pullbackCongrIsoLeft (Z.condiso i p.1)
        (show (Z.condiso i p.1).hom ≫ pullback.snd (Z.subscheme i ↘ X) (Z.cov.map p.1) =
              (loc_to_PreClos (Z.cov.obj p.1) (ideal_loc X Z p.1)).subscheme i ↘
                Spec (Z.cov.obj p.1)
          from (Z.condover i p.1).1)
        ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2 ≫
          (Proj_loc X Z p.1 ↘ Spec (Z.cov.obj p.1))) ≪≫
      pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) (Z.cov.map p.1)
        ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2 ≫
          (Proj_loc X Z p.1 ↘ Spec (Z.cov.obj p.1))) ≪≫
      pullback.congrHom rfl (by

        show (BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2 ≫
              ((Proj_loc X Z p.1) ↘ X) =
            ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2 ≫
              (PreBlGlob Z).ι p.1) ≫ ((BlGlob Z) ↘ X)
        rw [Category.assoc ((BlMuAffineCover (Z.cov.obj p.1) (ideal_loc X Z p.1)).map p.2)
          ((PreBlGlob Z).ι p.1) ((BlGlob Z) ↘ X), PreBlGlob_ι_over Z p.1]) ≪≫
      (pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) ((BlGlob Z) ↘ X)
        ((BlGlobAffineCover Z).map p)).symm
  condover i p := by
    have hM := ((BlMuPreClos (Z.cov.obj p.1) (ideal_loc X Z p.1)).condover i p.2)
    rw [Scheme.Hom.isOver_iff] at hM ⊢

    show _ ≫ pullback.snd (pullback.snd (Z.subscheme i ↘ X) ((BlGlob Z) ↘ X))
        ((BlGlobAffineCover Z).map p) = _

    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd, pullback_congrHom_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd, pullbackCongrIsoLeft_hom_snd]
    exact hM

lemma BlGlob_IsCars (Z : PreClos X)
    [DecidableEq Z.indnumb] [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    IsCars _ (pullback_Clos ((BlGlob Z) ↘ X) (Quotient.mk'' Z)) := by
  refine ⟨⟨BlGlobPreClos Z, ?_, ?_⟩⟩
  · exact ⟨⟨fun i p => (BlMuPreClos_IsPreCars (Z.cov.obj p.1) (ideal_loc X Z p.1)).prin i p.2⟩,
      fun i p => (BlMuPreClos_IsPreCars (Z.cov.obj p.1) (ideal_loc X Z p.1)).nonzerodiv i p.2⟩
  · exact Quotient.sound
      ⟨{ indnumb_equiv := Equiv.refl _
         subscheme_iso := fun i => Iso.refl _
         subscheme_iso_over := fun i => by simp [Scheme.Hom.isOver_iff] }⟩

lemma PreProjBlowup_rel (Z' Z'' : PreClos X) (eq: Quotient.mk' Z' = Quotient.mk' Z'')
    {T : Scheme} [T.Over X]
    [DecidableEq Z'.indnumb]
    [Fintype Z'.indnumb]
    [Fintype Z''.indnumb]
    [DecidableEq Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z') :
  ∃! (e : BlGlob Z' ≅ BlGlob Z''), Scheme.Hom.IsOver e.hom X := by

  have heq : (Quotient.mk'' Z' : Clos X) = Quotient.mk'' Z'' := eq

  have h' : IsCars _ (pullback_Clos ((BlGlob Z') ↘ X) (Quotient.mk'' Z')) := BlGlob_IsCars Z'
  have h'' : IsCars _ (pullback_Clos ((BlGlob Z'') ↘ X) (Quotient.mk'' Z'')) := BlGlob_IsCars Z''
  have hc' : IsCars _ (pullback_Clos ((BlGlob Z') ↘ X) (Quotient.mk'' Z'')) := by
    rw [← heq]; exact h'
  have hc'' : IsCars _ (pullback_Clos ((BlGlob Z'') ↘ X) (Quotient.mk'' Z')) := by
    rw [heq]; exact h''
  obtain ⟨φ, hφ⟩ := PreProjBlowup_UnivProp_existence_Cars Z'' (T := BlGlob Z') hc'
  obtain ⟨ψ, hψ⟩ := PreProjBlowup_UnivProp_existence_Cars Z' (T := BlGlob Z'') hc''
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ, ?_⟩
  · exact PreProjBlowup_UnivProp_unicity_Cars Z' h' _ _
      ⟨by rw [Category.assoc, hψ.comp_over]; exact hφ.comp_over⟩ ⟨rfl⟩
  · exact PreProjBlowup_UnivProp_unicity_Cars Z'' h'' _ _
      ⟨by rw [Category.assoc, hφ.comp_over]; exact hψ.comp_over⟩ ⟨rfl⟩
  · intro e' he'
    ext1
    exact PreProjBlowup_UnivProp_unicity_Cars Z'' hc' _ _ he' hφ

noncomputable def GlobalBlowup (Z : Clos X) [DecidableEq Z.out.indnumb] [Fintype Z.out.indnumb]
    [(i : Z.out.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.out.indnumb))] : Scheme :=
  BlGlob Z.out

noncomputable instance GlobalBlowup.over (Z : Clos X) [DecidableEq Z.out.indnumb]
    [Fintype Z.out.indnumb]
    [(i : Z.out.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.out.indnumb))] :
    Scheme.Over (GlobalBlowup Z) X :=
  inferInstanceAs (Scheme.Over (BlGlob Z.out) X)

theorem GlobalBlowup_UnivProp (Z : Clos X) [DecidableEq Z.out.indnumb] [Fintype Z.out.indnumb]
    [(i : Z.out.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.out.indnumb))]
    {T : Scheme} [T.Over X]
    (cond : IsCars _ <| pullback_Clos (T ↘ X) Z) :
    ∃! φ : T ⟶ GlobalBlowup Z, Scheme.Hom.IsOver φ X := by
  have hcond : IsCars _ <| pullback_Clos (T ↘ X) (Quotient.mk'' Z.out) := by
    rwa [Quotient.out_eq']
  obtain ⟨φ, hφ⟩ := PreProjBlowup_UnivProp_existence_Cars Z.out hcond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact (PreProjBlowup_UnivProp_unicity_Cars Z.out hcond φ φ' hφ hφ').symm
