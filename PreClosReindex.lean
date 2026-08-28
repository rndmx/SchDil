import PreClosClosedImmersion

/-!
# Change of covering for the ideals of a closed-subscheme datum

`chartIdeal_agree_rel` compares the ideals of two `PreClos` representatives on a common
affine `W` mapping to a chart of each. Taking `W` to be *the chart itself* and both maps
the identity gives the change-of-covering statement: the ideals of a `PreClos` on a given
covering are determined by its class in `Clos`, so any two representatives agree there.

This is locality-free -- the ideal of a closed subscheme on an affine chart is read off the
closed immersion (`PreClos.reindexIdeal`), not glued from smaller pieces.

A closed-subscheme datum is therefore determined by its ideals on a covering
(`PreClos.clos_eq_of_ideal_eq`): the chart-wise comparison isomorphisms glue, and the
cocycle condition is free because a closed immersion is a monomorphism, so any two
morphisms over the base agree.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

theorem PreClos.ideal_eq_reindexIdeal (Z₁ Z₂ : PreClos X) (R : relStructure Z₁ Z₂)
    (γ : Z₁.cov.J) (i : Z₁.indnumb) :
    Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (R.indnumb_equiv i) γ := by
  have key := chartIdeal_agree_rel Z₁ (Z₂.reindex Z₁.cov)
    ({ indnumb_equiv := R.indnumb_equiv
       subscheme_iso := R.subscheme_iso
       subscheme_iso_over := R.subscheme_iso_over } : relStructure Z₁ (Z₂.reindex Z₁.cov))
    (W := Spec (Z₁.cov.obj γ)) (γ₁ := γ) (γ₂ := γ) (𝟙 _) (𝟙 _) rfl i
  set u : Spec Γ(Spec (Z₁.cov.obj γ), ⊤) ⟶ Spec (Z₁.cov.obj γ) :=
    (Spec (Z₁.cov.obj γ)).isoSpec.inv ≫ 𝟙 _ with hu
  haveI : IsIso u := by rw [hu]; infer_instance
  set φ := Spec.preimage u with hφ
  haveI : IsIso φ := by
    refine ⟨Spec.preimage (inv u), ?_, ?_⟩
    · apply Spec.map_injective
      rw [Spec.map_comp, hφ, Spec.map_preimage, Spec.map_preimage, Spec.map_id,
        IsIso.inv_hom_id]
    · apply Spec.map_injective
      rw [Spec.map_comp, hφ, Spec.map_preimage, Spec.map_preimage, Spec.map_id,
        IsIso.hom_inv_id]
  have hbij : Function.Bijective φ.hom := ConcreteCategory.bijective_of_isIso φ
  have h1 := Ideal.comap_mono (f := φ.hom) key.le
  have h2 := Ideal.comap_mono (f := φ.hom) key.ge
  rw [Ideal.comap_map_of_bijective φ.hom hbij, Ideal.comap_map_of_bijective φ.hom hbij] at h1 h2
  exact le_antisymm h1 h2

lemma quot_eqToIso_comp {R : CommRingCat.{u+1}} {I J : Ideal R} (hIJ : I = J) :
    (eqToIso (by rw [hIJ]) :
        Spec (CommRingCat.of (R ⧸ I)) ≅ Spec (CommRingCat.of (R ⧸ J))).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  subst hIJ; simp

namespace PreClos

/-- Chart-wise comparison of two closed-subscheme data with the same ideals. -/
noncomputable def chartCompareIdeal (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ)
    (i : Z₁.indnumb) (γ : Z₁.cov.J) :
    pullback (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) ≅
      pullback (Z₂.subscheme (e i) ↘ X) (Z₁.cov.map γ) :=
  (Z₁.condiso i γ).symm ≪≫ eqToIso (by rw [h i γ]) ≪≫ (Z₂.reindexIso Z₁.cov (e i) γ).symm

/-- The comparison is a morphism over the chart. -/
lemma chartCompareIdeal_snd (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ)
    (i : Z₁.indnumb) (γ : Z₁.cov.J) :
    (Z₁.chartCompareIdeal Z₂ e h i γ).hom ≫
        pullback.snd (Z₂.subscheme (e i) ↘ X) (Z₁.cov.map γ) =
      pullback.snd (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) := by
  have h1 : (Z₁.condiso i γ).hom ≫ pullback.snd (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z₁.ideal i γ))) := by
    have := Z₁.condover i γ
    rw [Scheme.Hom.isOver_iff] at this
    simpa [pullback_over_right, spec_quotient_ideal_over_eq] using this
  have h2 := Z₂.reindexIso_eq Z₁.cov (e i) γ
  simp only [chartCompareIdeal, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [h2, ← Category.assoc ((Z₂.reindexIso Z₁.cov (e i) γ)).inv, Iso.inv_hom_id,
    Category.id_comp, quot_eqToIso_comp (h i γ), ← h1, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end PreClos

namespace PreClos

/-- Glue the chart-wise comparisons into a morphism of subschemes. -/
noncomputable def compareHom (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) (i : Z₁.indnumb) :
    Z₁.subscheme i ⟶ Z₂.subscheme (e i) :=
  ((Z₁.cov.cover).pullbackCover (Z₁.subscheme i ↘ X)).glueMorphisms
    (fun γ => (Z₁.chartCompareIdeal Z₂ e h i γ).hom ≫
      pullback.fst (Z₂.subscheme (e i) ↘ X) (Z₁.cov.map γ))
    (by
      intro γ δ
      haveI := Z₂.subscheme_isClosedImmersion (e i)
      haveI : Mono (Z₂.subscheme (e i) ↘ X) := inferInstance
      rw [← cancel_mono (Z₂.subscheme (e i) ↘ X)]
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc ((Z₁.chartCompareIdeal Z₂ e h i γ).hom),
        Z₁.chartCompareIdeal_snd Z₂ e h i γ,
        ← Category.assoc ((Z₁.chartCompareIdeal Z₂ e h i δ).hom),
        Z₁.chartCompareIdeal_snd Z₂ e h i δ]
      have hc : pullback.fst ((Z₁.cov.cover.pullbackCover (Z₁.subscheme i ↘ X)).map γ)
            ((Z₁.cov.cover.pullbackCover (Z₁.subscheme i ↘ X)).map δ) ≫
          pullback.fst (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) =
          pullback.snd _ _ ≫ pullback.fst (Z₁.subscheme i ↘ X) (Z₁.cov.map δ) :=
        pullback.condition
      have e1 : pullback.snd (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) ≫ Z₁.cov.map γ =
          pullback.fst (Z₁.subscheme i ↘ X) (Z₁.cov.map γ) ≫ (Z₁.subscheme i ↘ X) :=
        pullback.condition.symm
      have e2 : pullback.snd (Z₁.subscheme i ↘ X) (Z₁.cov.map δ) ≫ Z₁.cov.map δ =
          pullback.fst (Z₁.subscheme i ↘ X) (Z₁.cov.map δ) ≫ (Z₁.subscheme i ↘ X) :=
        pullback.condition.symm
      rw [e1, e2, ← Category.assoc, ← Category.assoc, hc])

lemma compareHom_over (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) (i : Z₁.indnumb) :
    Z₁.compareHom Z₂ e h i ≫ (Z₂.subscheme (e i) ↘ X) = (Z₁.subscheme i ↘ X) := by
  refine ((Z₁.cov.cover).pullbackCover (Z₁.subscheme i ↘ X)).hom_ext _ _ (fun γ => ?_)
  rw [← Category.assoc, compareHom, Scheme.Cover.ι_glueMorphisms]
  simp only [Category.assoc, pullback.condition]
  rw [← Category.assoc ((Z₁.chartCompareIdeal Z₂ e h i γ).hom),
    Z₁.chartCompareIdeal_snd Z₂ e h i γ, ← pullback.condition]
  rfl

end PreClos

namespace PreClos

lemma reindexIdeal_self (Z : PreClos X) (i : Z.indnumb) (γ : Z.cov.J) :
    Z.reindexIdeal Z.cov i γ = Z.ideal i γ :=
  (Z.ideal_eq_reindexIdeal Z (relStructure.refl Z) γ i).symm

lemma reindex_symm_hyp (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ)
    (j : Z₂.indnumb) (γ : Z₁.cov.J) :
    (Z₂.reindex Z₁.cov).ideal j γ =
      Z₁.reindexIdeal (Z₂.reindex Z₁.cov).cov (e.symm j) γ := by
  show Z₂.reindexIdeal Z₁.cov j γ = Z₁.reindexIdeal Z₁.cov (e.symm j) γ
  rw [Z₁.reindexIdeal_self (e.symm j) γ, h (e.symm j) γ, Equiv.apply_symm_apply]

/-- The inverse comparison morphism. -/
noncomputable def compareInv (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) (i : Z₁.indnumb) :
    Z₂.subscheme (e i) ⟶ Z₁.subscheme i :=
  (Z₂.reindex Z₁.cov).compareHom Z₁ e.symm (reindex_symm_hyp Z₁ Z₂ e h) (e i) ≫
    eqToHom (congrArg Z₁.subscheme (Equiv.symm_apply_apply e i))

lemma compareInv_over (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) (i : Z₁.indnumb) :
    compareInv Z₁ Z₂ e h i ≫ (Z₁.subscheme i ↘ X) = (Z₂.subscheme (e i) ↘ X) := by
  have h1 := (Z₂.reindex Z₁.cov).compareHom_over Z₁ e.symm (reindex_symm_hyp Z₁ Z₂ e h) (e i)
  have h2 := Z₁.index_eq_triangle (e.symm (e i)) i (Equiv.symm_apply_apply e i)
  rw [Scheme.Hom.isOver_iff] at h2
  rw [compareInv, Category.assoc, h2]
  exact h1

/-- **A closed-subscheme datum is determined by its ideals on a covering.** -/
noncomputable def relStructure_of_ideal_eq (Z₁ Z₂ : PreClos X)
    (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) : relStructure Z₁ Z₂ where
  indnumb_equiv := e
  subscheme_iso i :=
    { hom := Z₁.compareHom Z₂ e h i
      inv := compareInv Z₁ Z₂ e h i
      hom_inv_id := by
        haveI := Z₁.subscheme_isClosedImmersion i
        rw [← cancel_mono (Z₁.subscheme i ↘ X), Category.assoc,
          compareInv_over Z₁ Z₂ e h i, Z₁.compareHom_over Z₂ e h i, Category.id_comp]
      inv_hom_id := by
        haveI := Z₂.subscheme_isClosedImmersion (e i)
        rw [← cancel_mono (Z₂.subscheme (e i) ↘ X), Category.assoc,
          Z₁.compareHom_over Z₂ e h i, compareInv_over Z₁ Z₂ e h i, Category.id_comp] }
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]; exact Z₁.compareHom_over Z₂ e h i

theorem clos_eq_of_ideal_eq (Z₁ Z₂ : PreClos X) (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) :
    (Quotient.mk'' Z₁ : Clos X) = Quotient.mk'' Z₂ :=
  Quotient.sound ⟨relStructure_of_ideal_eq Z₁ Z₂ e h⟩

end PreClos
