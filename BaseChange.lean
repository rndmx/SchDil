import Functoriality

/-!
# Base change of dilatations: [Ma24, §3.7]

For `f : X' ⟶ X` and a multicenter `M` on `X`, the preimage multicenter is
`M.baseChange f`, and §3.6 provides the canonical morphism (3.4)

  `baseChangeCompare : Bl_{Y'}^{D'} X' ⟶ Bl_Y^D X ×_X X'`

(the functoriality morphism for `RD := relStructure.refl` — the base-change divisors are
*definitionally* the pulled-back ones — paired with the structure map).

* **Lemma 3.36** (`baseChangeIso`): if the fiber product is `D'`-regular (`hcars`), then
  (3.4) is an isomorphism. The reverse morphism is the universal property of
  `M.baseChange f` applied to the fiber product; its `pullSubset` input
  (`baseChange_pullSubset_snd`) routes the containment through `pullback.fst` and the
  exceptional-divisor equality on `Bl` (`structureMapInterRel`), with the two legs of the
  fiber product exchanged by `pullback_Pre_congr` — a `relStructure` along an equality of
  morphisms whose index equivalence is *definitionally* the identity, so that all
  composite equivalences reduce by `rfl`.
* **Corollary 3.37** (`flatBaseChangeIso`, `baseChangeHom_flat`,
  `baseChangeHom_property`): for flat `f` the hypothesis holds automatically
  (`pullback_IsCars` along the flat projection), so `Bl' ≅ Bl ×_X X'`, and the canonical
  morphism `Bl' ⟶ Bl` is flat — more generally it inherits any property of `f` stable
  under base change and respecting isomorphisms.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X X' : Scheme.{u+1}} (M : PreMultiCenter X) (f : X' ⟶ X)

-- (b) congr-rel
def pullback_Pre_congr {T : Scheme.{u+1}} {g g' : T ⟶ X} (hg : g = g') (Z : PreClos X) :
    _root_.relStructure (pullback_PreClos X T g Z) (pullback_PreClos X T g' Z) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso i := eqToIso (by subst hg; rfl)
  subscheme_iso_over i := by
    subst hg
    simp [Scheme.Hom.isOver_iff]

@[simp] theorem pullback_Pre_congr_equiv {T : Scheme.{u+1}} {g g' : T ⟶ X}
    (hg : g = g') (Z : PreClos X) (i : Z.indnumb) :
    (pullback_Pre_congr hg Z).indnumb_equiv i = i := rfl

@[simp] theorem relStructure_trans_equiv {Z₁ Z₂ Z₃ : PreClos X}
    (R : _root_.relStructure Z₁ Z₂) (R' : _root_.relStructure Z₂ Z₃) :
    (R.trans R').indnumb_equiv = R.indnumb_equiv.trans R'.indnumb_equiv := rfl

@[simp] theorem relStructure_symm_equiv {Z₁ Z₂ : PreClos X}
    (R : _root_.relStructure Z₁ Z₂) :
    (R.symm).indnumb_equiv = R.indnumb_equiv.symm := rfl

@[simp] theorem pullback_lem_equiv {Z Z' : PreClos X} (T : Scheme.{u+1}) (g : T ⟶ X)
    (e : _root_.relStructure Z Z') :
    (pullback_lem X Z Z' T g e).indnumb_equiv = e.indnumb_equiv := rfl

@[simp] theorem relStructure_of_ideal_eq_equiv (Z₁ Z₂ : PreClos X)
    (e : Z₁.indnumb ≃ Z₂.indnumb)
    (h : ∀ i γ, Z₁.ideal i γ = Z₂.reindexIdeal Z₁.cov (e i) γ) :
    (PreClos.relStructure_of_ideal_eq Z₁ Z₂ e h).indnumb_equiv = e := rfl

@[simp] theorem pullback_Pre_assoc'_equiv (X'' X'a : Scheme.{u+1}) (f' : X'' ⟶ X'a)
    (g : X'a ⟶ X) (Z : PreClos X) :
    (pullback_Pre_assoc' X'' X'a f' g Z).indnumb_equiv = Equiv.refl _ := rfl

-- the content rel on Bl_M: pullback of Y∩D = pullback of D  ([Ma24, Prop. 3.16])
noncomputable def structureMapInterRel :
    _root_.relStructure
      (pullback_PreClos X M.dilatation M.structureMap
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb)))
      (pullback_PreClos X M.dilatation M.structureMap M.Drep) :=
  PreClos.relStructure_of_ideal_eq _ _ (Equiv.refl _) (fun i γβ => by
    have hself : (pullback_PreClos X M.dilatation M.structureMap M.Drep).reindexIdeal
        (pullback_PreClos X M.dilatation M.structureMap
          (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).cov i γβ =
        (pullback_PreClos X M.dilatation M.structureMap M.Drep).ideal i γβ :=
      PreClos.reindexIdeal_self
        (pullback_PreClos X M.dilatation M.structureMap M.Drep) i γβ
    have hmain : (pullback_PreClos X M.dilatation M.structureMap
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).ideal i γβ =
        (pullback_PreClos X M.dilatation M.structureMap M.Drep).ideal i γβ :=
      M.structureMap_pull_inter_ideal_eq_D i γβ
    exact hmain.trans hself.symm)

-- the free hY for the base-change datum
theorem baseChange_hY : ∀ (i : M.indnumb) (γ' : (M.baseChange f).cov.J),
    (pullback_PreClos X X' f M.Yrep).reindexIdeal (M.baseChange f).cov i γ' ≤
      (M.baseChange f).Yideal ((_root_.relStructure.refl
        (pullback_PreClos X X' f M.Drep)).indnumb_equiv i) γ' ⊔
      (M.baseChange f).Dideal ((_root_.relStructure.refl
        (pullback_PreClos X X' f M.Drep)).indnumb_equiv i) γ' :=
  fun i γ' => le_trans
    (le_of_eq (PreClos.reindexIdeal_self (pullback_PreClos X X' f M.Yrep) i γ'))
    le_sup_left

/-- The canonical morphism `Bl' ⟶ Bl` of [Ma24, §3.7]. -/
noncomputable def baseChangeHom : (M.baseChange f).dilatation ⟶ M.dilatation :=
  functorialityHom M (M.baseChange f) f (_root_.relStructure.refl _) (baseChange_hY M f)

theorem baseChangeHom_over :
    baseChangeHom M f ≫ M.structureMap = (M.baseChange f).structureMap ≫ f :=
  functorialityHom_over M (M.baseChange f) f (_root_.relStructure.refl _) (baseChange_hY M f)

/-- The canonical morphism (3.4): `Bl' ⟶ Bl ×_X X'`. -/
noncomputable def baseChangeCompare :
    (M.baseChange f).dilatation ⟶ pullback M.structureMap f :=
  pullback.lift (baseChangeHom M f) (M.baseChange f).structureMap (baseChangeHom_over M f)

/-- On the fiber product, the pullback of `Y ∩ D` along `snd ≫ f` agrees with the
pullback of `D`: route through `fst` and the exceptional divisor equality on `Bl`. -/
noncomputable def sndCompRel : _root_.relStructure
    (pullback_PreClos X (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) (M.Yrep.inter M.Drep (Equiv.refl M.indnumb)))
    (pullback_PreClos X (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) M.Drep) :=
  (pullback_Pre_congr pullback.condition.symm
      (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).trans
  ((pullback_Pre_assoc' (pullback M.structureMap f) M.dilatation
      (pullback.fst M.structureMap f) M.structureMap
      (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).trans
  ((pullback_lem M.dilatation _ _ (pullback M.structureMap f)
      (pullback.fst M.structureMap f) (structureMapInterRel M)).trans
  ((pullback_Pre_assoc' (pullback M.structureMap f) M.dilatation
      (pullback.fst M.structureMap f) M.structureMap M.Drep).symm.trans
  (pullback_Pre_congr pullback.condition M.Drep))))

theorem sndCompRel_equiv (i : M.indnumb) :
    (sndCompRel M f).indnumb_equiv i = i := rfl

/-- `M`'s containment condition holds on the fiber product over `X`. -/
theorem pullSubset_sndComp :
    M.pullSubset (pullback.snd M.structureMap f ≫ f) := by
  intro i γβ
  have key := PreClos.ideal_eq_reindexIdeal _ _ (sndCompRel M f) γβ i
  rw [sndCompRel_equiv M f i] at key
  have hself : (pullback_PreClos X (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f) M.Drep).reindexIdeal
      (pullback_PreClos X (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f)
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).cov i γβ =
      (pullback_PreClos X (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f) M.Drep).ideal i γβ :=
    PreClos.reindexIdeal_self (pullback_PreClos X (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) M.Drep) i γβ
  rw [hself] at key
  have hexp : M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1 =
      M.Yideal i γβ.1 ⊔ M.Drep.ideal i γβ.1 := by
    rw [M.Yrep.interIdeal_eq M.Drep (Equiv.refl M.indnumb) i γβ.1]
    congr 1
    exact PreClos.reindexIdeal_self M.Drep i γβ.1
  have key2 : Ideal.map (pull_mor_ring X M.Drep (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f) γβ).hom
        (M.Yideal i γβ.1 ⊔ M.Drep.ideal i γβ.1) =
      Ideal.map (pull_mor_ring X M.Drep (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f) γβ).hom (M.Drep.ideal i γβ.1) := by
    have hQ : (pullback_PreClos X (pullback M.structureMap f)
        (pullback.snd M.structureMap f ≫ f)
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).ideal i γβ =
        Ideal.map (pull_mor_ring X M.Drep (pullback M.structureMap f)
          (pullback.snd M.structureMap f ≫ f) γβ).hom
          (M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1) := rfl
    rw [← hexp]
    exact hQ.symm.trans key
  rw [Ideal.map_sup] at key2
  show Ideal.map (pull_mor_ring X M.Drep (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) γβ).hom (M.Yideal i γβ.1) ≤
    Ideal.map (pull_mor_ring X M.Drep (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) γβ).hom (M.Drep.ideal i γβ.1)
  exact le_trans le_sup_left key2.le

/-- The base-changed containment on the fiber product, over `X'`. -/
noncomputable def sndRel : _root_.relStructure
    (pullback_PreClos X' (pullback M.structureMap f) (pullback.snd M.structureMap f)
      ((M.baseChange f).Yrep.inter (M.baseChange f).Drep
        (Equiv.refl (M.baseChange f).indnumb)))
    (pullback_PreClos X' (pullback M.structureMap f) (pullback.snd M.structureMap f)
      (M.baseChange f).Drep) :=
  (pullback_lem X' _ _ (pullback M.structureMap f) (pullback.snd M.structureMap f)
      (inter_pullback_rel M.Yrep M.Drep (Equiv.refl M.indnumb) X' f).symm).trans
  ((pullback_Pre_assoc' (pullback M.structureMap f) X'
      (pullback.snd M.structureMap f) f
      (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).symm.trans
  ((sndCompRel M f).trans
  (pullback_Pre_assoc' (pullback M.structureMap f) X'
      (pullback.snd M.structureMap f) f M.Drep)))

theorem sndRel_equiv (i : M.indnumb) : (sndRel M f).indnumb_equiv i = i := rfl

/-- `(M.baseChange f)`'s containment condition holds on the fiber product over `X'`. -/
theorem baseChange_pullSubset_snd :
    (M.baseChange f).pullSubset (pullback.snd M.structureMap f) := by
  intro i γβ
  have key := PreClos.ideal_eq_reindexIdeal _ _ (sndRel M f) γβ i
  rw [sndRel_equiv M f i] at key
  have hself : (pullback_PreClos X' (pullback M.structureMap f)
        (pullback.snd M.structureMap f) (M.baseChange f).Drep).reindexIdeal
      (pullback_PreClos X' (pullback M.structureMap f) (pullback.snd M.structureMap f)
        ((M.baseChange f).Yrep.inter (M.baseChange f).Drep
          (Equiv.refl (M.baseChange f).indnumb))).cov i γβ =
      (pullback_PreClos X' (pullback M.structureMap f)
        (pullback.snd M.structureMap f) (M.baseChange f).Drep).ideal i γβ :=
    PreClos.reindexIdeal_self (pullback_PreClos X' (pullback M.structureMap f)
      (pullback.snd M.structureMap f) (M.baseChange f).Drep) i γβ
  rw [hself] at key
  have hexp : (M.baseChange f).Yrep.interIdeal (M.baseChange f).Drep
      (Equiv.refl (M.baseChange f).indnumb) i γβ.1 =
      (M.baseChange f).Yideal i γβ.1 ⊔ (M.baseChange f).Drep.ideal i γβ.1 := by
    rw [(M.baseChange f).Yrep.interIdeal_eq (M.baseChange f).Drep
      (Equiv.refl (M.baseChange f).indnumb) i γβ.1]
    congr 1
    exact PreClos.reindexIdeal_self (M.baseChange f).Drep i γβ.1
  have key2 : Ideal.map (pull_mor_ring X' (M.baseChange f).Drep
        (pullback M.structureMap f) (pullback.snd M.structureMap f) γβ).hom
        ((M.baseChange f).Yideal i γβ.1 ⊔ (M.baseChange f).Drep.ideal i γβ.1) =
      Ideal.map (pull_mor_ring X' (M.baseChange f).Drep
        (pullback M.structureMap f) (pullback.snd M.structureMap f) γβ).hom
        ((M.baseChange f).Drep.ideal i γβ.1) := by
    have hQ : (pullback_PreClos X' (pullback M.structureMap f)
        (pullback.snd M.structureMap f)
        ((M.baseChange f).Yrep.inter (M.baseChange f).Drep
          (Equiv.refl (M.baseChange f).indnumb))).ideal i γβ =
        Ideal.map (pull_mor_ring X' (M.baseChange f).Drep
          (pullback M.structureMap f) (pullback.snd M.structureMap f) γβ).hom
          ((M.baseChange f).Yrep.interIdeal (M.baseChange f).Drep
            (Equiv.refl (M.baseChange f).indnumb) i γβ.1) := rfl
    rw [← hexp]
    exact hQ.symm.trans key
  rw [Ideal.map_sup] at key2
  show Ideal.map (pull_mor_ring X' (M.baseChange f).Drep
      (pullback M.structureMap f) (pullback.snd M.structureMap f) γβ).hom
      ((M.baseChange f).Yideal i γβ.1) ≤
    Ideal.map (pull_mor_ring X' (M.baseChange f).Drep
      (pullback M.structureMap f) (pullback.snd M.structureMap f) γβ).hom
      ((M.baseChange f).Drep.ideal i γβ.1)
  exact le_trans le_sup_left key2.le

section Lemma336

variable (hcars : IsCars (pullback M.structureMap f)
  (Clos.pullback (pullback.snd M.structureMap f) (M.baseChange f).D))

include hcars in
/-- The Cartier hypothesis over `X`, from the one over `X'`. -/
theorem sndComp_isCars :
    IsCars (pullback M.structureMap f)
      (Clos.pullback (pullback.snd M.structureMap f ≫ f) M.D) := by
  have hstep : Clos.pullback (pullback.snd M.structureMap f ≫ f) M.D =
      Clos.pullback (pullback.snd M.structureMap f) (M.baseChange f).D := by
    show pullback_Clos (pullback.snd M.structureMap f ≫ f) (Quotient.mk'' M.Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  exact hcars

include hcars in
/-- Lemma 3.36, reverse direction: the section of the fiber product. -/
theorem existsUnique_baseChangeInv :
    ∃! g : pullback M.structureMap f ⟶ (M.baseChange f).dilatation,
      g ≫ (M.baseChange f).structureMap = pullback.snd M.structureMap f :=
  (M.baseChange f).universal_property (pullback M.structureMap f)
    (pullback.snd M.structureMap f) hcars (baseChange_pullSubset_snd M f)

noncomputable def baseChangeInv :
    pullback M.structureMap f ⟶ (M.baseChange f).dilatation :=
  (existsUnique_baseChangeInv M f hcars).choose

theorem baseChangeInv_over :
    baseChangeInv M f hcars ≫ (M.baseChange f).structureMap =
      pullback.snd M.structureMap f :=
  (existsUnique_baseChangeInv M f hcars).choose_spec.1

theorem baseChangeCompare_fst :
    baseChangeCompare M f ≫ pullback.fst M.structureMap f = baseChangeHom M f :=
  pullback.lift_fst _ _ _

theorem baseChangeCompare_snd :
    baseChangeCompare M f ≫ pullback.snd M.structureMap f =
      (M.baseChange f).structureMap :=
  pullback.lift_snd _ _ _

theorem baseChangeCompare_comp_inv :
    baseChangeCompare M f ≫ baseChangeInv M f hcars = 𝟙 _ :=
  ((M.baseChange f).universal_property (M.baseChange f).dilatation
    (M.baseChange f).structureMap (M.baseChange f).structureMap_isCars
    (M.baseChange f).structureMap_pullSubset).unique
    (by rw [Category.assoc, baseChangeInv_over, baseChangeCompare_snd])
    (Category.id_comp _)

theorem baseChangeInv_comp_compare :
    baseChangeInv M f hcars ≫ baseChangeCompare M f = 𝟙 _ := by
  apply pullback.hom_ext
  · have hfst : (baseChangeInv M f hcars ≫ baseChangeCompare M f) ≫
        pullback.fst M.structureMap f = baseChangeInv M f hcars ≫ baseChangeHom M f := by
      rw [Category.assoc, baseChangeCompare_fst]
    rw [hfst, Category.id_comp]
    exact (M.universal_property (pullback M.structureMap f)
      (pullback.snd M.structureMap f ≫ f) (sndComp_isCars M f hcars)
      (pullSubset_sndComp M f)).unique
      (by rw [Category.assoc, baseChangeHom_over M f, ← Category.assoc,
        baseChangeInv_over])
      pullback.condition
  · rw [Category.assoc, baseChangeCompare_snd, baseChangeInv_over, Category.id_comp]

/-- **[Ma24, Lemma 3.36]**: if the fiber product is `D'`-regular, the canonical morphism
(3.4) is an isomorphism `Bl_{Y'}^{D'} X' ≅ Bl_Y^D X ×_X X'`. -/
noncomputable def baseChangeIso :
    (M.baseChange f).dilatation ≅ pullback M.structureMap f where
  hom := baseChangeCompare M f
  inv := baseChangeInv M f hcars
  hom_inv_id := baseChangeCompare_comp_inv M f hcars
  inv_hom_id := baseChangeInv_comp_compare M f hcars

end Lemma336

section Corollary337

variable [AlgebraicGeometry.Flat f]

/-- For flat `f`, the fiber product is automatically `D'`-regular. -/
theorem baseChange_isCars_of_flat :
    IsCars (pullback M.structureMap f)
      (Clos.pullback (pullback.snd M.structureMap f) (M.baseChange f).D) := by
  have h := pullback_IsCars (pullback M.structureMap f) (pullback.fst M.structureMap f)
    (Clos.pullback M.structureMap M.D) M.structureMap_isCars
  have hstep : Clos.pullback (pullback.snd M.structureMap f) (M.baseChange f).D =
      pullback_Clos (pullback.fst M.structureMap f)
        (Clos.pullback M.structureMap M.D) := by
    show pullback_Clos (pullback.snd M.structureMap f)
        (pullback_Clos f (Quotient.mk'' M.Drep)) = _
    rw [← pullback_assoc, ← pullback.condition, pullback_assoc]
    rfl
  rw [hstep]
  exact h

/-- **[Ma24, Cor. 3.37] (isomorphism form)**: for flat `f`,
`Bl_{Y'}^{D'} X' ≅ Bl_Y^D X ×_X X'`. -/
noncomputable def flatBaseChangeIso :
    (M.baseChange f).dilatation ≅ pullback M.structureMap f :=
  baseChangeIso M f (baseChange_isCars_of_flat M f)

/-- **[Ma24, Cor. 3.37]**: for flat `f`, the canonical morphism `Bl' ⟶ Bl` is flat. -/
theorem baseChangeHom_flat : AlgebraicGeometry.Flat (baseChangeHom M f) := by
  rw [show baseChangeHom M f =
      (flatBaseChangeIso M f).hom ≫ pullback.fst M.structureMap f from
    (baseChangeCompare_fst M f).symm]
  infer_instance

/-- **[Ma24, Cor. 3.37], general form**: any property stable under base change and
respecting isomorphisms passes from `f` to `Bl' ⟶ Bl`. -/
theorem baseChangeHom_property (P : MorphismProperty Scheme.{u+1})
    [P.IsStableUnderBaseChange] [P.RespectsIso] (hf : P f) :
    P (baseChangeHom M f) := by
  rw [show baseChangeHom M f =
      (flatBaseChangeIso M f).hom ≫ pullback.fst M.structureMap f from
    (baseChangeCompare_fst M f).symm]
  exact (P.cancel_left_of_respectsIso _ _).mpr (MorphismProperty.pullback_fst _ _ hf)

end Corollary337

end PreMultiCenter
end SchemeDilatation
