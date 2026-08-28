import Tower

/-!
# Reindexing the center

[Ma24, Prop. 3.33] fixes "an arbitrary bijection `I = {1, …, k}`", so the iterated form of
the tower formula needs to know that the dilatation does not depend on how the center is
indexed. That is what this file proves: for a bijection `σ : J ≃ M.indnumb`,

* `restrict_equiv_D` / `restrict_equiv_Y` -- the reindexed center defines the *same*
  element of `Clos X` (the comparison `relStructure` is `Iso.refl` on every subscheme);
* `pullSubset_of_equiv` -- `pullSubset` transfers, since the two data share the covering
  `M.cov` and the index sets are in bijection;
* `reindexIso` -- consequently `M.dilatation ≅ (M.restrict σ).dilatation` over `X`, and
  `reindexIso_unique` says it is the only `X`-morphism.

Both directions come from the universal property, exactly as in `Tower.lean`; the forward
one is already `exists_unique_hom_restrict`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X) {Jt : Type} (σ : Jt ≃ M.indnumb)

/-- Reindexing the divisors along a bijection changes nothing up to `relStructure`. -/
def restrictEquivDrepRel : _root_.relStructure (M.restrict σ).Drep M.Drep where
  indnumb_equiv := σ
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

/-- Reindexing the centers along a bijection changes nothing up to `relStructure`. -/
def restrictEquivYrepRel : _root_.relStructure (M.restrict σ).Yrep M.Yrep where
  indnumb_equiv := σ
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Scheme.Hom.isOver_iff]

@[simp] theorem restrict_equiv_D : (M.restrict σ).D = M.D :=
  Quotient.sound ⟨M.restrictEquivDrepRel σ⟩

@[simp] theorem restrict_equiv_Y : (M.restrict σ).Y = M.Y :=
  Quotient.sound ⟨M.restrictEquivYrepRel σ⟩

/-- `pullSubset` transfers along a bijection of index sets: the two data share the
covering `M.cov`, so this is just reindexing the conjunction. -/
theorem pullSubset_of_equiv {T : Scheme.{u+1}} (f : T ⟶ X)
    (h : (M.restrict σ).pullSubset f) : M.pullSubset f := by
  intro i γβ
  have hi : Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Yideal (σ (σ.symm i)) γβ.1) ≤
      Ideal.map (pull_mor_ring X M.Drep T f γβ).hom (M.Dideal (σ (σ.symm i)) γβ.1) :=
    h (σ.symm i) γβ
  rw [Equiv.apply_symm_apply] at hi
  exact hi

/-- The reindexed dilatation is Cartier for the original divisors. -/
theorem restrict_equiv_isCars :
    IsCars (M.restrict σ).dilatation
      (Clos.pullback (M.restrict σ).structureMap M.D) := by
  have h := (M.restrict σ).structureMap_isCars
  rwa [M.restrict_equiv_D σ] at h

/-- `(M.restrict σ).dilatation ⟶ M.dilatation`, the reverse comparison. -/
theorem existsUnique_reindexInv :
    ∃! g : (M.restrict σ).dilatation ⟶ M.dilatation,
      g ≫ M.structureMap = (M.restrict σ).structureMap :=
  M.universal_property (M.restrict σ).dilatation (M.restrict σ).structureMap
    (M.restrict_equiv_isCars σ)
    (M.pullSubset_of_equiv σ (M.restrict σ).structureMap
      (M.restrict σ).structureMap_pullSubset)

/-- The forward comparison, from `exists_unique_hom_restrict`. -/
def reindexHom : M.dilatation ⟶ (M.restrict σ).dilatation :=
  (M.exists_unique_hom_restrict σ).choose

theorem reindexHom_over :
    M.reindexHom σ ≫ (M.restrict σ).structureMap = M.structureMap :=
  (M.exists_unique_hom_restrict σ).choose_spec.1

/-- The reverse comparison. -/
def reindexInv : (M.restrict σ).dilatation ⟶ M.dilatation :=
  (M.existsUnique_reindexInv σ).choose

theorem reindexInv_over :
    M.reindexInv σ ≫ M.structureMap = (M.restrict σ).structureMap :=
  (M.existsUnique_reindexInv σ).choose_spec.1

theorem reindexHom_comp_reindexInv :
    M.reindexHom σ ≫ M.reindexInv σ = 𝟙 _ := by
  have e₁ : (M.reindexHom σ ≫ M.reindexInv σ) ≫ M.structureMap = M.structureMap := by
    rw [Category.assoc, M.reindexInv_over σ, M.reindexHom_over σ]
  have e₂ : 𝟙 M.dilatation ≫ M.structureMap = M.structureMap := Category.id_comp _
  exact (M.universal_property M.dilatation M.structureMap
    M.structureMap_isCars M.structureMap_pullSubset).unique e₁ e₂

theorem reindexInv_comp_reindexHom :
    M.reindexInv σ ≫ M.reindexHom σ = 𝟙 _ := by
  have e₁ : (M.reindexInv σ ≫ M.reindexHom σ) ≫ (M.restrict σ).structureMap =
      (M.restrict σ).structureMap := by
    rw [Category.assoc, M.reindexHom_over σ, M.reindexInv_over σ]
  have e₂ : 𝟙 (M.restrict σ).dilatation ≫ (M.restrict σ).structureMap =
      (M.restrict σ).structureMap := Category.id_comp _
  exact ((M.restrict σ).universal_property (M.restrict σ).dilatation
    (M.restrict σ).structureMap (M.restrict σ).structureMap_isCars
    (M.restrict σ).structureMap_pullSubset).unique e₁ e₂

/-- **The dilatation does not depend on the indexing of the center.** -/
def reindexIso : M.dilatation ≅ (M.restrict σ).dilatation where
  hom := M.reindexHom σ
  inv := M.reindexInv σ
  hom_inv_id := M.reindexHom_comp_reindexInv σ
  inv_hom_id := M.reindexInv_comp_reindexHom σ

@[simp] theorem reindexIso_hom_over :
    (M.reindexIso σ).hom ≫ (M.restrict σ).structureMap = M.structureMap :=
  M.reindexHom_over σ

theorem reindexIso_unique (g : M.dilatation ⟶ (M.restrict σ).dilatation)
    (hg : g ≫ (M.restrict σ).structureMap = M.structureMap) :
    g = (M.reindexIso σ).hom :=
  (M.exists_unique_hom_restrict σ).choose_spec.2 g hg

end PreMultiCenter

end SchemeDilatation
