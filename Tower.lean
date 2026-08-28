import MultiCenterBaseChange
import DilatationNonZeroDivisor
import DilatationChart
import ClosInterPullback

/-!
# The tower formula for dilatations of schemes

This file formalises [Ma23d, Prop. 2.22]: for `J ⊆ I` with `K = I \ J`, the `I`-dilatation
of `X` is the `K`-dilatation, along the base-changed centers, of the `J`-dilatation of `X`;
and in particular there is a unique `X`-morphism `Bl_I X ⟶ Bl_J X`.

## Set-up

A subset `J ⊆ I` with complement `K` is encoded by two maps `ι : Jt → M.indnumb` and
`κ : Kt → M.indnumb` whose images cover `M.indnumb` (the hypothesis `hIK`). The
`J`-dilatation is `(M.restrict ι).dilatation`; the right-hand side of the formula is
`M.tower ι κ`, the dilatation of
`M.towerCenter ι κ = (M.restrict κ).baseChange (M.restrict ι).structureMap`.

## Main results

* `existsUnique_homToBase` -- the "in particular" clause, unconditionally.
* `towerCenter_isCars`, `tower_isCars`, `tower_isCars_base` -- the Cartier hypotheses of
  the universal property, for both directions, unconditionally.
* `existsUnique_towerHom`, `existsUnique_towerInv`, `towerIso`, `towerIso_hom_over`,
  `towerIso_unique` -- the two comparison morphisms and the isomorphism of the
  proposition.

## Fully unconditional

Both `pullSubset` obligations of the universal property are proved: the forward one
(`towerCenter_pullSubset`) from the cover-free `Yideal_le_Dideal_of_over_dilatation`; the
reverse one by splitting along the index set (`pullSubset_of_split`) into the `J`-half
(`tower_pullSubset_base`, the tower lies over the `J`-dilatation) and the `K`-half
(`tower_pullSubset_K`). The `K`-half is where the change of covering happens: the
containment is known on the tower's own two-step covering ([Ma24, Prop. 3.16], as the
ideal equality `structureMap_pull_inter_ideal_eq_D`), and it is transported to the
canonical one-step covering as an *equality of closed-subscheme data* -- carried by an
explicit `relStructure` (`towerKRel`) built from associativity of base change and
compatibility of base change with intersections -- then read off on the one-step charts by
`ideal_eq_reindexIdeal` and expanded by `interIdeal_eq`. No locality of ideal containments
along a covering is used anywhere: containments are carried as equalities
(`Y ∩ D = D`), which transport between coverings for free.

-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

variable {X : Scheme.{u+1}}

namespace SchemeDilatation

namespace PreMultiCenter

variable (M : PreMultiCenter X) {Jt Kt : Type} (ι : Jt → M.indnumb) (κ : Kt → M.indnumb)

section Restrict

/-- Restricting the index set preserves `pullSubset`. -/
theorem restrict_pullSubset_of {T : Scheme.{u+1}} (f : T ⟶ X) (h : M.pullSubset f) :
    (M.restrict ι).pullSubset f := fun k γβ => h (ι k) γβ

theorem restrict_id : M.restrict (id : M.indnumb → M.indnumb) = M := rfl

end Restrict

section Tower

/-- The `K`-indexed multicenter `{D_k ×_X Bl_J X / Y_k ×_X Bl_J X}` on the
`J`-dilatation. -/
abbrev towerCenter : PreMultiCenter (M.restrict ι).dilatation :=
  (M.restrict κ).baseChange (M.restrict ι).structureMap

/-- The right-hand side of [Ma23d, Prop. 2.22]. -/
abbrev tower : Scheme.{u+1} := (M.towerCenter ι κ).dilatation

/-- The structure map of the tower onto the `J`-dilatation. -/
abbrev towerToBase : M.tower ι κ ⟶ (M.restrict ι).dilatation :=
  (M.towerCenter ι κ).structureMap

/-- The structure map of the tower onto `X`. -/
abbrev towerToX : M.tower ι κ ⟶ X :=
  M.towerToBase ι κ ≫ (M.restrict ι).structureMap

end Tower

section InParticular

/-- The "in particular" clause of [Ma23d, Prop. 2.22]: there is a unique `X`-morphism
`Bl_I X ⟶ Bl_J X`. -/
theorem existsUnique_homToBase :
    ∃! g : M.dilatation ⟶ (M.restrict ι).dilatation,
      g ≫ (M.restrict ι).structureMap = M.structureMap :=
  M.exists_unique_hom_restrict ι

/-- The unique `X`-morphism `Bl_I X ⟶ Bl_J X`. -/
def homToBase : M.dilatation ⟶ (M.restrict ι).dilatation :=
  (M.existsUnique_homToBase ι).choose

@[simp] theorem homToBase_comp :
    M.homToBase ι ≫ (M.restrict ι).structureMap = M.structureMap :=
  (M.existsUnique_homToBase ι).choose_spec.1

theorem homToBase_unique (g : M.dilatation ⟶ (M.restrict ι).dilatation)
    (hg : g ≫ (M.restrict ι).structureMap = M.structureMap) : g = M.homToBase ι :=
  (M.existsUnique_homToBase ι).choose_spec.2 g hg

end InParticular

section Cartier

/-- Forward direction: the base-changed `K`-divisors are Cartier on `Bl_I X`.

All three steps are formal: `baseChange_D` identifies the divisors of `M.towerCenter ι κ`
with the `K`-divisors pulled back to `Bl_J X`, `pullback_Clos_comp` collapses the two
pullbacks into one along `homToBase ≫ p = M.structureMap`, and `restrict_isCars` is the
already-known statement that the `K`-divisors are Cartier on `Bl_I X`. -/
theorem towerCenter_isCars :
    IsCars M.dilatation (Clos.pullback (M.homToBase ι) (M.towerCenter ι κ).D) := by
  rw [baseChange_D]
  show IsCars M.dilatation
    (pullback_Clos (M.homToBase ι)
      (pullback_Clos (M.restrict ι).structureMap (M.restrict κ).D))
  rw [pullback_Clos_comp, homToBase_comp]
  exact M.restrict_isCars κ

/-- The chart-level Cartier statement on the tower, for a single index of `M`.

For a `J`-index the divisor is already Cartier on `Bl_J X` (`structureMap_isCars_chart`
for `M.restrict ι`) and stays so after the further `K`-dilatation, by
`structureMap_preserves_nonzerodiv`. For a `K`-index it becomes Cartier exactly at the
second step, by `structureMap_isCars_chart` for the tower. -/
theorem tower_isCars_chart (i : M.indnumb) (hi : (∃ j, ι j = i) ∨ ∃ k, κ k = i)
    (γβδ : (pull_cov (M.restrict ι).dilatation
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
      (M.tower ι κ) (M.towerToBase ι κ)).J) :
    ∃ g : (pull_loc_cov (M.restrict ι).dilatation
        (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
        (M.tower ι κ) (M.towerToBase ι κ) γβδ.1).obj γβδ.2,
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
          (pullback_PreClos X (M.restrict ι).dilatation
            (M.restrict ι).structureMap M.Drep)).ideal i γβδ = Ideal.span {g} ∧
      g ∈ nonZeroDivisors _ := by
  rcases hi with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨g, hg, hgnzd⟩ := (M.restrict ι).structureMap_isCars_chart j γβδ.1
    refine ⟨(pull_mor_ring (M.restrict ι).dilatation
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap M.Drep)
      (M.tower ι κ) (M.towerToBase ι κ) γβδ).hom g, ?_, ?_⟩
    · show Ideal.map _ (Ideal.map (pull_mor_ring X M.Drep _ _ γβδ.1).hom
        (M.Drep.ideal (ι j) γβδ.1.1)) = _
      rw [show Ideal.map (pull_mor_ring X M.Drep _ (M.restrict ι).structureMap γβδ.1).hom
            (M.Drep.ideal (ι j) γβδ.1.1) = Ideal.span {g} from hg,
        Ideal.map_span, Set.image_singleton]
      rfl
    · exact (M.towerCenter ι κ).structureMap_preserves_nonzerodiv γβδ hgnzd
  · exact (M.towerCenter ι κ).structureMap_isCars_chart k γβδ

/-- Reverse direction, for any sub-family of the index set: the divisors of
`M.restrict lam` are Cartier on the tower, as soon as every index of `lam` is a `J`- or a
`K`-index. -/
theorem tower_isCars_restrict {Lt : Type} (lam : Lt → M.indnumb)
    (hL : ∀ l, (∃ j, ι j = lam l) ∨ ∃ k, κ k = lam l) :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) (M.restrict lam).D) := by
  refine ⟨pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
      (pullback_PreClos X (M.restrict ι).dilatation (M.restrict ι).structureMap
        (M.restrict lam).Drep), ?_, ?_⟩
  · exact pullback_IsPreCars_of_charts _ _ _
      (fun l γβδ => M.tower_isCars_chart ι κ (lam l) (hL l) γβδ)
  · exact pullback_Clos_comp (M.restrict lam).D (M.restrict ι).structureMap
      (M.towerToBase ι κ)

/-- Reverse direction: all the divisors of `M` are Cartier on the tower. -/
theorem tower_isCars (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) M.D) :=
  M.tower_isCars_restrict ι κ id hIK

/-- The `J`-divisors are Cartier on the tower. -/
theorem tower_isCars_base :
    IsCars (M.tower ι κ) (Clos.pullback (M.towerToX ι κ) (M.restrict ι).D) :=
  M.tower_isCars_restrict ι κ ι (fun j => Or.inl ⟨j, rfl⟩)

end Cartier

section PullSubset

/-- The forward `pullSubset` hypothesis of [Ma23d, Prop. 2.22], proved.

Every affine chart of `Bl_I X` in the covering `pull_cov` for `homToBase` lies over
`Bl_I X` itself, so `Yideal_le_Dideal_of_over_dilatation` applies to `M` directly: no
covering of the chart has to be refined. -/
theorem towerCenter_pullSubset : (M.towerCenter ι κ).pullSubset (M.homToBase ι) := by
  intro k γβδ
  have h1 : (pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
        (M.homToBase ι)).map γβδ ≫ M.homToBase ι =
      Spec.map (pull_mor_ring (M.restrict ι).dilatation (M.towerCenter ι κ).Drep
          M.dilatation (M.homToBase ι) γβδ) ≫
        (pull_cov X M.Drep (M.restrict ι).dilatation
          (M.restrict ι).structureMap).map γβδ.1 :=
    pull_cov_map_comp (M.towerCenter ι κ).Drep (M.homToBase ι) γβδ
  have h2 : (pull_cov X M.Drep (M.restrict ι).dilatation
        (M.restrict ι).structureMap).map γβδ.1 ≫ (M.restrict ι).structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.restrict ι).dilatation
        (M.restrict ι).structureMap γβδ.1) ≫ M.cov.map γβδ.1.1 :=
    pull_cov_map_comp M.Drep (M.restrict ι).structureMap γβδ.1
  have hcomm :
      (pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
        (M.homToBase ι)).map γβδ ≫ M.structureMap =
      Spec.map (pull_mor_ring X M.Drep (M.restrict ι).dilatation
          (M.restrict ι).structureMap γβδ.1 ≫
        pull_mor_ring (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
          (M.homToBase ι) γβδ) ≫ M.cov.map γβδ.1.1 := by
    rw [Spec.map_comp, Category.assoc, ← h2, ← Category.assoc, ← h1, Category.assoc,
      M.homToBase_comp ι]
  have key := M.Yideal_le_Dideal_of_over_dilatation γβδ.1.1
    ((pull_cov (M.restrict ι).dilatation (M.towerCenter ι κ).Drep M.dilatation
      (M.homToBase ι)).map γβδ) _ hcomm (κ k)
  rw [CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map] at key
  exact key

/-- `pullSubset` splits along a decomposition of the index set: it is the conjunction of the
`J`-half and the `K`-half, since it is a conjunction over the indices and `restrict` shares the
covering. -/
theorem pullSubset_of_split {T : Scheme.{u+1}} (f : T ⟶ X)
    (hJ : (M.restrict ι).pullSubset f) (hK : (M.restrict κ).pullSubset f)
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) : M.pullSubset f := by
  intro i γβ
  rcases hIK i with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · exact hJ j γβ
  · exact hK k γβ

/-- Anything lying over the `J`-dilatation satisfies the `J`-half of `pullSubset`, by the
cover-free `Yideal_le_Dideal_of_over_dilatation`. -/
theorem restrict_pullSubset_of_over {T : Scheme.{u+1}} (f : T ⟶ X)
    (g : T ⟶ (M.restrict ι).dilatation) (hg : g ≫ (M.restrict ι).structureMap = f) :
    (M.restrict ι).pullSubset f := by
  intro j γε
  have hcw : ((pull_cov X (M.restrict ι).Drep T f).map γε ≫ g) ≫
      (M.restrict ι).structureMap =
      Spec.map (pull_mor_ring X (M.restrict ι).Drep T f γε) ≫ M.cov.map γε.1 := by
    rw [Category.assoc, hg]
    exact pull_cov_map_comp (M.restrict ι).Drep f γε
  exact (M.restrict ι).Yideal_le_Dideal_of_over_dilatation γε.1
    ((pull_cov X (M.restrict ι).Drep T f).map γε ≫ g) _ hcw j

/-- The `J`-half of the reverse `pullSubset`, proved: the tower lies over the
`J`-dilatation. -/
theorem tower_pullSubset_base : (M.restrict ι).pullSubset (M.towerToX ι κ) :=
  M.restrict_pullSubset_of_over ι (M.towerToX ι κ) (M.towerToBase ι κ) rfl

/-- The composite comparison of closed-subscheme data on the tower: the one-step base
change of `Y_K ∩ D_K` along `towerToX` agrees with the one-step base change of `D_K`.
Assembled from associativity of base change (`pullback_Pre_assoc'`), compatibility of
base change with intersections (`inter_pullback_rel`), and the exceptional-divisor
equality on the tower's own charts (`structureMap_pull_inter_ideal_eq_D` for
`towerCenter`, [Ma24, Prop. 3.16]). Every index equivalence involved is `Equiv.refl`,
so the composite's is definitionally the identity. -/
noncomputable def towerKRel :
    _root_.relStructure
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _)))
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep) :=
  (pullback_Pre_assoc' (M.tower ι κ) (M.restrict ι).dilatation
      (M.towerToBase ι κ) (M.restrict ι).structureMap
      ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).trans
  ((pullback_lem (M.restrict ι).dilatation _ _ (M.tower ι κ) (M.towerToBase ι κ)
      (inter_pullback_rel (M.restrict κ).Yrep (M.restrict κ).Drep (Equiv.refl _)
        (M.restrict ι).dilatation (M.restrict ι).structureMap)).trans
  ((PreClos.relStructure_of_ideal_eq
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
        ((M.towerCenter ι κ).Yrep.inter (M.towerCenter ι κ).Drep (Equiv.refl _)))
      (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
        (M.towerCenter ι κ).Drep)
      (Equiv.refl _)
      (by
        intro k γβ
        have hmain := (M.towerCenter ι κ).structureMap_pull_inter_ideal_eq_D k γβ
        have h2 : (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep).reindexIdeal
              (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ) (M.towerToBase ι κ)
                ((M.towerCenter ι κ).Yrep.inter (M.towerCenter ι κ).Drep (Equiv.refl _))).cov
              k γβ =
            (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep).ideal k γβ :=
          PreClos.reindexIdeal_self
            (pullback_PreClos (M.restrict ι).dilatation (M.tower ι κ)
              (M.towerToBase ι κ) (M.towerCenter ι κ).Drep) k γβ
        exact hmain.trans h2.symm)).trans
  (pullback_Pre_assoc' (M.tower ι κ) (M.restrict ι).dilatation
      (M.towerToBase ι κ) (M.restrict ι).structureMap (M.restrict κ).Drep).symm))

/-- **The reverse `pullSubset`, `K`-half — proved.** Reading the comparison
`towerKRel` on the canonical one-step covering (`ideal_eq_reindexIdeal`) and expanding
`interIdeal = Y ⊔ D` (`interIdeal_eq`) turns the class equality into
`map ρ Y ⊔ map ρ D = map ρ D`, i.e. the required containment. -/
theorem tower_pullSubset_K : (M.restrict κ).pullSubset (M.towerToX ι κ) := by
  intro k γε
  -- ideal equality from the composite relStructure
  have key := PreClos.ideal_eq_reindexIdeal _ _ (M.towerKRel ι κ) γε k
  have hself : (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        (M.restrict κ).Drep).reindexIdeal
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).cov
      ((M.towerKRel ι κ).indnumb_equiv k) γε =
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep).ideal
        ((M.towerKRel ι κ).indnumb_equiv k) γε :=
    PreClos.reindexIdeal_self
      (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ) (M.restrict κ).Drep) _ γε
  rw [hself] at key
  have hek : (M.towerKRel ι κ).indnumb_equiv k = k := rfl
  rw [hek] at key
  -- key : map ρ (interIdeal Yκ Dκ refl k γ) = map ρ (Dκ.ideal k γ)
  have hexp : (M.restrict κ).Yrep.interIdeal (M.restrict κ).Drep (Equiv.refl _) k γε.1 =
      (M.restrict κ).Yrep.ideal k γε.1 ⊔ (M.restrict κ).Drep.ideal k γε.1 := by
    rw [(M.restrict κ).Yrep.interIdeal_eq (M.restrict κ).Drep (Equiv.refl _) k γε.1]
    congr 1
    exact PreClos.reindexIdeal_self (M.restrict κ).Drep k γε.1
  have key2 : Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom
        ((M.restrict κ).Yrep.ideal k γε.1 ⊔ (M.restrict κ).Drep.ideal k γε.1) =
      Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Drep.ideal k γε.1) := by
    have : (pullback_PreClos X (M.tower ι κ) (M.towerToX ι κ)
        ((M.restrict κ).Yrep.inter (M.restrict κ).Drep (Equiv.refl _))).ideal k γε =
        Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
          (M.towerToX ι κ) γε).hom
          ((M.restrict κ).Yrep.interIdeal (M.restrict κ).Drep (Equiv.refl _) k γε.1) := rfl
    rw [← hexp]
    exact this.symm.trans key
  rw [Ideal.map_sup] at key2
  show Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Yrep.ideal k γε.1) ≤
      Ideal.map (pull_mor_ring X (M.restrict κ).Drep (M.tower ι κ)
        (M.towerToX ι κ) γε).hom ((M.restrict κ).Drep.ideal k γε.1)
  exact le_trans le_sup_left key2.le

end PullSubset

section Comparison

/-- `Bl_I X ⟶ Bl_K(Bl_J X)`, the forward comparison morphism. -/
theorem existsUnique_towerHom :
    ∃! a : M.dilatation ⟶ M.tower ι κ, a ≫ M.towerToBase ι κ = M.homToBase ι :=
  (M.towerCenter ι κ).universal_property M.dilatation (M.homToBase ι)
    (M.towerCenter_isCars ι κ) (M.towerCenter_pullSubset ι κ)

/-- `Bl_K(Bl_J X) ⟶ Bl_I X`, the reverse comparison morphism. -/
theorem existsUnique_towerInv (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    ∃! b : M.tower ι κ ⟶ M.dilatation, b ≫ M.structureMap = M.towerToX ι κ :=
  M.universal_property (M.tower ι κ) (M.towerToX ι κ) (M.tower_isCars ι κ hIK)
    (M.pullSubset_of_split ι κ (M.towerToX ι κ) (M.tower_pullSubset_base ι κ)
      (M.tower_pullSubset_K ι κ) hIK)

/-- The forward comparison morphism. -/
def towerHom : M.dilatation ⟶ M.tower ι κ :=
  (M.existsUnique_towerHom ι κ).choose

theorem towerHom_comp :
    M.towerHom ι κ ≫ M.towerToBase ι κ = M.homToBase ι :=
  (M.existsUnique_towerHom ι κ).choose_spec.1

theorem towerHom_over :
    M.towerHom ι κ ≫ M.towerToX ι κ = M.structureMap := by
  show M.towerHom ι κ ≫ M.towerToBase ι κ ≫ (M.restrict ι).structureMap = _
  rw [← Category.assoc, M.towerHom_comp ι κ, M.homToBase_comp ι]

/-- The reverse comparison morphism. -/
def towerInv (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) : M.tower ι κ ⟶ M.dilatation :=
  (M.existsUnique_towerInv ι κ hIK).choose

theorem towerInv_over (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.structureMap = M.towerToX ι κ :=
  (M.existsUnique_towerInv ι κ hIK).choose_spec.1

/-- The reverse comparison morphism is a morphism over the `J`-dilatation. -/
theorem towerInv_comp_homToBase (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.homToBase ι = M.towerToBase ι κ := by
  have e₁ : (M.towerInv ι κ hIK ≫ M.homToBase ι) ≫ (M.restrict ι).structureMap =
      M.towerToX ι κ := by
    rw [Category.assoc, M.homToBase_comp ι, M.towerInv_over ι κ hIK]
  have e₂ : M.towerToBase ι κ ≫ (M.restrict ι).structureMap = M.towerToX ι κ := rfl
  exact ((M.restrict ι).universal_property (M.tower ι κ) (M.towerToX ι κ)
    (M.tower_isCars_base ι κ)
    (M.tower_pullSubset_base ι κ)).unique e₁ e₂

theorem towerHom_comp_towerInv
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerHom ι κ ≫ M.towerInv ι κ hIK = 𝟙 _ := by
  have e₁ : (M.towerHom ι κ ≫ M.towerInv ι κ hIK) ≫ M.structureMap =
      M.structureMap := by
    rw [Category.assoc, M.towerInv_over ι κ hIK, M.towerHom_over ι κ]
  have e₂ : 𝟙 M.dilatation ≫ M.structureMap = M.structureMap := Category.id_comp _
  exact (M.universal_property M.dilatation M.structureMap
    M.structureMap_isCars M.structureMap_pullSubset).unique e₁ e₂

theorem towerInv_comp_towerHom
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.towerInv ι κ hIK ≫ M.towerHom ι κ = 𝟙 _ := by
  have e₁ : (M.towerInv ι κ hIK ≫ M.towerHom ι κ) ≫ M.towerToBase ι κ =
      M.towerToBase ι κ := by
    rw [Category.assoc, M.towerHom_comp ι κ,
      M.towerInv_comp_homToBase ι κ hIK]
  have e₂ : 𝟙 (M.tower ι κ) ≫ M.towerToBase ι κ = M.towerToBase ι κ := Category.id_comp _
  exact ((M.towerCenter ι κ).universal_property (M.tower ι κ) (M.towerToBase ι κ)
    (M.towerCenter ι κ).structureMap_isCars
    (M.towerCenter ι κ).structureMap_pullSubset).unique e₁ e₂

/-- **[Ma23d, Prop. 2.22]**: the `I`-dilatation of `X` is the `K`-dilatation, along the
base-changed centers, of the `J`-dilatation of `X`. -/
def towerIso (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    M.dilatation ≅ M.tower ι κ where
  hom := M.towerHom ι κ
  inv := M.towerInv ι κ hIK
  hom_inv_id := M.towerHom_comp_towerInv ι κ hIK
  inv_hom_id := M.towerInv_comp_towerHom ι κ hIK

@[simp] theorem towerIso_hom_over
    (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i) :
    (M.towerIso ι κ hIK).hom ≫ M.towerToX ι κ = M.structureMap :=
  M.towerHom_over ι κ

/-- The isomorphism of [Ma23d, Prop. 2.22] is the unique morphism over `X`. -/
theorem towerIso_unique (hIK : ∀ i, (∃ j, ι j = i) ∨ ∃ k, κ k = i)
    (e : M.dilatation ⟶ M.tower ι κ) (he : e ≫ M.towerToX ι κ = M.structureMap) :
    e = (M.towerIso ι κ hIK).hom :=
  (M.existsUnique_towerHom ι κ).unique
    (M.homToBase_unique ι (e ≫ M.towerToBase ι κ) (by rw [Category.assoc]; exact he))
    (M.towerHom_comp ι κ)

end Comparison

end PreMultiCenter

end SchemeDilatation
