import Tower

/-!
# Functoriality of dilatations: [Ma24, §3.6]

Let `M` be a multicenter on `X`, `M'` a multicenter on `X'`, and `f : X' ⟶ X` such that

* `f⁻¹(Dᵢ) = D'ᵢ` — expressed as a `relStructure RD` between the base change of the
  divisors and `M'`'s divisors (its index equivalence `e := RD.indnumb_equiv` is the
  paper's identification of the two index sets);
* the restriction of `f` to `Z'ᵢ = Y'ᵢ ∩ D'ᵢ` factors through `Zᵢ` — expressed ideal-wise
  on the covering `M'.cov` as `hY`: the ideal of `f⁻¹(Yᵢ)` (read on `M'.cov` via
  `reindexIdeal`) is contained in the ideal of `Z'ᵢ`.

Then there is a unique morphism `Bl_{Y'}^{D'} X' ⟶ Bl_Y^D X` making the square with the
structure maps and `f` commute. As in the paper, "this follows directly from
Proposition 3.17": the composite `Bl' → X' → X` satisfies the universal-property
conditions of `Bl_Y^D X`.

* Cartier-ness (`functoriality_isCars`) transports through `RD` and associativity of
  base change — three rewrites at the `Clos` level.
* The containment (`functoriality_pullSubset`) is carried, as everywhere in this
  development, as an *equality* of closed subschemes `f'⁻¹(Y ∩ D) = f'⁻¹(D)`
  (`functRel`), assembled from associativity of base change, compatibility of base
  change with intersections, `RD`, and — the only substantive input — the exceptional
  divisor equality [Ma24, Prop. 3.16] for `M'` together with `hY`
  (`functoriality_content`), then read off on the canonical covering.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

namespace PreMultiCenter

variable {X X' : Scheme.{u+1}} (M : PreMultiCenter X) (M' : PreMultiCenter X')
  (f : X' ⟶ X)
  (RD : _root_.relStructure (pullback_PreClos X X' f M.Drep) M'.Drep)
  (hY : ∀ (i : M.indnumb) (γ' : M'.cov.J),
    (pullback_PreClos X X' f M.Yrep).reindexIdeal M'.cov i γ' ≤
      M'.Yideal (RD.indnumb_equiv i) γ' ⊔ M'.Dideal (RD.indnumb_equiv i) γ')

include RD in
/-- Cartier-ness of the pulled-back divisors on `Bl'`: transport
`M'.structureMap_isCars` through `f⁻¹(D) = D'` and associativity of base change. -/
theorem functoriality_isCars :
    IsCars M'.dilatation (Clos.pullback (M'.structureMap ≫ f) M.D) := by
  have h := M'.structureMap_isCars
  have hD : (Quotient.mk'' (pullback_PreClos X X' f M.Drep) : Clos X') = M'.D :=
    Quotient.sound ⟨RD⟩
  rw [← hD] at h
  have hstep : Clos.pullback (M'.structureMap ≫ f) M.D =
      Clos.pullback M'.structureMap
        (Quotient.mk'' (pullback_PreClos X X' f M.Drep)) := by
    show pullback_Clos (M'.structureMap ≫ f) (Quotient.mk'' M.Drep) = _
    rw [pullback_assoc]
    rfl
  rw [hstep]
  exact h

include hY in
/-- The substantive chart-level input: on the canonical covering of `Bl'` over `X'`,
the ideal of the pullback of `f⁻¹(Y) ∩ D'` equals the ideal of the pullback of `D'`.
Combines `hY` with the exceptional divisor equality [Ma24, Prop. 3.16] for `M'`. -/
theorem functoriality_content (i : M.indnumb)
    (γδ : (pull_cov X' M'.Drep M'.dilatation M'.structureMap).J) :
    (pullback_PreClos X' M'.dilatation M'.structureMap
        (((pullback_PreClos X X' f M.Yrep).reindex M'.cov).inter M'.Drep
          RD.indnumb_equiv)).ideal i γδ =
      (pullback_PreClos X' M'.dilatation M'.structureMap M'.Drep).reindexIdeal
        (pullback_PreClos X' M'.dilatation M'.structureMap
          (((pullback_PreClos X X' f M.Yrep).reindex M'.cov).inter M'.Drep
            RD.indnumb_equiv)).cov (RD.indnumb_equiv i) γδ := by
  have hself : (pullback_PreClos X' M'.dilatation M'.structureMap M'.Drep).reindexIdeal
      (pullback_PreClos X' M'.dilatation M'.structureMap
        (((pullback_PreClos X X' f M.Yrep).reindex M'.cov).inter M'.Drep
          RD.indnumb_equiv)).cov (RD.indnumb_equiv i) γδ =
      (pullback_PreClos X' M'.dilatation M'.structureMap M'.Drep).ideal
        (RD.indnumb_equiv i) γδ :=
    PreClos.reindexIdeal_self
      (pullback_PreClos X' M'.dilatation M'.structureMap M'.Drep) (RD.indnumb_equiv i) γδ
  have hmain : Ideal.map (pull_mor_ring X' M'.Drep M'.dilatation
        M'.structureMap γδ).hom
        (((pullback_PreClos X X' f M.Yrep).reindex M'.cov).interIdeal M'.Drep
          RD.indnumb_equiv i γδ.1) =
      Ideal.map (pull_mor_ring X' M'.Drep M'.dilatation M'.structureMap γδ).hom
        (M'.Drep.ideal (RD.indnumb_equiv i) γδ.1) := by
    have expand : ((pullback_PreClos X X' f M.Yrep).reindex M'.cov).interIdeal M'.Drep
        RD.indnumb_equiv i γδ.1 =
        ((pullback_PreClos X X' f M.Yrep).reindex M'.cov).ideal i γδ.1 ⊔
          M'.Drep.ideal (RD.indnumb_equiv i) γδ.1 := by
      rw [((pullback_PreClos X X' f M.Yrep).reindex M'.cov).interIdeal_eq M'.Drep
        RD.indnumb_equiv i γδ.1]
      congr 1
      exact PreClos.reindexIdeal_self M'.Drep (RD.indnumb_equiv i) γδ.1
    rw [expand, Ideal.map_sup, sup_eq_right]
    have h2 := hY i γδ.1
    refine le_trans (Ideal.map_mono h2) ?_
    have h3 : M'.Yideal (RD.indnumb_equiv i) γδ.1 ⊔
        M'.Dideal (RD.indnumb_equiv i) γδ.1 =
        M'.Yrep.interIdeal M'.Drep (Equiv.refl M'.indnumb) (RD.indnumb_equiv i) γδ.1 := by
      rw [M'.Yrep.interIdeal_eq M'.Drep (Equiv.refl M'.indnumb)
        (RD.indnumb_equiv i) γδ.1]
      congr 1
      exact (PreClos.reindexIdeal_self M'.Drep (RD.indnumb_equiv i) γδ.1).symm
    rw [h3]
    exact le_of_eq (M'.structureMap_pull_inter_ideal_eq_D (RD.indnumb_equiv i) γδ)
  exact hmain.trans hself.symm

/-- The composite comparison: on `Bl'`, the pullback of `Y ∩ D` along
`M'.structureMap ≫ f` agrees with the pullback of `D`. -/
noncomputable def functRel : _root_.relStructure
    (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f)
      (M.Yrep.inter M.Drep (Equiv.refl M.indnumb)))
    (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f) M.Drep) :=
  (pullback_Pre_assoc' M'.dilatation X' M'.structureMap f
      (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).trans
  ((pullback_lem X' _ _ M'.dilatation M'.structureMap
      (inter_pullback_rel M.Yrep M.Drep (Equiv.refl M.indnumb) X' f)).trans
  ((pullback_lem X' _ _ M'.dilatation M'.structureMap
      (PreClos.interRel (pullback_PreClos X X' f M.Yrep) (pullback_PreClos X X' f M.Drep)
        ((pullback_PreClos X X' f M.Yrep).reindex M'.cov) M'.Drep
        (Equiv.refl _) RD.indnumb_equiv
        ((pullback_PreClos X X' f M.Yrep).reindex_rel M'.cov).symm RD
        (fun _ => rfl))).trans
  ((PreClos.relStructure_of_ideal_eq
      (pullback_PreClos X' M'.dilatation M'.structureMap
        (((pullback_PreClos X X' f M.Yrep).reindex M'.cov).inter M'.Drep
          RD.indnumb_equiv))
      (pullback_PreClos X' M'.dilatation M'.structureMap M'.Drep)
      RD.indnumb_equiv (functoriality_content M M' f RD hY)).trans
  ((pullback_lem X' _ _ M'.dilatation M'.structureMap RD.symm).trans
  (pullback_Pre_assoc' M'.dilatation X' M'.structureMap f M.Drep).symm))))

include RD hY in
/-- The containment condition on `Bl'`: read `functRel` off on the canonical covering. -/
theorem functoriality_pullSubset : M.pullSubset (M'.structureMap ≫ f) := by
  intro i γβ
  have key := PreClos.ideal_eq_reindexIdeal _ _ (functRel M M' f RD hY) γβ i
  have hei : (functRel M M' f RD hY).indnumb_equiv i = i :=
    Equiv.symm_apply_apply RD.indnumb_equiv i
  rw [hei] at key
  have hself : (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f)
        M.Drep).reindexIdeal
      (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f)
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).cov i γβ =
      (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f) M.Drep).ideal i γβ :=
    PreClos.reindexIdeal_self
      (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f) M.Drep) i γβ
  rw [hself] at key
  have hexp : M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1 =
      M.Yideal i γβ.1 ⊔ M.Drep.ideal i γβ.1 := by
    rw [M.Yrep.interIdeal_eq M.Drep (Equiv.refl M.indnumb) i γβ.1]
    congr 1
    exact PreClos.reindexIdeal_self M.Drep i γβ.1
  have key2 : Ideal.map (pull_mor_ring X M.Drep M'.dilatation
        (M'.structureMap ≫ f) γβ).hom (M.Yideal i γβ.1 ⊔ M.Drep.ideal i γβ.1) =
      Ideal.map (pull_mor_ring X M.Drep M'.dilatation
        (M'.structureMap ≫ f) γβ).hom (M.Drep.ideal i γβ.1) := by
    have hQ : (pullback_PreClos X M'.dilatation (M'.structureMap ≫ f)
        (M.Yrep.inter M.Drep (Equiv.refl M.indnumb))).ideal i γβ =
        Ideal.map (pull_mor_ring X M.Drep M'.dilatation
          (M'.structureMap ≫ f) γβ).hom
          (M.Yrep.interIdeal M.Drep (Equiv.refl M.indnumb) i γβ.1) := rfl
    rw [← hexp]
    exact hQ.symm.trans key
  rw [Ideal.map_sup] at key2
  show Ideal.map (pull_mor_ring X M.Drep M'.dilatation
      (M'.structureMap ≫ f) γβ).hom (M.Yideal i γβ.1) ≤
    Ideal.map (pull_mor_ring X M.Drep M'.dilatation
      (M'.structureMap ≫ f) γβ).hom (M.Drep.ideal i γβ.1)
  exact le_trans le_sup_left key2.le

include RD hY in
/-- **[Ma24, §3.6], functoriality**: there is a unique morphism
`Bl_{Y'}^{D'} X' ⟶ Bl_Y^D X` making the square with the structure maps and `f`
commute. -/
theorem existsUnique_functorialityHom :
    ∃! g : M'.dilatation ⟶ M.dilatation,
      g ≫ M.structureMap = M'.structureMap ≫ f :=
  M.universal_property M'.dilatation (M'.structureMap ≫ f)
    (functoriality_isCars M M' f RD) (functoriality_pullSubset M M' f RD hY)

/-- The functoriality morphism `Bl_{Y'}^{D'} X' ⟶ Bl_Y^D X`. -/
noncomputable def functorialityHom : M'.dilatation ⟶ M.dilatation :=
  (existsUnique_functorialityHom M M' f RD hY).choose

/-- The commuting square of [Ma24, §3.6]. -/
@[simp] theorem functorialityHom_over :
    functorialityHom M M' f RD hY ≫ M.structureMap = M'.structureMap ≫ f :=
  (existsUnique_functorialityHom M M' f RD hY).choose_spec.1

theorem functorialityHom_unique (g : M'.dilatation ⟶ M.dilatation)
    (hg : g ≫ M.structureMap = M'.structureMap ≫ f) :
    g = functorialityHom M M' f RD hY :=
  (existsUnique_functorialityHom M M' f RD hY).choose_spec.2 g hg

end PreMultiCenter

end SchemeDilatation
