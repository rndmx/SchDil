import ClosInterSch
import PreClosReindex

/-!
# Base change commutes with intersection of closed-subscheme data

Three transport results used to discharge the `pullSubset` hypothesis of the tower formula:

* `pullback_Pre_assoc'` -- the explicit-`relStructure` form of `pullback_Pre_assoc`
  (associativity of base change), with `Equiv.refl` as index equivalence, so that the
  equivalence of a composite of these structures is computable.
* `pullback_reindexIdeal` -- pushing forward a `reindexIdeal` along the canonical ring map
  of a base change computes the `reindexIdeal` of the base-changed datum. Proved from
  `ideal_eq_reindexIdeal` applied to the base change of `Z.reindex W.cov`, whose ideals are
  *definitionally* the left-hand side.
* `inter_pullback_rel` -- base change commutes with `PreClos.inter`, as a `relStructure`
  with `Equiv.refl`. Both sides live on the same covering (`pull_cov` only depends on the
  covering of its argument), so this is `relStructure_of_ideal_eq` applied to the ideal
  computation `map ρ (I ⊔ J) = map ρ I ⊔ map ρ J` plus `pullback_reindexIdeal`.
-/

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

/-- Associativity of base change of closed-subscheme data, as an explicit `relStructure`
with `Equiv.refl` as index equivalence. -/
def pullback_Pre_assoc' (X'' X' : Scheme) (f' : X'' ⟶ X') (f : X' ⟶ X) (Z : PreClos X) :
    relStructure (pullback_PreClos X X'' (f' ≫ f) Z)
      (pullback_PreClos X' X'' f' (pullback_PreClos X X' f Z)) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso i := (pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) f f').symm
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

/-- Pushing a `reindexIdeal` forward along the canonical ring map of a base change gives
the `reindexIdeal` of the base-changed datum, on the base-changed covering. -/
theorem pullback_reindexIdeal (W Z : PreClos X) (T : Scheme.{u+1}) (g : T ⟶ X)
    (j : Z.indnumb) (γδ : (pull_cov X W T g).J) :
    Ideal.map (pull_mor_ring X W T g γδ).hom (Z.reindexIdeal W.cov j γδ.1) =
      (pullback_PreClos X T g Z).reindexIdeal (pull_cov X W T g) j γδ := by
  have key := PreClos.ideal_eq_reindexIdeal
    (pullback_PreClos X T g (Z.reindex W.cov)) (pullback_PreClos X T g Z)
    (pullback_lem X (Z.reindex W.cov) Z T g (Z.reindex_rel W.cov)) γδ j
  exact key

/-- Base change commutes with the intersection of two closed-subscheme data. -/
noncomputable def inter_pullback_rel (W Z : PreClos X) (e : W.indnumb ≃ Z.indnumb)
    (T : Scheme.{u+1}) (g : T ⟶ X) :
    relStructure (pullback_PreClos X T g (W.inter Z e))
      ((pullback_PreClos X T g W).inter (pullback_PreClos X T g Z) e) :=
  PreClos.relStructure_of_ideal_eq _ _ (Equiv.refl _) (by
    intro i γδ
    have h2 : ((pullback_PreClos X T g W).inter (pullback_PreClos X T g Z) e).reindexIdeal
        (pullback_PreClos X T g (W.inter Z e)).cov i γδ =
        ((pullback_PreClos X T g W).inter (pullback_PreClos X T g Z) e).ideal i γδ :=
      PreClos.reindexIdeal_self
        ((pullback_PreClos X T g W).inter (pullback_PreClos X T g Z) e) i γδ
    have hmain : Ideal.map (pull_mor_ring X W T g γδ).hom (W.interIdeal Z e i γδ.1) =
        (pullback_PreClos X T g W).interIdeal (pullback_PreClos X T g Z) e i γδ := by
      rw [W.interIdeal_eq Z e i γδ.1,
        (pullback_PreClos X T g W).interIdeal_eq (pullback_PreClos X T g Z) e i γδ,
        Ideal.map_sup, pullback_reindexIdeal W Z T g (e i) γδ]
      rfl
    exact hmain.trans h2.symm)
