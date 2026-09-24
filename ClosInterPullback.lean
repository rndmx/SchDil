import ClosInterSch
import PreClosReindex

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u+1}}

def pullback_Pre_assoc' (X'' X' : Scheme) (f' : X'' ⟶ X') (f : X' ⟶ X) (Z : PreClos X) :
    relStructure (pullback_PreClos X X'' (f' ≫ f) Z)
      (pullback_PreClos X' X'' f' (pullback_PreClos X X' f Z)) where
  indnumb_equiv := Equiv.refl _
  subscheme_iso i := (pullbackLeftPullbackSndIso (Z.subscheme i ↘ X) f f').symm
  subscheme_iso_over i := by
    rw [Scheme.Hom.isOver_iff]
    exact pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

theorem pullback_reindexIdeal (W Z : PreClos X) (T : Scheme.{u+1}) (g : T ⟶ X)
    (j : Z.indnumb) (γδ : (pull_cov X W T g).J) :
    Ideal.map (pull_mor_ring X W T g γδ).hom (Z.reindexIdeal W.cov j γδ.1) =
      (pullback_PreClos X T g Z).reindexIdeal (pull_cov X W T g) j γδ := by
  have key := PreClos.ideal_eq_reindexIdeal
    (pullback_PreClos X T g (Z.reindex W.cov)) (pullback_PreClos X T g Z)
    (pullback_lem X (Z.reindex W.cov) Z T g (Z.reindex_rel W.cov)) γδ j
  exact key

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
