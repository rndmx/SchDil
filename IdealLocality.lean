import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Ideal.Maps

/-!
# Locality of an inclusion of ideals along a covering

`Ideal.le_of_localization_maximal` tests an inclusion `I ≤ J` in the canonical
localizations `Localization.AtPrime P`. Geometrically one wants to test it on the members
of an affine open covering of `Spec R` instead: each member is a ring `S` between `R` and
the local ring at a point of it, but is not itself a localization of `R`.

`Ideal.le_of_localization_cover` is that test. The intended instantiation is
`S P = Γ(Y, U)` for an affine open `U` of `Y = Spec R` containing the point `P`, and
`T P = Y.presheaf.stalk P`, the common stalk: `IsAffineOpen.isLocalization_stalk` applied
to `⊤` says `T P` is the localization of `R` at `P`, and applied to `U` it makes `T P` an
`S P`-algebra, giving the scalar tower.

This is the ingredient needed to transport a containment of closed subschemes from a
covering on which it is known to the canonical covering that `pullSubset` is stated on.
-/

universe u v w

/-- An inclusion of ideals may be tested in *any* ring that computes the localization of
`R` at `P`, not only in the canonical `Localization.AtPrime P`. -/
theorem Ideal.map_le_map_localization_of_isLocalization
    {R : Type u} [CommRing R] (I J : Ideal R) (P : Ideal R) [P.IsPrime]
    (T : Type v) [CommRing T] [Algebra R T] [IsLocalization.AtPrime T P]
    (h : Ideal.map (algebraMap R T) I ≤ Ideal.map (algebraMap R T) J) :
    Ideal.map (algebraMap R (Localization.AtPrime P)) I ≤
      Ideal.map (algebraMap R (Localization.AtPrime P)) J := by
  set e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) T with he
  set φ : Localization.AtPrime P →+* T := e.toRingEquiv.toRingHom with hφ
  have hbij : Function.Bijective φ := e.toRingEquiv.bijective
  have hcomp : algebraMap R T = φ.comp (algebraMap R (Localization.AtPrime P)) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, hφ]
    exact (e.commutes x).symm
  rw [hcomp, ← Ideal.map_map, ← Ideal.map_map] at h
  have hc := Ideal.comap_mono (f := φ) h
  rwa [Ideal.comap_map_of_bijective φ hbij, Ideal.comap_map_of_bijective φ hbij] at hc

/-- **Locality of an inclusion of ideals along a covering.**

If, for every maximal ideal `P` of `R`, there is a ring `S P` receiving `R` and sitting
under a ring `T P` that computes the localization of `R` at `P`, and the inclusion
`I ≤ J` becomes true in `S P`, then `I ≤ J` holds in `R`.

Taking `S P` to be the ring of a member of an affine open covering of `Spec R` whose open
set contains `P`, and `T P` the local ring there, this says an inclusion of ideals may be
checked on an affine open covering. -/
theorem Ideal.le_of_localization_cover {R : Type u} [CommRing R] {I J : Ideal R}
    (S : ∀ (P : Ideal R) [P.IsMaximal], Type v)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (S P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (S P)]
    (T : ∀ (P : Ideal R) [P.IsMaximal], Type w)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (T P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (T P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra (S P) (T P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (S P) (T P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (T P) P]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Ideal.map (algebraMap R (S P)) I ≤ Ideal.map (algebraMap R (S P)) J) :
    I ≤ J := by
  refine Ideal.le_of_localization_maximal fun P hP => ?_
  haveI := hP
  refine Ideal.map_le_map_localization_of_isLocalization I J P (T P) ?_
  rw [IsScalarTower.algebraMap_eq R (S P) (T P), ← Ideal.map_map, ← Ideal.map_map]
  exact Ideal.map_mono (h P)
