import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Ideal.Maps

universe u v w

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
