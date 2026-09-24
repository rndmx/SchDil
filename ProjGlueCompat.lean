import ProjComparison
import Project.Potions.Basic

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open HomogeneousLocalization HomogeneousSubmonoid

namespace ProjGlueCompat

section ExtVal

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] {P Q : Submonoid A}

theorem funext_val {α : Sort*} {F G : α → HomogeneousLocalization 𝒜 Q}
    (h : ∀ a, (F a).val = (G a).val) : F = G :=
  funext fun a => HomogeneousLocalization.val_injective _ (h a)

theorem ringHom_ext_val {B : Type*} [CommRing B] {F G : B →+* HomogeneousLocalization 𝒜 Q}
    (h : ∀ b, (F b).val = (G b).val) : F = G :=
  RingHom.ext fun b => HomogeneousLocalization.val_injective _ (h b)

theorem ringHom_ext_val_mk
    {F G : HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization 𝒜 Q}
    (h : ∀ y : NumDenSameDeg 𝒜 P, (F (mk y)).val = (G (mk y)).val) : F = G := by
  refine ringHom_ext_val fun z => ?_
  obtain ⟨y, rfl⟩ := mk_surjective z
  exact h y

end ExtVal

section LocMap

variable {A : Type*} [CommRing A] {P Q W : Submonoid A}

noncomputable def locMap (h : P ≤ Q) : Localization P →+* Localization Q :=
  IsLocalization.map (M := P) (T := Q) (Localization Q) (RingHom.id A)
    (show P ≤ Q.comap (RingHom.id A) from h)

@[simp] theorem locMap_mk (h : P ≤ Q) (a : A) (b : P) :
    locMap h (Localization.mk a b) = Localization.mk a ⟨(b : A), h b.2⟩ := by
  rw [Localization.mk_eq_mk'_apply, locMap, IsLocalization.map_mk',
    ← Localization.mk_eq_mk'_apply]
  rfl

theorem locMap_locMap (h1 : P ≤ Q) (h2 : Q ≤ W) (z : Localization P) :
    locMap h2 (locMap h1 z) = locMap (h1.trans h2) z := by
  induction z using Localization.induction_on with
  | H y => obtain ⟨a, b⟩ := y; rw [locMap_mk, locMap_mk, locMap_mk]

end LocMap

section MapId

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {P Q : Submonoid A}

theorem val_mapId_mk (h : P ≤ Q) (y : NumDenSameDeg 𝒜 P) :
    (mapId 𝒜 h (mk y)).val = Localization.mk (y.num : A) ⟨(y.den : A), h y.den_mem⟩ := rfl

theorem val_mapId (h : P ≤ Q) (z : HomogeneousLocalization 𝒜 P) :
    (mapId 𝒜 h z).val = locMap h z.val := by
  obtain ⟨y, rfl⟩ := mk_surjective z
  rw [val_mapId_mk, val_mk, locMap_mk]

end MapId

section Potion

variable {ι R A : Type*} [AddCommGroup ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (S T : HomogeneousSubmonoid 𝒜)

theorem toSubmonoid_le_mul : S.toSubmonoid ≤ (S * T).toSubmonoid :=
  fun _ ha => left_le_mul S T ha

theorem potionToMul_eq_mapId :
    S.potionToMul T = mapId 𝒜 (toSubmonoid_le_mul S T) := rfl

theorem val_potionToMul_mk (y : NumDenSameDeg 𝒜 S.toSubmonoid) :
    (S.potionToMul T (mk y)).val =
      Localization.mk (y.num : A) ⟨(y.den : A), toSubmonoid_le_mul S T y.den_mem⟩ := rfl

theorem val_potionToMul (z : S.Potion) :
    (S.potionToMul T z).val = locMap (toSubmonoid_le_mul S T) z.val := by
  rw [potionToMul_eq_mapId, val_mapId]

end Potion

section Away

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable {e : ι} {f g x : A}

theorem locMap_val_awayMap (hg : g ∈ 𝒜 e) (hx : x = f * g) {Q : Submonoid A}
    (hfQ : Submonoid.powers f ≤ Q) (hxQ : Submonoid.powers x ≤ Q) (z : Away 𝒜 f) :
    locMap hxQ (awayMap 𝒜 hg hx z).val = locMap hfQ z.val := by
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb⟩, i, (rfl : f ^ i = b)⟩, rfl⟩ := mk_surjective z
  rw [val_awayMap_mk 𝒜 hg hx, val_mk, locMap_mk, locMap_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by subst hx; ring⟩

theorem mapId_comp_awayMap (hg : g ∈ 𝒜 e) (hx : x = f * g) {Q : Submonoid A}
    (hfQ : Submonoid.powers f ≤ Q) (hxQ : Submonoid.powers x ≤ Q) :
    (mapId 𝒜 hxQ).comp (awayMap 𝒜 hg hx) = mapId 𝒜 hfQ :=
  ringHom_ext_val fun z => by
    rw [RingHom.comp_apply, val_mapId, val_mapId, locMap_val_awayMap]

end Away

section Compare

open ProjComparison

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

noncomputable def awayToPotion (f : A) (U : HomogeneousSubmonoid (intGrading 𝒜))
    (h : Submonoid.powers f ≤ U.toSubmonoid) : Away 𝒜 f →+* U.Potion :=
  (mapId (intGrading 𝒜) h).comp (transport 𝒜 Nat.toIntHom (Submonoid.powers f))

theorem val_awayToPotion (f : A) (U : HomogeneousSubmonoid (intGrading 𝒜))
    (h : Submonoid.powers f ≤ U.toSubmonoid) (z : Away 𝒜 f) :
    (awayToPotion 𝒜 f U h z).val = locMap h z.val := by
  rw [awayToPotion, RingHom.comp_apply, val_mapId, val_transport]

theorem awayToPotion_comp_awayMap {e : ℕ} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (U : HomogeneousSubmonoid (intGrading 𝒜))
    (hfU : Submonoid.powers f ≤ U.toSubmonoid) (hxU : Submonoid.powers x ≤ U.toSubmonoid) :
    (awayToPotion 𝒜 x U hxU).comp (awayMap 𝒜 hg hx) = awayToPotion 𝒜 f U hfU :=
  ringHom_ext_val fun z => by
    rw [RingHom.comp_apply, val_awayToPotion, val_awayToPotion, locMap_val_awayMap]

theorem potionToMul_comp_awayToPotion (f : A) (S T : HomogeneousSubmonoid (intGrading 𝒜))
    (h : Submonoid.powers f ≤ S.toSubmonoid) :
    (S.potionToMul T).comp (awayToPotion 𝒜 f S h) =
      awayToPotion 𝒜 f (S * T) (h.trans (toSubmonoid_le_mul S T)) :=
  ringHom_ext_val fun z => by
    rw [RingHom.comp_apply, val_potionToMul, val_awayToPotion, val_awayToPotion,
      locMap_locMap]

theorem awayMap_potionToMul_square {e : ℕ} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (S T : HomogeneousSubmonoid (intGrading 𝒜))
    (hfS : Submonoid.powers f ≤ S.toSubmonoid)
    (hxST : Submonoid.powers x ≤ (S * T).toSubmonoid) :
    (awayToPotion 𝒜 x (S * T) hxST).comp (awayMap 𝒜 hg hx) =
      (S.potionToMul T).comp (awayToPotion 𝒜 f S hfS) := by
  rw [awayToPotion_comp_awayMap 𝒜 hg hx, potionToMul_comp_awayToPotion]

theorem awayEquivPotion_eq_awayToPotion (f : A) (S : HomogeneousSubmonoid (intGrading 𝒜))
    (hS : S.toSubmonoid = Submonoid.powers f) :
    (awayEquivPotion 𝒜 f S hS).toRingHom = awayToPotion 𝒜 f S (le_of_eq hS.symm) := by
  refine ringHom_ext_val fun z => ?_
  obtain ⟨y, rfl⟩ := mk_surjective z
  rfl

theorem awayEquivPotion_awayMap {e : ℕ} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (S T : HomogeneousSubmonoid (intGrading 𝒜))
    (hS : S.toSubmonoid = Submonoid.powers f)
    (hST : (S * T).toSubmonoid = Submonoid.powers x)
    (z : Away 𝒜 f) :
    awayEquivPotion 𝒜 x (S * T) hST (awayMap 𝒜 hg hx z) =
      S.potionToMul T (awayEquivPotion 𝒜 f S hS z) := by
  have h1 : (awayEquivPotion 𝒜 x (S * T) hST) (awayMap 𝒜 hg hx z) =
      awayToPotion 𝒜 x (S * T) (le_of_eq hST.symm) (awayMap 𝒜 hg hx z) :=
    congrArg (fun F => F (awayMap 𝒜 hg hx z))
      (awayEquivPotion_eq_awayToPotion 𝒜 x (S * T) hST)
  have h2 : (awayEquivPotion 𝒜 f S hS) z = awayToPotion 𝒜 f S (le_of_eq hS.symm) z :=
    congrArg (fun F => F z) (awayEquivPotion_eq_awayToPotion 𝒜 f S hS)
  rw [h1, h2]
  exact congrArg (fun F => F z)
    (awayMap_potionToMul_square 𝒜 hg hx S T (le_of_eq hS.symm) (le_of_eq hST.symm))

end Compare

end ProjGlueCompat
