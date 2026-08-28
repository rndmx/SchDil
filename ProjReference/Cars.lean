import Project.Dilatation.ReesAlgebra
import Project.Dilatation.Multicenter
import Project.Proj.Over
import Project.Proj.OfLE

import Project.Blowups.Bl
import Project.Blowups.UniqueBlowup
import Project.Blowups.PreClosAndClos

suppress_compilation

universe u
variable {A : Type (u+1)} [CommRing A]
variable {B : Type (u+1)} [CommRing B]
variable {ι : Type} [Fintype ι] (L : ι → Ideal A) [DecidableEq ι]
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

open GoodPotionIngredient AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multicenter

lemma RingEquiv.mem_nonZeroDivisors_map {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {a : R} (ha : a ∈ nonZeroDivisors R) : e a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * e a = 0 → x = 0 := by
    intro x hx
    have h := congrArg e.symm hx
    rw [map_mul, e.symm_apply_apply, map_zero] at h
    have := (mem_nonZeroDivisors_iff.1 ha).2 _ h
    simpa using congrArg e this
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

@[simps]
def BlMuAffineCover (A : CommRingCat) (L : ι → Ideal A) :
    Scheme.AffineCover (P := @IsOpenImmersion) (BlMu L) where
  J := Mu L
  obj P := CommRingCat.of ((map_index L P).Potion)
  map P := (glueData (τ := Mu L) (map_index L)).ι P
  f x := ((glueData (τ := Mu L) (map_index L)).ι_jointly_surjective x).choose
  covers x := ((glueData (τ := Mu L) (map_index L)).ι_jointly_surjective x).choose_spec
  map_prop P := inferInstance

set_option maxHeartbeats 1600000 in

def BlMuPreClos (A : CommRingCat) (L : ι → Ideal A) : PreClos (BlMu L) where
  indnumb := ι
  subscheme i := pullback ((loc_to_PreClos A L).subscheme i ↘ Spec A) (BlMu L ↘ Spec A)
  over i := ⟨pullback.snd _ _⟩
  cov := BlMuAffineCover A L
  ideal i P := Ideal.map (algebraMap A ((map_index L P).Potion)) (L i)
  condiso i P :=
    (loc_to_PreClos_baseChange A (CommRingCat.of ((map_index L P).Potion)) L).subscheme_iso i ≪≫
      (pullback.congrHom rfl (BlMu_ι_over A L P)).symm ≪≫
      (pullbackLeftPullbackSndIso ((loc_to_PreClos A L).subscheme i ↘ Spec A)
        (BlMu L ↘ Spec A) ((glueData (τ := Mu L) (map_index L)).ι P)).symm
  condover i P := by
    rw [Scheme.Hom.isOver_iff]
    show _ ≫ pullback.snd _ _ = _
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.congrHom_inv]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd]
    erw [pullback.lift_snd]
    simp only [Category.comp_id]
    exact ((loc_to_PreClos_baseChange A (CommRingCat.of ((map_index L P).Potion))
      L).subscheme_iso_over i).comp_over

lemma BlMuPreClos_IsPreCars (A : CommRingCat) (L : ι → Ideal A) :
    IsPreCars _ (BlMuPreClos A L) := by
  refine isPreCars_of_generators (BlMuPreClos A L)
      (fun i (P : Mu L) => (Mu_mor_iso L P).toRingEquiv
        (algebraMap A A[P.multicenter] (P.multicenter.elem (P.sec i)))) ?_ ?_
  · intro i (P : Mu L)
    have hLI : L i = P.multicenter.LargeIdeal (P.sec i) := by
      rw [P.cond (P.sec i), P.surj i]
    have h := Multicenter.Dilatation.image_elem_LargeIdeal_equal
      (F := P.multicenter) (Finsupp.single (P.sec i) 1)
    rw [familyPow_single, familyPow_single] at h
    have halg : (algebraMap A ((map_index L P).Potion)) =
        RingHom.comp (Mu_mor_iso L P).toRingEquiv.toRingHom
          (algebraMap A A[P.multicenter]) :=
      RingHom.ext fun a => ((Mu_mor_iso L P).commutes a).symm
    show Ideal.map (algebraMap A ((map_index L P).Potion)) (L i) = _
    rw [halg, ← Ideal.map_map, hLI, ← h, Ideal.map_span, Set.image_singleton]
    rfl
  · intro i (P : Mu L)
    refine RingEquiv.mem_nonZeroDivisors_map _ ?_
    have h := Multicenter.Dilatation.nonzerodiv_image
      (F := P.multicenter) (Finsupp.single (P.sec i) 1)
    rw [familyPow_single] at h
    exact h

lemma blowups_Cars (A : CommRingCat) (L : ι → Ideal A) :
    IsCars _ <|
      pullback_Clos (BlMu L ↘ (Spec (CommRingCat.of A))) (loc_to_Clos A L) :=

  ⟨⟨BlMuPreClos A L, BlMuPreClos_IsPreCars A L,
    Quotient.sound
      ⟨{ indnumb_equiv := Equiv.refl ι
         subscheme_iso := fun i => Iso.refl _
         subscheme_iso_over := fun i => by
           simp [Scheme.Hom.isOver_iff] }⟩⟩⟩

lemma open_of_blowup_IsCars (A : CommRingCat) (L : ι → Ideal A)
    {U : Scheme} [U.Over (Spec A)] (i : U ⟶ BlMu L) [IsOpenImmersion i]
    (hi : Scheme.Hom.IsOver i (Spec A)) :
    IsCars U (pullback_Clos (U ↘ Spec A) (loc_to_Clos A L)) := by
  haveI : AlgebraicGeometry.Flat i := inferInstance
  have h := pullback_IsCars U i _ (blowups_Cars A L)
  rw [← pullback_assoc, hi.comp_over] at h
  exact h

#exit
