import PartitionUnity

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open HomogeneousSubmonoid HomogeneousLocalization ChartBar PartitionUnity

namespace ChartCover

variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

def singleGen (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A}
    (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d) (hfS : f ∈ S) :
    PotionGen S (gen g ⟨d, hg⟩) where
  index := Unit
  elem := fun _ => g
  elem_mem := fun _ => mem_gen_self g ⟨d, hg⟩
  gen := by
    show Submonoid.closure (Set.range (fun _ : Unit => g)) = Submonoid.closure {g}
    congr 1
    ext x
    simp
  n := fun _ => 1
  s := fun _ => f
  s' := fun _ => 1
  s_mem_bar := fun _ => le_bar _ hfS
  s'_mem_bar := fun _ => one_mem _
  i := fun _ => d
  i' := fun _ => 0
  t_deg := fun _ => by simpa using hg
  s_deg := fun _ => hf
  s'_deg := fun _ => SetLike.GradedOne.one_mem

theorem singleGen_genSubmonoid (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A}
    (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d) (hfS : f ∈ S) :
    (singleGen S hg hf hfS).genSubmonoid =
      Submonoid.closure {frac S hg hf hfS} := by
  have key : ∀ t : Unit,
      S.equivBarPotion.symm (HomogeneousLocalization.mk
        { deg := (singleGen S hg hf hfS).i t,
          num := ⟨(singleGen S hg hf hfS).elem t ^ ((singleGen S hg hf hfS).n t : ℕ) *
            (singleGen S hg hf hfS).s' t, by
              simpa using SetLike.mul_mem_graded
                ((singleGen S hg hf hfS).t_deg t) ((singleGen S hg hf hfS).s'_deg t)⟩,
          den := ⟨(singleGen S hg hf hfS).s t, (singleGen S hg hf hfS).s_deg t⟩,
          den_mem := (singleGen S hg hf hfS).s_mem_bar t }) = frac S hg hf hfS := by
    intro t
    apply S.equivBarPotion.injective
    rw [RingEquiv.apply_symm_apply]
    simp only [frac, equivBarPotion_apply, toBarPotion_mk]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
    show Localization.mk (g ^ (1:ℕ) * 1) _ = _
    simp only [pow_one, mul_one]
    rfl
  show Submonoid.closure _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact Set.mem_singleton_iff.2 (key t)
  · rintro (rfl : x = _)
    exact ⟨(), (key ()).symm⟩

theorem singleGen_genSubmonoid_powers (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A}
    (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d) (hfS : f ∈ S) :
    (singleGen S hg hf hfS).genSubmonoid = Submonoid.powers (frac S hg hf hfS) := by
  rw [singleGen_genSubmonoid, Submonoid.powers_eq_closure]

theorem potionToMul_eq (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A}
    (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d) (hfS : f ∈ S) :
    (localizationToPotion (singleGen S hg hf hfS)).comp
        (algebraMap S.Potion (Localization (singleGen S hg hf hfS).genSubmonoid)) =
      S.potionToMul (gen g ⟨d, hg⟩) :=
  IsLocalization.lift_comp _

theorem exists_comap_eq (S : HomogeneousSubmonoid 𝒜) {d : ι} {g f : A}
    (hg : g ∈ 𝒜 d) (hf : f ∈ 𝒜 d) (hfS : f ∈ S)
    (p : Ideal S.Potion) [hp : p.IsPrime] (hfrac : frac S hg hf hfS ∉ p) :
    ∃ (q : Ideal (S * gen g ⟨d, hg⟩).Potion) (_ : q.IsPrime),
      Ideal.comap (S.potionToMul (gen g ⟨d, hg⟩)) q = p := by
  classical
  set T' := singleGen S hg hf hfS with hT'

  have hdisj : Disjoint (T'.genSubmonoid : Set S.Potion) (p : Set S.Potion) := by
    rw [hT', singleGen_genSubmonoid_powers]
    refine Set.disjoint_left.2 ?_
    rintro x ⟨n, rfl⟩ hx
    exact hfrac (hp.mem_of_pow_mem n hx)

  obtain ⟨p', hp'⟩ : (⟨p, hp⟩ : PrimeSpectrum S.Potion) ∈
      Set.range (PrimeSpectrum.comap
        (algebraMap S.Potion (Localization T'.genSubmonoid))) := by
    rw [PrimeSpectrum.localization_comap_range _ T'.genSubmonoid]
    exact hdisj

  refine ⟨Ideal.comap (localizationRingEquivPotion T').symm.toRingHom p'.asIdeal,
    Ideal.comap_isPrime _ _, ?_⟩
  have hid : (localizationRingEquivPotion T').symm.toRingHom.comp
      (localizationToPotion T') = RingHom.id _ := by
    ext x
    exact (localizationRingEquivPotion T').symm_apply_apply x
  have hcomp := potionToMul_eq S hg hf hfS
  have hkey : Ideal.comap (S.potionToMul (gen g ⟨d, hg⟩))
      (Ideal.comap (localizationRingEquivPotion T').symm.toRingHom p'.asIdeal) =
      Ideal.comap (algebraMap S.Potion (Localization T'.genSubmonoid)) p'.asIdeal := by
    rw [Ideal.comap_comap, ← hcomp, ← RingHom.comp_assoc, hid, RingHom.id_comp]
  rw [hkey]
  exact congrArg PrimeSpectrum.asIdeal hp'

theorem exists_summand_comap_eq {κ : Type*} (S : HomogeneousSubmonoid 𝒜) {d : ι} {f : A}
    (hf : f ∈ 𝒜 d) (hfS : f ∈ S) (J : Finset κ) (G : κ → A)
    (hG : ∀ j : κ, G j ∈ 𝒜 d) (hsum : ∑ j ∈ J, G j = f)
    (p : Ideal S.Potion) [hp : p.IsPrime] :
    ∃ j ∈ J, ∃ (q : Ideal (S * gen (G j) ⟨d, hG j⟩).Potion) (_ : q.IsPrime),
      Ideal.comap (S.potionToMul (gen (G j) ⟨d, hG j⟩)) q = p := by
  obtain ⟨j, hjJ, hj⟩ := exists_frac_notMem S hf hfS J G hG hsum p hp
  obtain ⟨q, hq, hqp⟩ := exists_comap_eq S (hG j) hf hfS p hj
  exact ⟨j, hjJ, q, hq, hqp⟩

end ChartCover
