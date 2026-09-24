import Project.Proj.Construction
import Project.Grading.Injection
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousSubmonoid

namespace ProjComparison

section Transport

variable {ι ι' R A : Type*}
variable [AddCommMonoid ι] [DecidableEq ι] [AddCommMonoid ι'] [DecidableEq ι']
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (ρ : ι →+ ι') [inj : Fact (Function.Injective ρ)]
variable [∀ i : ι', Decidable (i ∈ Set.range ρ)]

theorem rangeSplitting_ρ (n : ι) :
    Set.rangeSplitting ρ ⟨ρ n, ⟨n, rfl⟩⟩ = n :=
  inj.out (Set.apply_rangeSplitting _ _)

theorem gradingOfInjection_apply_ρ (n : ι) :
    gradingOfInjection 𝒜 ρ (ρ n) = 𝒜 n := by
  delta gradingOfInjection
  rw [dif_pos ⟨n, rfl⟩, rangeSplitting_ρ ρ n]

theorem gradingOfInjection_apply_not_mem {m : ι'} (hm : m ∉ Set.range ρ) :
    gradingOfInjection 𝒜 ρ m = ⊥ := by
  delta gradingOfInjection
  rw [dif_neg hm]

variable (x : Submonoid A)

def transportNumDen (y : NumDenSameDeg 𝒜 x) :
    NumDenSameDeg (gradingOfInjection 𝒜 ρ) x where
  deg := ρ y.deg
  num := ⟨y.num, by rw [gradingOfInjection_apply_ρ 𝒜 ρ]; exact y.num.2⟩
  den := ⟨y.den, by rw [gradingOfInjection_apply_ρ 𝒜 ρ]; exact y.den.2⟩
  den_mem := y.den_mem

@[simp] theorem transportNumDen_num (y : NumDenSameDeg 𝒜 x) :
    ((transportNumDen 𝒜 ρ x y).num : A) = (y.num : A) := rfl

@[simp] theorem transportNumDen_den (y : NumDenSameDeg 𝒜 x) :
    ((transportNumDen 𝒜 ρ x y).den : A) = (y.den : A) := rfl

theorem val_mk_transport (y : NumDenSameDeg 𝒜 x) :
    (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x y)).val =
      (HomogeneousLocalization.mk y).val := by
  rw [val_mk, val_mk]
  rfl

def transport :
    HomogeneousLocalization 𝒜 x →+*
      HomogeneousLocalization (gradingOfInjection 𝒜 ρ) x where
  toFun := Quotient.lift (fun y => HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x y))
    (by
      intro a b h
      apply HomogeneousLocalization.val_injective
      rw [val_mk_transport, val_mk_transport]
      exact congrArg HomogeneousLocalization.val (Quotient.sound h))
  map_one' := by
    apply HomogeneousLocalization.val_injective
    show (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x 1)).val = _
    rw [val_mk_transport]
    simp
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn' with | h a =>
    induction b using Quotient.inductionOn' with | h b =>
    apply HomogeneousLocalization.val_injective
    show (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x (a * b))).val = _
    rw [val_mk_transport]
    rw [val_mul]
    show _ = (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x a)).val *
      (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x b)).val
    rw [val_mk_transport, val_mk_transport, ← val_mul]
    rfl
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    show (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x 0)).val = _
    rw [val_mk_transport]
    simp
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn' with | h a =>
    induction b using Quotient.inductionOn' with | h b =>
    apply HomogeneousLocalization.val_injective
    show (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x (a + b))).val = _
    rw [val_mk_transport]
    rw [val_add]
    show _ = (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x a)).val +
      (HomogeneousLocalization.mk (transportNumDen 𝒜 ρ x b)).val
    rw [val_mk_transport, val_mk_transport, ← val_add]
    rfl

@[simp] theorem val_transport (z : HomogeneousLocalization 𝒜 x) :
    (transport 𝒜 ρ x z).val = z.val := by
  induction z using Quotient.inductionOn' with | h z =>
  exact val_mk_transport 𝒜 ρ x z

theorem transport_injective : Function.Injective (transport 𝒜 ρ x) := by
  intro a b h
  apply HomogeneousLocalization.val_injective
  rw [← val_transport 𝒜 ρ x a, ← val_transport 𝒜 ρ x b, h]

theorem transport_surjective : Function.Surjective (transport 𝒜 ρ x) := by
  intro w
  induction w using Quotient.inductionOn' with | h w =>
  obtain ⟨d, ⟨na, hna⟩, ⟨da, hda⟩, den_mem⟩ := w
  by_cases hm : d ∈ Set.range ρ
  · obtain ⟨n, rfl⟩ := hm
    rw [gradingOfInjection_apply_ρ 𝒜 ρ] at hna hda
    refine ⟨HomogeneousLocalization.mk ⟨n, ⟨na, hna⟩, ⟨da, hda⟩, den_mem⟩, ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [val_transport, val_mk]
    show _ = (HomogeneousLocalization.mk
      (⟨ρ n, ⟨na, by rwa [gradingOfInjection_apply_ρ 𝒜 ρ]⟩,
        ⟨da, by rwa [gradingOfInjection_apply_ρ 𝒜 ρ]⟩, den_mem⟩ :
        NumDenSameDeg (gradingOfInjection 𝒜 ρ) x)).val
    rw [val_mk]
  · rw [gradingOfInjection_apply_not_mem 𝒜 ρ hm] at hda
    have hbot : da = 0 := by simpa using hda
    have h0 : (0 : A) ∈ x := hbot ▸ den_mem
    have : Subsingleton (HomogeneousLocalization (gradingOfInjection 𝒜 ρ) x) :=
      HomogeneousLocalization.subsingleton _ h0
    exact ⟨0, Subsingleton.elim _ _⟩

theorem transport_bijective : Function.Bijective (transport 𝒜 ρ x) :=
  ⟨transport_injective 𝒜 ρ x, transport_surjective 𝒜 ρ x⟩

def transportEquiv :
    HomogeneousLocalization 𝒜 x ≃+*
      HomogeneousLocalization (gradingOfInjection 𝒜 ρ) x :=
  RingEquiv.ofBijective (transport 𝒜 ρ x) (transport_bijective 𝒜 ρ x)

@[simp] theorem val_transportEquiv (z : HomogeneousLocalization 𝒜 x) :
    (transportEquiv 𝒜 ρ x z).val = z.val := val_transport 𝒜 ρ x z

end Transport

namespace Nat

abbrev toIntHom : ℕ →+ ℤ := Nat.castAddMonoidHom ℤ

instance : Fact (Function.Injective toIntHom) := ⟨fun a b h => by simpa using h⟩

noncomputable instance (i : ℤ) : Decidable (i ∈ Set.range toIntHom) := Classical.dec _

end Nat

section MathlibProj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

noncomputable abbrev intGrading : ℤ → Submodule R A :=
  gradingOfInjection 𝒜 Nat.toIntHom

noncomputable def awayEquivPotion (f : A)
    (S : HomogeneousSubmonoid (intGrading 𝒜))
    (hS : S.toSubmonoid = Submonoid.powers f) :
    Away 𝒜 f ≃+* S.Potion :=
  (transportEquiv 𝒜 Nat.toIntHom (Submonoid.powers f)).trans
    (RingEquiv.ofHomInv
      (HomogeneousLocalization.map _ _ (RingHom.id _)
        (by rw [hS]; erw [Submonoid.comap_id])
        (fun i a ha => ha))
      (HomogeneousLocalization.map _ _ (RingHom.id _)
        (by rw [hS]; erw [Submonoid.comap_id])
        (fun i a ha => ha))
      (by ext z; induction z using Quotient.inductionOn' with | h z => rfl)
      (by ext z; induction z using Quotient.inductionOn' with | h z => rfl))

end MathlibProj

section Degrees

variable {ι : Type*} {R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A]
variable [Algebra R A]
variable (𝒩 : (ι →₀ ℕ) → Submodule R A) [GradedAlgebra 𝒩]

local notation "ρ" => ρNatToInt ι

variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

def coordHom (i : ι) : (ι →₀ ℤ) →+ ℤ := Finsupp.applyAddHom i

theorem coordHom_surjective (i : ι) : Function.Surjective (coordHom (ι := ι) i) :=
  fun n => ⟨Finsupp.single i n, by simp [coordHom]⟩

theorem coordKer_not_finiteIndex (i : ι) :
    ¬ (coordHom (ι := ι) i).ker.FiniteIndex := by
  intro h
  have e : ((ι →₀ ℤ) ⧸ (coordHom (ι := ι) i).ker) ≃+ ℤ :=
    QuotientAddGroup.quotientKerEquivOfSurjective _ (coordHom_surjective (ι := ι) i)
  have hinf : Infinite ((ι →₀ ℤ) ⧸ (coordHom (ι := ι) i).ker) :=
    Infinite.of_injective e.symm e.symm.injective
  exact h.index_ne_zero (AddSubgroup.index_eq_zero_iff_infinite.mpr hinf)

theorem not_finiteIndex_of_le {H K : AddSubgroup (ι →₀ ℤ)} (hle : H ≤ K)
    (hK : ¬ K.FiniteIndex) : ¬ H.FiniteIndex := fun _ =>
  hK (AddSubgroup.finiteIndex_of_le (H := H) hle)

theorem mem_range_of_ne_zero {d : ι →₀ ℤ} {a : A}
    (ha : a ∈ gradingOfInjection 𝒩 ρ d) (ha0 : a ≠ 0) : d ∈ Set.range ρ := by
  by_contra hd
  rw [gradingOfInjection_apply_not_mem 𝒩 ρ hd] at ha
  exact ha0 (by simpa using ha)

theorem coord_nonneg_of_ne_zero {d : ι →₀ ℤ} {a : A}
    (ha : a ∈ gradingOfInjection 𝒩 ρ d) (ha0 : a ≠ 0) (i : ι) : 0 ≤ d i := by
  obtain ⟨v, rfl⟩ := mem_range_of_ne_zero 𝒩 ha ha0
  simp [ρNatToInt]

theorem coord_pos_of_elemIsRelevant
    {d : ι →₀ ℤ} {a : A}
    (ha : SetLike.IsHomogeneousElem (gradingOfInjection 𝒩 ρ) a)
    (had : a ∈ gradingOfInjection 𝒩 ρ d)
    (hrel : ElemIsRelevant a ha)
    (hnil : ∀ k : ℕ, a ^ k ≠ 0) (i : ι) : 0 < d i := by
  classical
  obtain ⟨n, x, deg, mem, hfin, k, hprod⟩ :=
    (elemIsRelevant_iff (𝒜 := gradingOfInjection 𝒩 ρ) a ha).1 hrel

  have hx0 : ∀ j, x j ≠ 0 := by
    intro j hj
    exact hnil k (by rw [← hprod, Finset.prod_eq_zero (Finset.mem_univ j) hj])

  have hdeg_nonneg : ∀ j, 0 ≤ (deg j) i :=
    fun j => coord_nonneg_of_ne_zero 𝒩 (mem j) (hx0 j) i

  have hsum : a ^ k ∈ gradingOfInjection 𝒩 ρ (∑ j : Fin n, deg j) := by
    rw [← hprod]
    exact SetLike.prod_mem_graded _ _ _ (fun j _ => mem j)
  have hpow : a ^ k ∈ gradingOfInjection 𝒩 ρ (k • d) :=
    SetLike.pow_mem_graded _ had
  have hdeq : (∑ j : Fin n, deg j) = k • d :=
    DirectSum.degree_eq_of_mem_mem _ hsum hpow (hnil k)

  by_contra hle
  push_neg at hle
  have ha0 : a ≠ 0 := by simpa using hnil 1
  have hd0 : d i = 0 := le_antisymm hle (coord_nonneg_of_ne_zero 𝒩 had ha0 i)
  have hzero : ∀ j, (deg j) i = 0 := by
    have hsum0 : ∑ j : Fin n, (deg j) i = 0 := by
      have := congrArg (fun c => c i) hdeq
      simpa [hd0, Finsupp.coe_finset_sum] using this
    intro j
    exact le_antisymm
      (Finset.single_le_sum (fun j _ => hdeg_nonneg j) (Finset.mem_univ j) |>.trans_eq hsum0)
      (hdeg_nonneg j)

  haveI : (AddSubgroup.closure (Set.range deg)).FiniteIndex := hfin
  refine coordKer_not_finiteIndex (ι := ι) i
    (AddSubgroup.finiteIndex_of_le (H := AddSubgroup.closure (Set.range deg)) ?_)
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨j, rfl⟩
  simpa [coordHom, AddMonoidHom.mem_ker] using hzero j

end Degrees

end ProjComparison
