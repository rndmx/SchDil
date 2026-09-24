import ProjComparison

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open HomogeneousLocalization

namespace ProjOverlap

section CongrSubmonoid

variable {ι R A : Type*}
variable [AddCommMonoid ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

def congrSubmonoid {P Q : Submonoid A} (h : P = Q) :
    HomogeneousLocalization 𝒜 P ≃+* HomogeneousLocalization 𝒜 Q :=
  RingEquiv.ofHomInv
    (HomogeneousLocalization.map _ _ (RingHom.id _)
      (by subst h; erw [Submonoid.comap_id]) (fun _ _ ha => ha))
    (HomogeneousLocalization.map _ _ (RingHom.id _)
      (by subst h; erw [Submonoid.comap_id]) (fun _ _ ha => ha))
    (by ext z; induction z using Quotient.inductionOn' with | h z => rfl)
    (by ext z; induction z using Quotient.inductionOn' with | h z => rfl)

end CongrSubmonoid

section Main

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

variable {f g : A}

theorem powers_mul_le_mul :
    Submonoid.powers (f * g) ≤ Submonoid.powers f * Submonoid.powers g := by
  rintro _ ⟨k, rfl⟩
  exact Submonoid.mem_mul_iff.mpr ⟨f ^ k, ⟨k, rfl⟩, g ^ k, ⟨k, rfl⟩, (mul_pow f g k).symm⟩

theorem closure_pair_eq_mul (f g : A) :
    Submonoid.closure ({f, g} : Set A) = Submonoid.powers f * Submonoid.powers g := by
  have h : ({f, g} : Set A) = {f} ∪ {g} := Set.singleton_union.symm
  rw [h, Submonoid.closure_union_eq_mul, ← Submonoid.powers_eq_closure,
    ← Submonoid.powers_eq_closure]

theorem exists_pow_mul_pow {s : A} (hs : s ∈ Submonoid.powers f * Submonoid.powers g) :
    ∃ i j : ℕ, f ^ i * g ^ j = s := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := Submonoid.mem_mul_iff.mp hs
  exact ⟨i, j, rfl⟩

theorem pow_add_eq (i j : ℕ) :
    ((f * g) ^ (i + j) : A) = (f ^ i * g ^ j) * (f ^ j * g ^ i) := by
  rw [mul_pow, pow_add, pow_add]; ring

variable {m n : ℕ}

theorem pow_mul_pow_mem (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n) (j i : ℕ) :
    f ^ j * g ^ i ∈ 𝒜 (j * m + i * n) := by
  have h1 : f ^ j ∈ 𝒜 (j * m) := by
    simpa only [smul_eq_mul] using SetLike.pow_mem_graded j hf
  have h2 : g ^ i ∈ 𝒜 (i * n) := by
    simpa only [smul_eq_mul] using SetLike.pow_mem_graded i hg
  exact SetLike.mul_mem_graded h1 h2

def toMul : Away 𝒜 (f * g) →+*
    HomogeneousLocalization 𝒜 (Submonoid.powers f * Submonoid.powers g) :=
  HomogeneousLocalization.map _ _ (RingHom.id _)
    (by erw [Submonoid.comap_id]; exact powers_mul_le_mul) (fun _ _ ha => ha)

@[simp] theorem toMul_mk (c : NumDenSameDeg 𝒜 (Submonoid.powers (f * g))) :
    toMul 𝒜 (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk
        ⟨c.deg, c.num, c.den, powers_mul_le_mul c.den_mem⟩ := rfl

theorem toMul_injective : Function.Injective (toMul 𝒜 (f := f) (g := g)) := by
  intro z₁ z₂
  induction z₁ using Quotient.inductionOn' with | h y₁ =>
  induction z₂ using Quotient.inductionOn' with | h y₂ =>
  intro h
  have h' : (Localization.mk (y₁.num : A)
        ⟨(y₁.den : A), powers_mul_le_mul y₁.den_mem⟩ :
        Localization (Submonoid.powers f * Submonoid.powers g)) =
      Localization.mk (y₂.num : A) ⟨(y₂.den : A), powers_mul_le_mul y₂.den_mem⟩ :=
    congrArg HomogeneousLocalization.val h
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h'
  obtain ⟨⟨c, hc⟩, hcc⟩ := h'
  simp only at hcc
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow hc
  apply HomogeneousLocalization.val_injective
  show (Localization.mk (y₁.num : A) ⟨(y₁.den : A), y₁.den_mem⟩ :
      Localization (Submonoid.powers (f * g))) = Localization.mk _ _
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨(f * g) ^ (i + j), ⟨i + j, rfl⟩⟩, ?_⟩
  show ((f * g) ^ (i + j) : A) * ((y₂.den : A) * (y₁.num : A)) =
    ((f * g) ^ (i + j) : A) * ((y₁.den : A) * (y₂.num : A))
  calc ((f * g) ^ (i + j) : A) * ((y₂.den : A) * (y₁.num : A))
      = (f ^ j * g ^ i) * ((f ^ i * g ^ j) * ((y₂.den : A) * (y₁.num : A))) := by
        rw [pow_add_eq]; ring
    _ = (f ^ j * g ^ i) * ((f ^ i * g ^ j) * ((y₁.den : A) * (y₂.num : A))) := by rw [hcc]
    _ = ((f * g) ^ (i + j) : A) * ((y₁.den : A) * (y₂.num : A)) := by rw [pow_add_eq]; ring

theorem toMul_surjective (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n) :
    Function.Surjective (toMul 𝒜 (f := f) (g := g)) := by
  intro w
  induction w using Quotient.inductionOn' with | h y =>
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow y.den_mem
  have hden : ((f * g) ^ (i + j) : A) = (y.den : A) * (f ^ j * g ^ i) := by
    rw [pow_add_eq, hij]
  refine ⟨HomogeneousLocalization.mk
    ⟨y.deg + (j * m + i * n),
      ⟨(y.num : A) * (f ^ j * g ^ i),
        SetLike.mul_mem_graded y.num.2 (pow_mul_pow_mem 𝒜 hf hg j i)⟩,
      ⟨(f * g) ^ (i + j), by
        rw [hden]
        exact SetLike.mul_mem_graded y.den.2 (pow_mul_pow_mem 𝒜 hf hg j i)⟩,
      ⟨i + j, rfl⟩⟩, ?_⟩
  apply HomogeneousLocalization.val_injective
  show (Localization.mk ((y.num : A) * (f ^ j * g ^ i))
      ⟨((f * g) ^ (i + j) : A), powers_mul_le_mul ⟨i + j, rfl⟩⟩ :
      Localization (Submonoid.powers f * Submonoid.powers g)) =
    Localization.mk (y.num : A) ⟨(y.den : A), y.den_mem⟩
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  show (1 : A) * ((y.den : A) * ((y.num : A) * (f ^ j * g ^ i))) =
    (1 : A) * (((f * g) ^ (i + j) : A) * (y.num : A))
  rw [hden]; ring

def mulEquivAway (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n) :
    Away 𝒜 (f * g) ≃+*
      HomogeneousLocalization 𝒜 (Submonoid.powers f * Submonoid.powers g) :=
  RingEquiv.ofBijective (toMul 𝒜) ⟨toMul_injective 𝒜, toMul_surjective 𝒜 hf hg⟩

@[simp] theorem mulEquivAway_apply (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n)
    (z : Away 𝒜 (f * g)) : mulEquivAway 𝒜 hf hg z = toMul 𝒜 z := rfl

def closureEquivAway (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n) :
    HomogeneousLocalization 𝒜 (Submonoid.closure ({f, g} : Set A)) ≃+* Away 𝒜 (f * g) :=
  (congrSubmonoid 𝒜 (closure_pair_eq_mul f g)).trans (mulEquivAway 𝒜 hf hg).symm

end Main

section Potion

open ProjComparison HomogeneousSubmonoid

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {f g : A} {m n : ℕ}

def awayMulEquivPotionMul (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 n)
    (S T : HomogeneousSubmonoid (intGrading 𝒜))
    (hS : S.toSubmonoid = Submonoid.powers f)
    (hT : T.toSubmonoid = Submonoid.powers g) :
    Away 𝒜 (f * g) ≃+* (S * T).Potion :=
  (mulEquivAway 𝒜 hf hg).trans
    ((transportEquiv 𝒜 Nat.toIntHom (Submonoid.powers f * Submonoid.powers g)).trans
      (congrSubmonoid (intGrading 𝒜)
        (show (Submonoid.powers f * Submonoid.powers g) = (S * T).toSubmonoid by
          rw [HomogeneousSubmonoid.mul_toSubmonoid, hS, hT])))

end Potion

end ProjOverlap
