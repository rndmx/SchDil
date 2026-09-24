import MulticenterQuotient
import MulticenterSingleDivisor

suppress_compilation

universe u

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)
  [Unique F.index]

local notation "u₀" => (default : F.index)

noncomputable def cor240_phi
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    A[F.multiple (fun _ => 1)] →ₐ[A] A ⧸ F.ideal u₀ :=
  F.descQuot (fun _ => 1) hb

theorem cor240_ker
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    RingHom.ker (F.cor240_phi hb) = F.liftIdeal (fun _ => 1) u₀ :=
  F.ker_descQuot (fun _ => 1) hb

noncomputable def cor240_step (k d : ℕ) :
    (A[F.multiple (fun _ => k)])[F.iterated (fun _ => k) (fun _ => d)]
      ≃ₐ[A] A[F.multiple (fun _ => k + d)] :=
  F.iterateEquiv (fun _ => k) (fun _ => d)


theorem sub_of_unique : ∀ i, F.ideal i ≤ F.ideal u₀ :=
  fun i => le_of_eq (by rw [Unique.eq_default i])

theorem nzd_of_unique
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    ∀ i, Ideal.Quotient.mk (F.ideal u₀) (F.elem i) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀) :=
  fun i => by rw [Unique.eq_default i]; exact hb

noncomputable def cor240_map
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    A[F] →ₐ[A] A ⧸ F.ideal u₀ :=
  F.descTo u₀ (F.sub_of_unique) (F.nzd_of_unique hb)

theorem cor240_map_unique
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀))
    (χ : A[F] →ₐ[A] A ⧸ F.ideal u₀) : χ = F.cor240_map hb :=
  F.lemma_exists_unique_morphism' (F.descTo_nzd u₀ (F.nzd_of_unique hb))
    (F.descTo_gen u₀ (F.sub_of_unique)) χ _

theorem cor240_map_ker
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    RingHom.ker (F.cor240_map hb) = F.genFracIdeal :=
  F.ker_descTo u₀ (F.sub_of_unique) (F.nzd_of_unique hb)


section Step

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) [Unique F.index]
  (ν : F.index → ℕ)

theorem multiple_nzd
    (hb : Ideal.Quotient.mk (F.ideal (default : F.index))
      (F.elem default) ∈
      nonZeroDivisors (A ⧸ F.ideal (default : F.index))) :
    Ideal.Quotient.mk
        ((F.multiple ν).ideal (default : (F.multiple ν).index))
        ((F.multiple ν).elem default) ∈
      nonZeroDivisors (A ⧸ (F.multiple ν).ideal (default : (F.multiple ν).index)) := by
  show Ideal.Quotient.mk (F.ideal (default : F.index))
    (F.elem (default : F.index) ^ ν default) ∈ _
  rw [map_pow]
  exact pow_mem hb _

theorem liftIdeal_eq_genFracIdeal
    (hb : Ideal.Quotient.mk (F.ideal (default : F.index))
      (F.elem default) ∈
      nonZeroDivisors (A ⧸ F.ideal (default : F.index))) :
    F.liftIdeal ν (default : F.index) = (F.multiple ν).genFracIdeal := by
  have heq : F.descQuot ν hb = (F.multiple ν).cor240_map (F.multiple_nzd ν hb) :=
    (F.multiple ν).lemma_exists_unique_morphism'
      (F.descQuot_nzd ν hb) (F.descQuot_gen ν) _ _
  rw [← F.ker_descQuot ν hb, heq,
    (F.multiple ν).cor240_map_ker (F.multiple_nzd ν hb)]

theorem cor240_step_center (k d : ℕ)
    (hb : Ideal.Quotient.mk (F.ideal (default : F.index))
      (F.elem default) ∈
      nonZeroDivisors (A ⧸ F.ideal (default : F.index))) :
    (F.iterated (fun _ => k) (fun _ => d)).ideal (default : F.index) =
      RingHom.ker ((F.multiple (fun _ => k)).cor240_map
        (F.multiple_nzd (fun _ => k) hb)) := by
  rw [(F.multiple (fun _ => k)).cor240_map_ker (F.multiple_nzd (fun _ => k) hb),
    ← F.liftIdeal_eq_genFracIdeal (fun _ => k) hb]
  rfl

end Step

end Multicenter
