import MulticenterShift

suppress_compilation

universe u

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] {ι : Type} (M : ι → Ideal A) (a : A)
  (s : ι → ℕ) (i₀ : ι)

theorem ofPowers_nzd
    (hcar : Ideal.Quotient.mk (M i₀) a ∈ nonZeroDivisors (A ⧸ M i₀))
    (i : ι) :
    Ideal.Quotient.mk ((ofPowers M a s).ideal i₀)
      ((ofPowers M a s).elem i) ∈
      nonZeroDivisors (A ⧸ (ofPowers M a s).ideal i₀) := by
  simpa [ofPowers, map_pow] using pow_mem hcar (s i)

noncomputable def fact51Hom (hsub : ∀ i, M i ≤ M i₀)
    (hcar : Ideal.Quotient.mk (M i₀) a ∈ nonZeroDivisors (A ⧸ M i₀)) :
    A[ofPowers M a s] →ₐ[A] A ⧸ M i₀ :=
  (ofPowers M a s).descTo i₀ hsub (ofPowers_nzd M a s i₀ hcar)

theorem fact51_ker (hsub : ∀ i, M i ≤ M i₀)
    (hcar : Ideal.Quotient.mk (M i₀) a ∈ nonZeroDivisors (A ⧸ M i₀)) :
    RingHom.ker (fact51Hom M a s i₀ hsub hcar) =
      (ofPowers M a s).genFracIdeal :=
  (ofPowers M a s).ker_descTo i₀ hsub (ofPowers_nzd M a s i₀ hcar)


theorem fact51_ker_asis [Fintype ι]
    (hsub : ∀ i, M i ≤ M i₀)
    (hcar : ∀ i, Ideal.Quotient.mk (M i) a ∈ nonZeroDivisors (A ⧸ M i)) :
    RingHom.ker (fact51Hom M a s i₀ hsub (hcar i₀)) =
      (ofPowers M a s).genFracIdeal :=
  fact51_ker M a s i₀ hsub (hcar i₀)

noncomputable def powersShiftEquiv_asis [Fintype ι] (t : ℕ)
    (hsub : ∀ i, M i ≤ M i₀)
    (hcar : ∀ i, Ideal.Quotient.mk (M i) a ∈ nonZeroDivisors (A ⧸ M i))
    (ht : t ≤ s i₀) :
    (A[ofPowers M a s])[(ofPowers M a s).secondStage (a ^ t)] ≃ₐ[A]
      A[ofPowers M a (fun i => s i + t)] :=
  powersShiftEquiv M a s t i₀

end Multicenter
