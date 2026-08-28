import MulticenterRing

/-!
# Non-zero-divisors survive a multicenter dilatation

The dilatation `A[F]` of a ring `A` along a multicenter `F` is a quotient of a subring of
a localisation, so a priori a non-zero-divisor of `A` could acquire a zero-divisor image.
It does not: `nonzerodiv_of_nonzerodiv` shows the algebra map `A → A[F]` sends
non-zero-divisors to non-zero-divisors.

This complements `Multicenter.Dilatation.nonzerodiv_image`, which says the same for the
distinguished elements `F.elem ^ v` (which are *not* assumed to be non-zero-divisors in
`A`, and become ones only after dilating).

Geometrically this is the statement that a dilatation does not destroy Cartier divisors
already present on the base — the ingredient needed for the tower formula
[Ma23d, Prop. 2.22], where the divisors indexed by `J` must stay Cartier after further
dilating along the divisors indexed by `K`.
-/

suppress_compilation

universe u

namespace Multicenter

section semiring

variable {A : Type _} [CommSemiring A] {F : Multicenter A}

namespace Dilatation

/-- The image in `A[F]` of a non-zero-divisor of `A` is a non-zero-divisor. -/
lemma nonzerodiv_of_nonzerodiv {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap A A[F] a ∈ nonZeroDivisors A[F] := by
  simp only [nonZeroDivisors, Submonoid.mem_inf, mem_nonZeroDivisorsLeft_iff, mul_comm,
    mem_nonZeroDivisorsRight_iff, and_self]
  intro x h
  induction x using induction_on with | h x =>
  simp only [algebraMap_apply, mk_mul_mk, zero_def, mk_eq_mk] at h
  rcases h with ⟨α, hα⟩
  simp only [mul'_num, add_zero, mul'_pow, zero_mul] at hα
  simp only [zero_def, mk_eq_mk]
  refine ⟨α, ?_⟩
  simp only [add_zero, zero_mul]
  refine (mem_nonZeroDivisors_iff.mp ha).1 _ ?_
  rw [← mul_assoc, mul_comm a x.num]
  exact hα

end Dilatation

end semiring

end Multicenter
