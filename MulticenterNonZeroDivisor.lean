import Project.Dilatation.Multicenter

suppress_compilation

universe u

namespace Multicenter

section semiring

variable {A : Type _} [CommSemiring A] {F : Multicenter A}

namespace Dilatation

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
