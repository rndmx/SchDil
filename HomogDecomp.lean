import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Operations

suppress_compilation

set_option linter.unusedSectionVars false

universe u

open DirectSum

namespace HomogDecomp

variable {ι R₀ A : Type*} [AddCommGroup ι] [DecidableEq ι] [CommRing R₀] [CommRing A]
variable [Algebra R₀ A] (𝒜 : ι → Submodule R₀ A) [GradedAlgebra 𝒜]

theorem exists_homogeneous_decomposition {d e : ι} {f : A} (hf : f ∈ 𝒜 d)
    (T : Set A) (hT : ∀ t ∈ T, t ∈ 𝒜 e) (hspan : f ∈ Ideal.span T) :
    ∃ (K : Finset A) (c : A → A), (↑K ⊆ T) ∧ (∀ m, c m ∈ 𝒜 (d - e)) ∧
      f = ∑ m ∈ K, c m * m := by
  classical
  obtain ⟨r, hrT, hrf⟩ := Submodule.mem_span_set.1 hspan
  refine ⟨r.support, fun m => GradedRing.proj 𝒜 (d - e) (r m), hrT, fun m => ?_, ?_⟩
  · exact SetLike.coe_mem _
  · have hfd : GradedRing.proj 𝒜 d f = f := by
      rw [GradedRing.proj_apply, decompose_of_mem_same 𝒜 hf]
    calc f = GradedRing.proj 𝒜 d f := hfd.symm
    _ = GradedRing.proj 𝒜 d (∑ m ∈ r.support, r m • m) := by
          rw [← hrf]; rfl
    _ = ∑ m ∈ r.support, GradedRing.proj 𝒜 d (r m * m) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [smul_eq_mul]
    _ = ∑ m ∈ r.support, GradedRing.proj 𝒜 (d - e) (r m) * m := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hme : m ∈ 𝒜 e := hT m (hrT hm)
          conv_lhs => rw [show d = (d - e) + e from by abel]
          rw [GradedRing.proj_apply, coe_decompose_mul_add_of_right_mem 𝒜 hme,
            ← GradedRing.proj_apply]

end HomogDecomp
