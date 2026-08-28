import PreMultiCenter

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct Multicenter

namespace SchemeDilatation

variable {X : Scheme.{u+1}}

variable (X) in

def MultiCenter := Quotient (PreMultiCenter.relSetoid X)

namespace MultiCenter

variable (M : MultiCenter X)

noncomputable def rep : PreMultiCenter X := M.exists_rep.choose

theorem rep_eq : (Quotient.mk'' M.rep : MultiCenter X) = M := M.exists_rep.choose_spec

noncomputable def indnumb : Type := M.rep.indnumb

noncomputable def Y (M : MultiCenter X) : Clos X :=
  Quotient.lift (fun P => Quotient.mk'' P.Yrep)
    (fun _ _ h => by obtain ⟨R⟩ := h; exact Quotient.sound ⟨R.RY⟩) M

noncomputable def D (M : MultiCenter X) : Clos X :=
  Quotient.lift (fun P => Quotient.mk'' P.Drep)
    (fun _ _ h => by obtain ⟨R⟩ := h; exact Quotient.sound ⟨R.RD⟩) M

@[simp] theorem Y_mk (P : PreMultiCenter X) :
    MultiCenter.Y (Quotient.mk'' P) = P.Y := rfl

@[simp] theorem D_mk (P : PreMultiCenter X) :
    MultiCenter.D (Quotient.mk'' P) = P.D := rfl

theorem rep_Y : M.rep.Y = M.Y := by
  conv_rhs => rw [← M.rep_eq]
  exact (Y_mk M.rep).symm

theorem rep_D : M.rep.D = M.D := by
  conv_rhs => rw [← M.rep_eq]
  exact (D_mk M.rep).symm

end MultiCenter

end SchemeDilatation
