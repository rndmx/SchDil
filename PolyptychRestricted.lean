import PolyptychKernelFormula
import MulticenterSpanEquiv

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

noncomputable abbrev resM (i : I) : I → Ideal (A ⧸ M i) :=
  fun j => Ideal.map (Ideal.Quotient.mk (M i)) (M j)

noncomputable abbrev resd (i : I) : I → (A ⧸ M i) :=
  fun s => Ideal.Quotient.mk (M i) (d s)

theorem comap_resM (i j : I) :
    Ideal.comap (Ideal.Quotient.mk (M i)) (resM M i j) = M j ⊔ M i := by
  show Ideal.comap (Ideal.Quotient.mk (M i))
    (Ideal.map (Ideal.Quotient.mk (M i)) (M j)) = M j ⊔ M i
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

variable {M d}

theorem restCenter_quot_span (J : Finset I) (i : I) (j : (restCenter M d J).index) :
    Ideal.span {elemOf (resd M d i) J j.1} =
      Ideal.span {((restCenter M d J).quotCenter (M i)).elem j} := by
  simp only [elemOf, Multicenter.quotCenter_elem, restCenter_elem, map_prod]

noncomputable def panelCodomEquiv (J : Finset I) (i : I) :
    (A ⧸ M i)[(restCenter M d J).quotCenter (M i)] ≃ₐ[A ⧸ M i]
      Ring (resM M i) (resd M d i) J :=
  Multicenter.spanEquiv ((restCenter M d J).quotCenter (M i))
    (fun j : (restCenter M d J).index => elemOf (resd M d i) J j.1)
    (restCenter_quot_span J i)

local instance instTowerQuot (J : Finset I) (i : I) :
    IsScalarTower A (A ⧸ M i) ((A ⧸ M i)[(restCenter M d J).quotCenter (M i)]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance instTowerRes (J : Finset I) (i : I) :
    IsScalarTower A (A ⧸ M i) (Ring (resM M i) (resd M d i) J) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable def panelKerEquiv (J : Finset I) (i : I) :
    (Ring M d J ⧸ RingHom.ker (panelHom M d J i)) ≃ₐ[A]
      Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientKerAlgEquivOfSurjective
    (panelHom_surjective M d J i)).trans ((panelCodomEquiv J i).restrictScalars A)

noncomputable def panelQuotEquiv (J : Finset I) (i : I) (hCi : CartierAt M d J i) :
    (Ring M d J ⧸ (restCenter M d J).kerFracIdeal (M i)) ≃ₐ[A]
      Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (ker_panelHom M d hCi).symm).trans
    (panelKerEquiv J i)

noncomputable def panelSubQuotEquiv (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    (Ring M d J ⧸ panelSubIdeal M d J i) ≃ₐ[A] Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (ker_panelHom_eq J i hCi hM hiJ hR1 hR2).symm).trans
    (panelKerEquiv J i)

@[simp] theorem panelSubQuotEquiv_mk (J : Finset I) (i : I) (hCi : CartierAt M d J i)
    (hM : Mono M) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i)
    (x : Ring M d J) :
    panelSubQuotEquiv J i hCi hM hiJ hR1 hR2 (Ideal.Quotient.mk _ x) =
      panelCodomEquiv J i (panelHom M d J i x) := by
  simp only [panelSubQuotEquiv, panelKerEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_apply,
    AlgEquiv.restrictScalars_apply]
  exact congrArg _ (RingHom.kerLift_mk _ x)

end Polyptych
