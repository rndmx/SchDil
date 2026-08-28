import PolyptychPaperForm
import MulticenterSpanEquiv

/-!
# The panel as the dilatation of the restricted datum -- ring level

Dubouloz-Mayeux, *A polyptych of multi-centered deformation spaces*, DEFINES the panel
`(𝔻_J)_i` as the multi-centered dilatation of the closed subscheme `X_i` with respect to
the **restricted deformation datum**

`(D_J, X_J)|_{X_i} = { (X_j ∩ X_i , (Σ_{s ∈ J≥j} D_s)|_{X_i}) }_{j ∈ J}`.

At ring level (`X = Spec A`, `X_i = Spec (A ⧸ M i)`) that datum is `resM`/`resd` below, and
this file proves that the panel really is its dilatation:

* `resM`, `resd` -- the restricted datum, and `comap_resM` : its `j`-th center is cut out by
  `M j + M i`, i.e. it is `X_j ∩ X_i`.
* `panelCodomEquiv` -- the codomain of `F_J(i)^*` **is** `R_J` of the restricted datum.
  (It is the dilatation of the restricted datum on the nose except for the distinguished
  elements, which differ by `map_prod`; `Multicenter.spanEquiv` bridges that.)
* `panelKerEquiv`, `panelQuotEquiv`, `panelSubQuotEquiv`, `paperQuotEquiv` -- the panel,
  cut out of `R_J` by `ker(F_J(i)^*)` / `kerFracIdeal` / `panelSubIdeal` / `paperIdeal`,
  **is** `R_J` of the restricted datum.  These are the first-isomorphism-theorem packagings
  of `panelHom_surjective` together with each of the kernel computations.
* `panelSubQuotEquiv_mk` -- the identification is the one induced by `F_J(i)^*`, not some
  other isomorphism.

So at ring level the paper's *definition* of the panel and this development's
*characterisation* of it by an ideal agree, and the agreement is exhibited, not merely
implicit.
-/

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

/-- The centers of the datum restricted to `X i = Spec (A ⧸ M i)`: the image of `M j`,
which cuts out `X_j ∩ X_i` inside `X_i`. -/
noncomputable abbrev resM (i : I) : I → Ideal (A ⧸ M i) :=
  fun j => Ideal.map (Ideal.Quotient.mk (M i)) (M j)

/-- The divisor equations of the datum restricted to `X i`. -/
noncomputable abbrev resd (i : I) : I → (A ⧸ M i) :=
  fun s => Ideal.Quotient.mk (M i) (d s)

/-- The `j`-th center of the restricted datum is `X_j ∩ X_i`: it is cut out of `A` by
`M j + M i`. -/
theorem comap_resM (i j : I) :
    Ideal.comap (Ideal.Quotient.mk (M i)) (resM M i j) = M j ⊔ M i := by
  show Ideal.comap (Ideal.Quotient.mk (M i))
    (Ideal.map (Ideal.Quotient.mk (M i)) (M j)) = M j ⊔ M i
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

variable {M d}

/-- The distinguished elements of `quotCenter` and of the restricted datum generate the
same ideals: they differ only by `map_prod`. -/
theorem restCenter_quot_span (J : Finset I) (i : I) (j : (restCenter M d J).index) :
    Ideal.span {elemOf (resd M d i) J j.1} =
      Ideal.span {((restCenter M d J).quotCenter (M i)).elem j} := by
  simp only [elemOf, Multicenter.quotCenter_elem, restCenter_elem, map_prod]

/-- **The codomain of `F_J(i)^*` is `R_J` of the restricted datum on `X i`.** -/
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

/-- **The panel is the dilatation of the restricted datum**, with the panel written as
`R_J ⧸ ker(F_J(i)^*)`. -/
noncomputable def panelKerEquiv (hC : Cartier M d) (J : Finset I) (i : I) :
    (Ring M d J ⧸ RingHom.ker (panelHom M d hC J i)) ≃ₐ[A]
      Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientKerAlgEquivOfSurjective
    (panelHom_surjective M d hC J i)).trans ((panelCodomEquiv J i).restrictScalars A)

/-- **The panel is the dilatation of the restricted datum**, with the panel written as
`R_J ⧸ kerFracIdeal` (the form of `propnoyauappendix`). -/
noncomputable def panelQuotEquiv (hC : Cartier M d) (J : Finset I) (i : I) :
    (Ring M d J ⧸ (restCenter M d J).kerFracIdeal (M i)) ≃ₐ[A]
      Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (ker_panelHom M d hC J i).symm).trans
    (panelKerEquiv hC J i)

/-- **The panel is the dilatation of the restricted datum**, with the panel written as the
`panelSubIdeal` used throughout this development. -/
noncomputable def panelSubQuotEquiv (hC : Cartier M d) (hM : Mono M) (J : Finset I)
    (i : I) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    (Ring M d J ⧸ panelSubIdeal M d J i) ≃ₐ[A] Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (ker_panelHom_eq hC hM J i hiJ hR1 hR2).symm).trans
    (panelKerEquiv hC J i)

/-- The identification of the panel with the dilatation of the restricted datum is the one
induced by `F_J(i)^*`. -/
@[simp] theorem panelSubQuotEquiv_mk (hC : Cartier M d) (hM : Mono M) (J : Finset I)
    (i : I) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i)
    (x : Ring M d J) :
    panelSubQuotEquiv hC hM J i hiJ hR1 hR2 (Ideal.Quotient.mk _ x) =
      panelCodomEquiv J i (panelHom M d hC J i x) := by
  simp only [panelSubQuotEquiv, panelKerEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_apply,
    AlgEquiv.restrictScalars_apply]
  exact congrArg _ (RingHom.kerLift_mk _ x)

/-- **The panel is the dilatation of the restricted datum**, with the panel written as the
paper's ideal `paperIdeal` of `lem:KerfJi-inclusion`.  This is the ring-level form of
`(𝔻_J)_i = 𝔻((D_J, X_J)|_{X_i} / X_i)`. -/
noncomputable def paperQuotEquiv (hC : Cartier M d) (hM : Mono M) (J : Finset I)
    (i : I) (hiJ : i ∉ J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    (Ring M d J ⧸ paperIdeal M d J i) ≃ₐ[A] Ring (resM M i) (resd M d i) J :=
  (Ideal.quotientEquivAlgOfEq A (paperIdeal_eq_panelSubIdeal M d hM J i)).trans
    (panelSubQuotEquiv hC hM J i hiJ hR1 hR2)

end Polyptych
