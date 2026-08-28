import MulticenterQuotient

/-!
# The exceptional quotient of a general mono-centered dilatation

`MulticenterQuotient.lean` proves the exceptional-quotient results of [Ma24, Cor. 2.40]
for the multiple `[M, b^v]` of a mono-centered multicenter `[M, b]`.  This file removes
the "multiple" shape: for an arbitrary mono-centered multicenter `G = [M, e]` over `A`
(index type `Unique`) such that the class of `e` is a non-zero-divisor in `A/M`,

* `exceptIdeal` -- the colon ideal `(M·A[G] : e) ⊆ A[G]`;
* `descQuotE : A[G] →ₐ[A] A/M` -- the universal-property map;
* `ker_descQuotE` -- `ker(descQuotE) = exceptIdeal`;
* `exceptQuotEquiv` -- `A[G] ⧸ exceptIdeal ≃ₐ[A] A/M`.

The proofs are those of `MulticenterQuotient.lean` verbatim with `b^v` replaced by `e`
(the shape `elem = power` was never used, only `mk e` being a non-zero-divisor).  The
general form is what the scheme-level Lemma 4.4 applies chart-wise: the charts of
`Bl^{vD}_Y X` are dilatations of mono-centered multicenters whose distinguished
elements are `Classical.choice` generators, not literal powers.
-/

suppress_compilation

universe u

open Family

namespace Multicenter
variable {A : Type (u+1)} [CommRing A] (G : Multicenter A) [Unique G.index]
open Dilatation

local notation "u₀" => (default : G.index)

/-- The exceptional colon ideal `(M·A[G] : e)` of a mono-centered multicenter. -/
noncomputable def exceptIdeal : Ideal A[G] :=
  Submodule.colon (Ideal.map (algebraMap A A[G]) (G.ideal u₀))
    (Submodule.span _ {algebraMap A A[G] (G.elem u₀)})

lemma mem_exceptIdeal {x : A[G]} :
    x ∈ G.exceptIdeal ↔
      algebraMap A A[G] (G.elem u₀) * x ∈
        Ideal.map (algebraMap A A[G]) (G.ideal u₀) := by
  rw [exceptIdeal, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]

/-- The non-zero-divisor condition for `descQuotE`. -/
lemma descQuotE_nzd
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    ∀ i, algebraMap A (A ⧸ G.ideal u₀) (G.elem i) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀) := by
  intro i
  rw [Unique.eq_default i]
  exact hb

/-- The span condition for `descQuotE`. -/
lemma descQuotE_gen :
    ∀ i, Ideal.span {algebraMap A (A ⧸ G.ideal u₀) (G.elem i)} =
      Ideal.map (algebraMap A (A ⧸ G.ideal u₀)) (G.LargeIdeal i) := by
  intro i
  rw [Unique.eq_default i]
  refine (gen_iff_le G u₀).mpr ?_
  rw [show (algebraMap A (A ⧸ G.ideal u₀)) =
    Ideal.Quotient.mk (G.ideal u₀) from rfl, Ideal.map_quotient_self]
  exact bot_le

/-- The universal-property map `A[G] →ₐ[A] A ⧸ M`. -/
noncomputable def descQuotE
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    A[G] →ₐ[A] A ⧸ G.ideal u₀ :=
  desc G (G.descQuotE_nzd hb) (G.descQuotE_gen)

/-- A numerator in `M · L^k` gives a fraction in the image of `M`. -/
lemma frac_mem_map_of_mem_mul_gen (k : ℕ) (p : A)
    (hp : p ∈ G.ideal u₀ * (G.LargeIdeal u₀) ^ k) :
    ∀ (hmem : p ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ))),
    Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨p, hmem⟩ ∈
      Ideal.map (algebraMap A A[G]) (G.ideal u₀) := by
  induction hp using Submodule.mul_induction_on' with
  | mem_mul_mem m hm l hl =>
    intro hmem
    have hlmem : l ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)) := by
      rw [familyPow_single']
      exact hl
    have heq := G.algebraMap_mul_frac m (Finsupp.single u₀ k) l hlmem
    have hpf : Dilatation.frac (F := G) (Finsupp.single u₀ k)
        (⟨m * l, Ideal.mul_mem_left _ m hlmem⟩ :
          G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ))) =
        Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨m * l, hmem⟩ := rfl
    rw [← hpf, ← heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm)
  | add x hx y hy ihx ihy =>
    intro hmem
    have hxk : x ∈ (G.LargeIdeal u₀) ^ k := Ideal.mul_le_left hx
    have hyk : y ∈ (G.LargeIdeal u₀) ^ k := Ideal.mul_le_left hy
    have hxmem : x ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)) := by
      rw [familyPow_single']; exact hxk
    have hymem : y ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)) := by
      rw [familyPow_single']; exact hyk
    have hsum := G.frac_add_same (Finsupp.single u₀ k) x y hxmem hymem
    have hpf : Dilatation.frac (F := G) (Finsupp.single u₀ k)
        (⟨x + y, Submodule.add_mem _ hxmem hymem⟩ :
          G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ))) =
        Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨x + y, hmem⟩ := rfl
    rw [← hpf, hsum]
    exact Ideal.add_mem _ (ihx hxmem) (ihy hymem)

/-- A fraction with zero-power denominator is the algebra image of its numerator. -/
lemma frac_single_zero_gen (x : A)
    (hx : x ∈ G.LargeIdeal ^ ((Finsupp.single u₀ 0 : G.index →₀ ℕ))) :
    Dilatation.frac (F := G) (Finsupp.single u₀ 0) ⟨x, hx⟩ =
      algebraMap A A[G] x := by
  rw [Dilatation.algebraMap_apply]
  simp only [Dilatation.frac, Dilatation.mk_eq_mk]
  use 0
  simp [familyPow_single']

/-- **The key induction** ([Ma24, Cor. 2.40], general form): a fraction whose numerator
lies in the center ideal lies in the exceptional colon ideal. -/
theorem frac_mem_exceptIdeal_of_mem_ideal
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    ∀ (k : ℕ) (m' : A)
      (hmem : m' ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)))
      (_ : m' ∈ G.ideal u₀),
      Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨m', hmem⟩ ∈
        G.exceptIdeal := by
  intro k
  induction k with
  | zero =>
    intro m' hmem hm'
    rw [G.frac_single_zero_gen m' hmem, mem_exceptIdeal, ← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hm')
  | succ k ih =>
    intro m' hmem hm'
    have hpow : m' ∈ (G.LargeIdeal u₀) ^ (k + 1) := by
      rw [familyPow_single'] at hmem
      exact hmem
    rw [pow_succ] at hpow
    have hL : G.LargeIdeal u₀ = G.ideal u₀ ⊔ Ideal.span {G.elem u₀} := by
      show G.ideal u₀ + Ideal.span {G.elem u₀} = _
      rw [Submodule.add_eq_sup]
    rw [hL, Ideal.mul_sup] at hpow
    obtain ⟨p, hp, s, hs, hps⟩ := Submodule.mem_sup.mp hpow
    obtain ⟨q, hq, hqs⟩ := Ideal.mem_span_singleton_mul.mp (by
      rwa [mul_comm] at hs)
    have hpM : p ∈ G.ideal u₀ := Ideal.mul_le_left hp
    have hqM : q ∈ G.ideal u₀ := by
      have hseq : s = m' - p := eq_sub_of_add_eq' hps
      have hbq : G.elem u₀ * q ∈ G.ideal u₀ := by
        rw [hqs, hseq]
        exact Submodule.sub_mem _ hm' hpM
      have h0 : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀ * q) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hbq
      rw [map_mul] at h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).mp h0)
    have hpk : p ∈ (G.LargeIdeal u₀) ^ k := Ideal.mul_le_right hp
    have hpfam : p ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)) := by
      rw [familyPow_single']; exact hpk
    have hqfam : q ∈ G.LargeIdeal ^ ((Finsupp.single u₀ k : G.index →₀ ℕ)) := by
      rw [familyPow_single']; exact hq
    have hML : G.ideal u₀ ≤ G.LargeIdeal u₀ := by
      rw [hL]; exact le_sup_left
    have helem : G.elem u₀ ∈ G.LargeIdeal u₀ := elem_mem_LargeIdeal G u₀
    have hpfam1 : p ∈ G.LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : G.index →₀ ℕ)) := by
      rw [familyPow_single', pow_succ]
      exact Ideal.mul_mono le_rfl hML hp
    have hbqfam : G.elem u₀ * q ∈ G.LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : G.index →₀ ℕ)) := by
      rw [familyPow_single', pow_succ']
      exact Ideal.mul_mem_mul helem hq
    have hval : (⟨m', hmem⟩ : ↥(G.LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : G.index →₀ ℕ)))) =
        ⟨p + G.elem u₀ * q, Submodule.add_mem _ hpfam1 hbqfam⟩ := by
      apply Subtype.ext
      show m' = p + G.elem u₀ * q
      rw [hqs, hps]
    rw [hval]
    have hsplit := G.frac_add_same (Finsupp.single u₀ (k+1)) p
      (G.elem u₀ * q) hpfam1 hbqfam
    rw [show (Dilatation.frac (F := G) (Finsupp.single u₀ (k+1))
        ⟨p + G.elem u₀ * q, Submodule.add_mem _ hpfam1 hbqfam⟩) =
        Dilatation.frac (F := G) (Finsupp.single u₀ (k+1)) ⟨p, hpfam1⟩ +
        Dilatation.frac (F := G) (Finsupp.single u₀ (k+1))
          ⟨G.elem u₀ * q, hbqfam⟩ from hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · rw [mem_exceptIdeal]
      have hchain : algebraMap A A[G] (G.elem u₀) *
          Dilatation.frac (F := G) (Finsupp.single u₀ (k+1)) ⟨p, hpfam1⟩ =
          Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨p, hpfam⟩ :=
        (G.algebraMap_mul_frac (G.elem u₀)
          (Finsupp.single u₀ (k+1)) p hpfam1).trans
        (G.frac_drop u₀ k p hpfam (by
          rw [familyPow_single', pow_succ']
          exact Ideal.mul_mem_mul helem hpk))
      rw [hchain]
      exact G.frac_mem_map_of_mem_mul_gen k p (by rwa [mul_comm] at hp) hpfam
    · have hchain : Dilatation.frac (F := G) (Finsupp.single u₀ (k+1))
          ⟨G.elem u₀ * q, hbqfam⟩ =
          Dilatation.frac (F := G) (Finsupp.single u₀ k) ⟨q, hqfam⟩ :=
        G.frac_drop u₀ k q hqfam hbqfam
      rw [hchain]
      exact ih q hqfam hqM

/-- Elements of the dilatation killed by `descQuotE` lie in the exceptional ideal. -/
lemma descQuotE_eq_zero_mem
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) (x : A[G]) :
    G.descQuotE hb x = 0 → x ∈ G.exceptIdeal := by
  induction x using Dilatation.induction_on with
  | h pd =>
    obtain ⟨w, m', hmem⟩ := pd
    intro hx
    have hw : w = Finsupp.single u₀ (w u₀) := Finsupp.unique_single w
    have hmem' : m' ∈ G.LargeIdeal ^
        ((Finsupp.single u₀ (w u₀) : G.index →₀ ℕ)) := by
      rw [← hw]; exact hmem
    have hfrac : Dilatation.mk ⟨w, m', hmem⟩ =
        Dilatation.frac (F := G) (Finsupp.single u₀ (w u₀)) ⟨m', hmem'⟩ := by
      simp only [Dilatation.frac, Dilatation.mk_eq_mk]
      use 0
      show m' * G.elem ^ ((0 : G.index →₀ ℕ) +
          (Finsupp.single u₀ (w u₀) : G.index →₀ ℕ)) =
        m' * G.elem ^ ((0 : G.index →₀ ℕ) + w)
      exact congrArg (fun t => m' * G.elem ^ ((0 : G.index →₀ ℕ) + t)) hw.symm
    have hspec := dsc_spec G (Finsupp.single u₀ (w u₀)) ⟨m', hmem'⟩
      (G.descQuotE_nzd hb) (G.descQuotE_gen)
    have h0 : (algebraMap A (A ⧸ G.ideal u₀)) m' = 0 := by
      rw [← hspec,
        show desc G (G.descQuotE_nzd hb) (G.descQuotE_gen)
            (Dilatation.frac (F := G) (Finsupp.single u₀ (w u₀)) ⟨m', hmem'⟩) =
          G.descQuotE hb (Dilatation.mk ⟨w, m', hmem⟩) from by rw [hfrac]; rfl,
        hx, mul_zero]
    have hm'M : m' ∈ G.ideal u₀ := Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [hfrac]
    exact G.frac_mem_exceptIdeal_of_mem_ideal hb (w u₀) m' hmem' hm'M

/-- The exceptional ideal is killed by `descQuotE`. -/
lemma exceptIdeal_le_ker
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    G.exceptIdeal ≤ RingHom.ker (G.descQuotE hb) := by
  intro x hx
  rw [RingHom.mem_ker]
  have hx' := (G.mem_exceptIdeal).mp hx
  have hmem : (G.descQuotE hb) (algebraMap A A[G] (G.elem u₀) * x) ∈
      Ideal.map (G.descQuotE hb).toRingHom
        (Ideal.map (algebraMap A A[G]) (G.ideal u₀)) :=
    Ideal.mem_map_of_mem _ hx'
  rw [Ideal.map_map,
    show (G.descQuotE hb).toRingHom.comp (algebraMap A A[G]) =
      algebraMap A (A ⧸ G.ideal u₀) from RingHom.ext fun a =>
        (G.descQuotE hb).commutes a,
    show (algebraMap A (A ⧸ G.ideal u₀)) = Ideal.Quotient.mk (G.ideal u₀) from rfl,
    Ideal.map_quotient_self] at hmem
  have h0 : (G.descQuotE hb) (algebraMap A A[G] (G.elem u₀) * x) = 0 :=
    Submodule.mem_bot _ |>.mp hmem
  rw [map_mul, AlgHom.commutes] at h0
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hb).mp h0

/-- **The kernel of `descQuotE` is the exceptional colon ideal.** -/
theorem ker_descQuotE
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    RingHom.ker (G.descQuotE hb) = G.exceptIdeal :=
  le_antisymm (fun x hx => G.descQuotE_eq_zero_mem hb x (RingHom.mem_ker.mp hx))
    (G.exceptIdeal_le_ker hb)

theorem descQuotE_surjective
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    Function.Surjective (G.descQuotE hb) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap A A[G] a, (G.descQuotE hb).commutes a⟩

/-- **The exceptional quotient of a mono-centered dilatation is the original
quotient**: `A[G] ⧸ (M·A[G] : e) ≃ₐ[A] A/M`. -/
noncomputable def exceptQuotEquiv
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) :
    (A[G] ⧸ G.exceptIdeal) ≃ₐ[A] A ⧸ G.ideal u₀ :=
  (Ideal.quotientEquivAlgOfEq A (G.ker_descQuotE hb).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (G.descQuotE_surjective hb))

@[simp] lemma exceptQuotEquiv_mk
    (hb : Ideal.Quotient.mk (G.ideal u₀) (G.elem u₀) ∈
      nonZeroDivisors (A ⧸ G.ideal u₀)) (x : A[G]) :
    G.exceptQuotEquiv hb (Ideal.Quotient.mk G.exceptIdeal x) =
      G.descQuotE hb x := by
  simp only [exceptQuotEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_apply]
  exact RingHom.kerLift_mk _ x

end Multicenter
