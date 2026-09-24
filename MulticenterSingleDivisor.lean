import MulticenterExceptional

suppress_compilation

universe u

open Family

def finsuppDeg {ι : Type*} (ν : ι →₀ ℕ) : ℕ := ν.sum fun _ k => k

lemma finsuppDeg_eq_zero {ι : Type*} (ν : ι →₀ ℕ) (h : finsuppDeg ν ≤ 0) : ν = 0 := by
  by_contra hν
  obtain ⟨j, hj⟩ : ∃ j, ν j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hν (Finsupp.ext fun j => by simp [hc j])
  have hjs : j ∈ ν.support := Finsupp.mem_support_iff.mpr hj
  have hle : ν j ≤ ∑ k ∈ ν.support, ν k :=
    Finset.single_le_sum (f := fun k => ν k) (fun k _ => Nat.zero_le _) hjs
  simp only [finsuppDeg, Finsupp.sum] at h
  omega

lemma finsuppDeg_single_add {ι : Type*} (i : ι) (ν : ι →₀ ℕ) :
    finsuppDeg ((Finsupp.single i 1 : ι →₀ ℕ) + ν) = 1 + finsuppDeg ν := by
  simp only [finsuppDeg]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  congr 1
  exact Finsupp.sum_single_index rfl

lemma exists_single_add_of_ne_zero {ι : Type*} [DecidableEq ι] (ν : ι →₀ ℕ)
    (hν : ν ≠ 0) : ∃ (i : ι) (ν' : ι →₀ ℕ), (Finsupp.single i 1 : ι →₀ ℕ) + ν' = ν := by
  obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hν (Finsupp.ext fun j => by simp [hc j])
  refine ⟨i, Finsupp.single i (ν i - 1) + ν.erase i, ?_⟩
  rw [← add_assoc, ← Finsupp.single_add,
    show 1 + (ν i - 1) = ν i from by omega]
  exact Finsupp.single_add_erase i ν

namespace Multicenter

section Fact51

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)

open Dilatation

def genFracIdeal : Ideal A[F] :=
  ⨆ i : F.index, Ideal.span
    {x : A[F] | ∃ (m : A) (hm : m ∈ F.ideal i),
      x = Dilatation.frac (Finsupp.single i 1)
        ⟨m, F.mem_largeIdealPow_single i hm⟩}

lemma frac_mem_genFracIdeal (i : F.index) {m : A} (hm : m ∈ F.ideal i) :
    Dilatation.frac (Finsupp.single i 1)
        (⟨m, F.mem_largeIdealPow_single i hm⟩ :
          F.LargeIdeal ^ (Finsupp.single i 1 : F.index →₀ ℕ)) ∈ F.genFracIdeal :=
  Submodule.mem_iSup_of_mem i (Ideal.subset_span ⟨m, hm, rfl⟩)

lemma mem_largeIdealPow_single_add {i : F.index} {ν : F.index →₀ ℕ} {x : A}
    (hx : x ∈ F.LargeIdeal ^ ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)) :
    x ∈ F.LargeIdeal i * F.LargeIdeal ^ ν := by
  rw [← familyPow_single F.LargeIdeal i, ← familyPow_add]
  exact hx

lemma mem_largeIdealPow_single_add' {i : F.index} {ν : F.index →₀ ℕ} {x : A}
    (hx : x ∈ F.LargeIdeal i * F.LargeIdeal ^ ν) :
    x ∈ F.LargeIdeal ^ ((Finsupp.single i 1 : F.index →₀ ℕ) + ν) := by
  rw [familyPow_add, familyPow_single]
  exact hx

lemma frac_drop_add (ν : F.index →₀ ℕ) (i : F.index) (q : A)
    (hq : q ∈ F.LargeIdeal ^ ν)
    (hbq : F.elem i * q ∈
      F.LargeIdeal ^ ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)) :
    Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)
        ⟨F.elem i * q, hbq⟩ =
      Dilatation.frac ν ⟨q, hq⟩ := by
  simp only [Dilatation.frac, Dilatation.mk_eq_mk]
  use 0
  simp only [zero_add, familyPow_add, familyPow_single]
  ring

lemma frac_mem_genFracIdeal_of_mem_mul (ν : F.index →₀ ℕ) (i : F.index) (p : A)
    (hp : p ∈ F.ideal i * F.LargeIdeal ^ ν) :
    ∀ (hmem : p ∈ F.LargeIdeal ^
      ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)),
    Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν) ⟨p, hmem⟩ ∈
      F.genFracIdeal := by
  induction hp using Submodule.mul_induction_on' with
  | mem_mul_mem m hm l hl =>
    intro hmem
    have hprod := Dilatation.frac_mul_frac (F := F) (Finsupp.single i 1) ν
      ⟨m, F.mem_largeIdealPow_single i hm⟩ ⟨l, hl⟩
    have hpf : Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)
        (⟨m * l, Ideal.mem_familyPow_add
          (F.mem_largeIdealPow_single i hm) hl⟩ :
          F.LargeIdeal ^ ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)) =
        Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)
          ⟨m * l, hmem⟩ := rfl
    rw [← hpf, ← hprod]
    exact Ideal.mul_mem_right _ _ (F.frac_mem_genFracIdeal i hm)
  | add x hx y hy ihx ihy =>
    intro hmem
    have hxmem : x ∈ F.LargeIdeal ^
        ((Finsupp.single i 1 : F.index →₀ ℕ) + ν) :=
      F.mem_largeIdealPow_single_add'
        (Ideal.mul_mono_left (by
          show F.ideal i ≤ F.LargeIdeal i
          rw [LargeIdeal, Submodule.add_eq_sup]
          exact le_sup_left) hx)
    have hymem : y ∈ F.LargeIdeal ^
        ((Finsupp.single i 1 : F.index →₀ ℕ) + ν) :=
      F.mem_largeIdealPow_single_add'
        (Ideal.mul_mono_left (by
          show F.ideal i ≤ F.LargeIdeal i
          rw [LargeIdeal, Submodule.add_eq_sup]
          exact le_sup_left) hy)
    have hsum := F.frac_add_same
      ((Finsupp.single i 1 : F.index →₀ ℕ) + ν) x y hxmem hymem
    have hpf : Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)
        (⟨x + y, Submodule.add_mem _ hxmem hymem⟩ :
          F.LargeIdeal ^ ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)) =
        Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν)
          ⟨x + y, hmem⟩ := rfl
    rw [← hpf, hsum]
    exact Ideal.add_mem _ (ihx hxmem) (ihy hymem)

lemma frac_zero_eq_algebraMap (x : A)
    (hx : x ∈ F.LargeIdeal ^ (0 : F.index →₀ ℕ)) :
    Dilatation.frac (0 : F.index →₀ ℕ) ⟨x, hx⟩ = algebraMap A A[F] x := by
  have h := F.algebraMap_eq_pow_mul_frac (0 : F.index →₀ ℕ) x hx
  rw [familyPow_zero, map_one, one_mul] at h
  exact h.symm

lemma frac_exp_congr (v w : F.index →₀ ℕ) (hvw : v = w) (m : A)
    (hm : m ∈ F.LargeIdeal ^ v) (hm' : m ∈ F.LargeIdeal ^ w) :
    Dilatation.frac v ⟨m, hm⟩ = Dilatation.frac w ⟨m, hm'⟩ := by
  subst hvw
  rfl

section Section5

variable (i₀ : F.index)
  (hsub : ∀ i, F.ideal i ≤ F.ideal i₀)
  (hnzd : ∀ i, Ideal.Quotient.mk (F.ideal i₀) (F.elem i) ∈
    nonZeroDivisors (A ⧸ F.ideal i₀))

include hnzd in
lemma descTo_nzd :
    ∀ i, algebraMap A (A ⧸ F.ideal i₀) (F.elem i) ∈
      nonZeroDivisors (A ⧸ F.ideal i₀) :=
  fun i => hnzd i

include hsub in
lemma descTo_gen :
    ∀ i, Ideal.span {algebraMap A (A ⧸ F.ideal i₀) (F.elem i)} =
      Ideal.map (algebraMap A (A ⧸ F.ideal i₀)) (F.LargeIdeal i) := by
  intro i
  refine (gen_iff_le F i).mpr ?_
  refine le_trans (Ideal.map_mono (hsub i)) ?_
  rw [show (algebraMap A (A ⧸ F.ideal i₀)) = Ideal.Quotient.mk (F.ideal i₀)
    from rfl, Ideal.map_quotient_self]
  exact bot_le

noncomputable def descTo : A[F] →ₐ[A] A ⧸ F.ideal i₀ :=
  desc F (F.descTo_nzd i₀ hnzd) (F.descTo_gen i₀ hsub)

set_option maxHeartbeats 2000000 in
include hsub hnzd in
theorem frac_mem_genFracIdeal_of_mem_ideal :
    ∀ (d : ℕ) (ν : F.index →₀ ℕ), finsuppDeg ν ≤ d →
      ∀ (m' : A) (hmem : m' ∈ F.LargeIdeal ^ ν), m' ∈ F.ideal i₀ →
      Dilatation.frac ν ⟨m', hmem⟩ ∈ F.genFracIdeal := by
  classical
  intro d
  induction d with
  | zero =>
    intro ν hd m' hmem hm'
    have hν0 : ν = 0 := finsuppDeg_eq_zero ν hd
    have hmem0 : m' ∈ F.LargeIdeal ^ (0 : F.index →₀ ℕ) := hν0 ▸ hmem
    rw [F.frac_exp_congr ν 0 hν0 m' hmem hmem0, F.frac_zero_eq_algebraMap m' hmem0]
    have hkey := F.algebraMap_eq_pow_mul_frac
      ((Finsupp.single i₀ 1 : F.index →₀ ℕ)) m'
      (F.mem_largeIdealPow_single i₀ hm')
    rw [hkey]
    exact Ideal.mul_mem_left _ _ (F.frac_mem_genFracIdeal i₀ hm')
  | succ d ih =>
    intro ν hd m' hmem hm'
    by_cases hν0 : ν = 0
    · have hmem0 : m' ∈ F.LargeIdeal ^ (0 : F.index →₀ ℕ) := hν0 ▸ hmem
      rw [F.frac_exp_congr ν 0 hν0 m' hmem hmem0, F.frac_zero_eq_algebraMap m' hmem0]
      have hkey := F.algebraMap_eq_pow_mul_frac
        ((Finsupp.single i₀ 1 : F.index →₀ ℕ)) m'
        (F.mem_largeIdealPow_single i₀ hm')
      rw [hkey]
      exact Ideal.mul_mem_left _ _ (F.frac_mem_genFracIdeal i₀ hm')
    · obtain ⟨i, ν', hνeq⟩ := exists_single_add_of_ne_zero ν hν0
      have hd' : finsuppDeg ν' ≤ d := by
        have := finsuppDeg_single_add i ν'
        rw [hνeq] at this
        omega
      have hmem' : m' ∈ F.LargeIdeal ^
          ((Finsupp.single i 1 : F.index →₀ ℕ) + ν') := hνeq ▸ hmem
      rw [F.frac_exp_congr ν ((Finsupp.single i 1 : F.index →₀ ℕ) + ν')
        hνeq.symm m' hmem hmem']
      have hsplit0 : m' ∈ F.LargeIdeal i * F.LargeIdeal ^ ν' :=
        F.mem_largeIdealPow_single_add hmem'
      have hLi : F.LargeIdeal i = F.ideal i ⊔ Ideal.span {F.elem i} := by
        rw [LargeIdeal, Submodule.add_eq_sup]
      rw [hLi, Ideal.sup_mul] at hsplit0
      obtain ⟨p, hp, t, ht, hpt⟩ := Submodule.mem_sup.mp hsplit0
      obtain ⟨q, hq, hqt⟩ := Ideal.mem_span_singleton_mul.mp ht
      have hpi : p ∈ F.ideal i := Ideal.mul_le_right hp
      have hpM : p ∈ F.ideal i₀ := hsub i hpi
      have hqM : q ∈ F.ideal i₀ := by
        have hbq : F.elem i * q ∈ F.ideal i₀ := by
          rw [hqt, show t = m' - p from eq_sub_of_add_eq' hpt]
          exact Submodule.sub_mem _ hm' hpM
        have h0 : Ideal.Quotient.mk (F.ideal i₀) (F.elem i * q) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hbq
        rw [map_mul] at h0
        exact Ideal.Quotient.eq_zero_iff_mem.mp
          ((mul_left_mem_nonZeroDivisors_eq_zero_iff (hnzd i)).mp h0)
      have hpν' : p ∈ F.LargeIdeal ^ ν' := Ideal.mul_le_left hp
      have hpmem : p ∈ F.LargeIdeal ^
          ((Finsupp.single i 1 : F.index →₀ ℕ) + ν') :=
        F.mem_largeIdealPow_single_add' (Ideal.mul_mono_left (by
          rw [hLi]; exact le_sup_left) hp)
      have hpMi : p ∈ F.ideal i * F.LargeIdeal ^ ν' := hp
      have hbqmem : F.elem i * q ∈ F.LargeIdeal ^
          ((Finsupp.single i 1 : F.index →₀ ℕ) + ν') :=
        F.mem_largeIdealPow_single_add'
          (Ideal.mul_mem_mul (elem_mem_LargeIdeal F i) hq)
      have hval : (⟨m', hmem'⟩ : ↥(F.LargeIdeal ^
          ((Finsupp.single i 1 : F.index →₀ ℕ) + ν'))) =
          ⟨p + F.elem i * q, Submodule.add_mem _ hpmem hbqmem⟩ := by
        apply Subtype.ext
        show m' = p + F.elem i * q
        rw [hqt, hpt]
      rw [hval]
      have hsum := F.frac_add_same
        ((Finsupp.single i 1 : F.index →₀ ℕ) + ν') p (F.elem i * q)
        hpmem hbqmem
      rw [show (Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν')
          ⟨p + F.elem i * q, Submodule.add_mem _ hpmem hbqmem⟩) =
          Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν')
            ⟨p, hpmem⟩ +
          Dilatation.frac ((Finsupp.single i 1 : F.index →₀ ℕ) + ν')
            ⟨F.elem i * q, hbqmem⟩ from hsum]
      refine Ideal.add_mem _ ?_ ?_
      · exact F.frac_mem_genFracIdeal_of_mem_mul ν' i p hpMi hpmem
      · rw [F.frac_drop_add ν' i q hq hbqmem]
        exact ih ν' hd' q hq hqM

include hsub hnzd in
lemma genFracIdeal_le_ker :
    F.genFracIdeal ≤ RingHom.ker (F.descTo i₀ hsub hnzd) := by
  refine iSup_le fun i => ?_
  rw [Ideal.span_le]
  rintro x ⟨m, hm, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  have hspec := dsc_spec F ((Finsupp.single i 1 : F.index →₀ ℕ))
    ⟨m, F.mem_largeIdealPow_single i hm⟩
    (F.descTo_nzd i₀ hnzd) (F.descTo_gen i₀ hsub)
  rw [familyPow_single] at hspec
  have hm0 : (algebraMap A (A ⧸ F.ideal i₀)) m = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hsub i hm)
  rw [hm0] at hspec
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (hnzd i)).mp hspec

include hsub hnzd in
lemma descTo_eq_zero_mem (x : A[F]) :
    F.descTo i₀ hsub hnzd x = 0 → x ∈ F.genFracIdeal := by
  induction x using Dilatation.induction_on with
  | h pd =>
    intro hx
    have hspec := dsc_spec F pd.pow ⟨pd.num, pd.num_mem⟩
      (F.descTo_nzd i₀ hnzd) (F.descTo_gen i₀ hsub)
    rw [show desc F (F.descTo_nzd i₀ hnzd) (F.descTo_gen i₀ hsub)
        (Dilatation.frac pd.pow ⟨pd.num, pd.num_mem⟩) =
        F.descTo i₀ hsub hnzd (Dilatation.mk pd) from rfl, hx, mul_zero] at hspec
    have hnum : pd.num ∈ F.ideal i₀ :=
      Ideal.Quotient.eq_zero_iff_mem.mp hspec.symm
    show Dilatation.mk pd ∈ F.genFracIdeal
    exact F.frac_mem_genFracIdeal_of_mem_ideal i₀ hsub hnzd
      (finsuppDeg pd.pow) pd.pow le_rfl pd.num pd.num_mem hnum

include hsub hnzd in
theorem ker_descTo :
    RingHom.ker (F.descTo i₀ hsub hnzd) = F.genFracIdeal :=
  le_antisymm
    (fun x hx => F.descTo_eq_zero_mem i₀ hsub hnzd x (RingHom.mem_ker.mp hx))
    (F.genFracIdeal_le_ker i₀ hsub hnzd)

include hsub hnzd in
theorem descTo_surjective :
    Function.Surjective (F.descTo i₀ hsub hnzd) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap A A[F] a, (F.descTo i₀ hsub hnzd).commutes a⟩

noncomputable def genFracQuotEquiv :
    (A[F] ⧸ F.genFracIdeal) ≃ₐ[A] A ⧸ F.ideal i₀ :=
  (Ideal.quotientEquivAlgOfEq A (F.ker_descTo i₀ hsub hnzd).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (F.descTo_surjective i₀ hsub hnzd))

@[simp] lemma genFracQuotEquiv_mk (x : A[F]) :
    F.genFracQuotEquiv i₀ hsub hnzd (Ideal.Quotient.mk F.genFracIdeal x) =
      F.descTo i₀ hsub hnzd x := by
  simp only [genFracQuotEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_apply]
  exact RingHom.kerLift_mk _ x

end Section5

end Fact51

end Multicenter
