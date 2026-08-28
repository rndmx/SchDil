import MulticenterIterate
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The exceptional quotient of a mono-centered dilatation: [Ma24, Cor. 2.40]

For a mono-centered multicenter `[M, b]` on `A` (index type `Unique`), the `ν`-th
multiple `[M, bᵛ]` has dilatation `A[F.multiple ν]`, and the *lift ideal*
`liftIdeal ν = (M·A[F.multiple ν] : bᵛ)` (a colon ideal, `MulticenterIterate.lean`)
is the kernel of the canonical map to `A/M`:

* `descQuot : A[F.multiple ν] →ₐ[A] A/M` — the universal-property map, defined when the
  class of `b` is a non-zero-divisor in `A/M`;
* `frac_mem_liftIdeal_of_mem_ideal` — the key induction: a fraction `m'/bᵛᵏ` with
  `m' ∈ M` lies in the lift ideal.  Induction on `k`: write `m' = p + bᵛq` with
  `p ∈ Lᵏ·M` and `q ∈ Lᵏ`; the `p`-part drops into `M·A[F.multiple ν]` directly and the
  `q`-part satisfies `q ∈ M` by cancelling the non-zero-divisor `bᵛ` in `A/M`, so the
  inductive hypothesis applies;
* `ker_descQuot` — `ker(descQuot) = liftIdeal ν`;
* `liftQuotEquiv` — `A[F.multiple ν] ⧸ liftIdeal ν ≃ₐ[A] A/M`.

This is the algebraic heart of the scheme-level Lemma 4.4 of [Ma24]: it identifies the
strict transform of the center `Y` inside `Bl^{νD}_Y X` chart-wise.
-/
suppress_compilation
universe u
open Family Multicenter Dilatation

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) [Unique F.index]
  (ν : F.index → ℕ)

local notation "u₀" => (default : F.index)

instance multiple_index_unique : Unique (F.multiple ν).index :=
  inferInstanceAs (Unique F.index)

/-- Powers of the quotient image of the distinguished element stay non-zero-divisors. -/
lemma quot_elem_pow_nzd
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) (k : ℕ) :
    Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀ ^ k) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀) := by
  rw [map_pow]
  exact pow_mem hb k

/-- The non-zero-divisor condition for `descQuot`. -/
lemma descQuot_nzd
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    ∀ i, algebraMap A (A ⧸ F.ideal u₀) ((F.multiple ν).elem i) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀) := by
  intro i
  rw [Unique.eq_default i]
  show algebraMap A (A ⧸ F.ideal u₀) ((F.multiple ν).elem u₀) ∈ _
  rw [multiple_elem]
  show Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀ ^ ν u₀) ∈ _
  exact F.quot_elem_pow_nzd hb (ν u₀)

/-- The span condition for `descQuot`. -/
lemma descQuot_gen :
    ∀ i, Ideal.span {algebraMap A (A ⧸ F.ideal u₀) ((F.multiple ν).elem i)} =
      Ideal.map (algebraMap A (A ⧸ F.ideal u₀)) ((F.multiple ν).LargeIdeal i) := by
  intro i
  rw [Unique.eq_default i]
  refine (gen_iff_le (F.multiple ν) u₀).mpr ?_
  rw [multiple_ideal]
  show Ideal.map (algebraMap A (A ⧸ F.ideal u₀)) (F.ideal u₀) ≤ _
  rw [show (algebraMap A (A ⧸ F.ideal u₀)) =
    Ideal.Quotient.mk (F.ideal u₀) from rfl, Ideal.map_quotient_self]
  exact bot_le

/-- The universal-property map `A[F.multiple ν] →ₐ[A] A ⧸ M` of [Ma24, Cor. 2.40]. -/
noncomputable def descQuot
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    A[F.multiple ν] →ₐ[A] A ⧸ F.ideal u₀ :=
  desc (F.multiple ν) (F.descQuot_nzd ν hb) (F.descQuot_gen ν)

end Multicenter

namespace Multicenter
variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)
open Dilatation

/-- Same-power additivity of fractions. -/
lemma frac_add_same (w : F.index →₀ ℕ) (x y : A) (hx : x ∈ F.LargeIdeal^w)
    (hy : y ∈ F.LargeIdeal^w) :
    Dilatation.frac w (⟨x + y, Submodule.add_mem _ hx hy⟩ : F.LargeIdeal^w) =
      Dilatation.frac w ⟨x, hx⟩ + Dilatation.frac w ⟨y, hy⟩ := by
  simp only [Dilatation.frac, Dilatation.mk_add_mk, Dilatation.mk_eq_mk]
  use 0
  simp only [Dilatation.add'_num, Dilatation.add'_pow, zero_add, familyPow_add]
  ring

/-- Scalar multiplication of a fraction by an algebra element. -/
lemma algebraMap_mul_frac (c : A) (w : F.index →₀ ℕ) (x : A)
    (hx : x ∈ F.LargeIdeal^w) :
    algebraMap A A[F] c * Dilatation.frac w ⟨x, hx⟩ =
      Dilatation.frac w (⟨c * x, Ideal.mul_mem_left _ c hx⟩ : F.LargeIdeal^w) := by
  rw [← Algebra.smul_def, Dilatation.smul_frac]
  rfl

/-- Dropping one power of the distinguished element from the numerator. -/
lemma frac_drop (i : F.index) (k : ℕ) (q : A)
    (hq : q ∈ F.LargeIdeal^((Finsupp.single i k : F.index →₀ ℕ)))
    (hbq : F.elem i * q ∈
      F.LargeIdeal^((Finsupp.single i (k+1) : F.index →₀ ℕ))) :
    Dilatation.frac (Finsupp.single i (k+1)) ⟨F.elem i * q, hbq⟩ =
      Dilatation.frac (Finsupp.single i k) ⟨q, hq⟩ := by
  simp only [Dilatation.frac, Dilatation.mk_eq_mk]
  use 0
  simp only [zero_add, familyPow_single']
  ring

end Multicenter

namespace Multicenter
variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) [Unique F.index]
  (ν : F.index → ℕ)
open Dilatation

local notation "u₀" => (default : F.index)

/-- A numerator in `M · Lᵏ` gives a fraction in the image of `M`. -/
lemma frac_mem_map_of_mem_mul (k : ℕ) (p : A)
    (hp : p ∈ F.ideal u₀ * ((F.multiple ν).LargeIdeal u₀) ^ k) :
    ∀ (hmem : p ∈ (F.multiple ν).LargeIdeal ^
      ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ))),
    Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k) ⟨p, hmem⟩ ∈
      Ideal.map (algebraMap A A[F.multiple ν]) (F.ideal u₀) := by
  induction hp using Submodule.mul_induction_on' with
  | mem_mul_mem m hm l hl =>
    intro hmem
    have hlmem : l ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single']
      exact hl
    have heq := (F.multiple ν).algebraMap_mul_frac m (Finsupp.single u₀ k) l hlmem
    have hpf : Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k)
        (⟨m * l, Ideal.mul_mem_left _ m hlmem⟩ :
          (F.multiple ν).LargeIdeal ^ ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ))) =
        Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k) ⟨m * l, hmem⟩ := rfl
    rw [← hpf, ← heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm)
  | add x hx y hy ihx ihy =>
    intro hmem
    have hxk : x ∈ ((F.multiple ν).LargeIdeal u₀) ^ k :=
      Ideal.mul_le_left hx
    have hyk : y ∈ ((F.multiple ν).LargeIdeal u₀) ^ k :=
      Ideal.mul_le_left hy
    have hxmem : x ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single']; exact hxk
    have hymem : y ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single']; exact hyk
    have hsum := (F.multiple ν).frac_add_same (Finsupp.single u₀ k) x y hxmem hymem
    have hpf : Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k)
        (⟨x + y, Submodule.add_mem _ hxmem hymem⟩ :
          (F.multiple ν).LargeIdeal ^ ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ))) =
        Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k) ⟨x + y, hmem⟩ := rfl
    rw [← hpf, hsum]
    exact Ideal.add_mem _ (ihx hxmem) (ihy hymem)

end Multicenter

namespace Multicenter
variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) [Unique F.index]
  (ν : F.index → ℕ)
open Dilatation

local notation "u₀" => (default : F.index)

/-- A fraction with zero-power denominator is the algebra image of its numerator. -/
lemma frac_single_zero (x : A)
    (hx : x ∈ (F.multiple ν).LargeIdeal ^
      ((Finsupp.single u₀ 0 : (F.multiple ν).index →₀ ℕ))) :
    Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ 0) ⟨x, hx⟩ =
      algebraMap A A[F.multiple ν] x := by
  rw [Dilatation.algebraMap_apply]
  simp only [Dilatation.frac, Dilatation.mk_eq_mk]
  use 0
  simp [familyPow_single']

/-- **The key induction of [Ma24, Cor. 2.40]**: a fraction whose numerator lies in the
center ideal lies in the lift ideal. -/
theorem frac_mem_liftIdeal_of_mem_ideal
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    ∀ (k : ℕ) (m' : A)
      (hmem : m' ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)))
      (_ : m' ∈ F.ideal u₀),
      Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k) ⟨m', hmem⟩ ∈
        F.liftIdeal ν u₀ := by
  intro k
  induction k with
  | zero =>
    intro m' hmem hm'
    rw [F.frac_single_zero ν m' hmem, mem_liftIdeal, ← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hm')
  | succ k ih =>
    intro m' hmem hm'
    have hpow : m' ∈ ((F.multiple ν).LargeIdeal u₀) ^ (k + 1) := by
      rw [familyPow_single'] at hmem
      exact hmem
    rw [pow_succ] at hpow
    have hL : (F.multiple ν).LargeIdeal u₀ =
        F.ideal u₀ ⊔ Ideal.span {F.elem u₀ ^ ν u₀} := by
      show F.ideal u₀ + Ideal.span {(F.multiple ν).elem u₀} = _
      rw [multiple_elem, Submodule.add_eq_sup]
    rw [hL, Ideal.mul_sup] at hpow
    obtain ⟨p, hp, s, hs, hps⟩ := Submodule.mem_sup.mp hpow
    obtain ⟨q, hq, hqs⟩ := Ideal.mem_span_singleton_mul.mp (by
      rwa [mul_comm] at hs)
    have hpM : p ∈ F.ideal u₀ := Ideal.mul_le_left hp
    have hqM : q ∈ F.ideal u₀ := by
      have hseq : s = m' - p := eq_sub_of_add_eq' hps
      have hbq : F.elem u₀ ^ ν u₀ * q ∈ F.ideal u₀ := by
        rw [hqs, hseq]
        exact Submodule.sub_mem _ hm' hpM
      have h0 : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀ ^ ν u₀ * q) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hbq
      rw [map_mul, map_pow] at h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hb (ν u₀))).mp h0)
    have hpk : p ∈ ((F.multiple ν).LargeIdeal u₀) ^ k := Ideal.mul_le_right hp
    have hpfam : p ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single']; exact hpk
    have hqfam : q ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ k : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single']; exact hq
    have hML : F.ideal u₀ ≤ (F.multiple ν).LargeIdeal u₀ := by
      rw [hL]; exact le_sup_left
    have helem : (F.multiple ν).elem u₀ ∈ (F.multiple ν).LargeIdeal u₀ :=
      elem_mem_LargeIdeal (F.multiple ν) u₀
    have hpfam1 : p ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single', pow_succ]
      exact Ideal.mul_mono le_rfl hML hp
    have hbqfam : (F.multiple ν).elem u₀ * q ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : (F.multiple ν).index →₀ ℕ)) := by
      rw [familyPow_single', pow_succ']
      exact Ideal.mul_mem_mul helem hq
    -- decompose the fraction: m' = p + bᵛ·q
    have hval : (⟨m', hmem⟩ : ↥((F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ (k+1) : (F.multiple ν).index →₀ ℕ)))) =
        ⟨p + (F.multiple ν).elem u₀ * q,
          Submodule.add_mem _ hpfam1
            (hbqfam)⟩ := by
      apply Subtype.ext
      show m' = p + (F.multiple ν).elem u₀ * q
      rw [multiple_elem, hqs, hps]
    rw [hval]
    have hsplit := (F.multiple ν).frac_add_same (Finsupp.single u₀ (k+1)) p
      ((F.multiple ν).elem u₀ * q) hpfam1 (hbqfam)
    rw [show (Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (k+1))
        ⟨p + (F.multiple ν).elem u₀ * q,
          Submodule.add_mem _ hpfam1 (hbqfam)⟩) =
        Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (k+1)) ⟨p, hpfam1⟩ +
        Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (k+1))
          ⟨(F.multiple ν).elem u₀ * q, hbqfam⟩ from hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · -- p-part
      rw [mem_liftIdeal]
      have hchain : algebraMap A A[F.multiple ν] (F.elem u₀ ^ ν u₀) *
          Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (k+1))
            ⟨p, hpfam1⟩ =
          Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k)
            ⟨p, hpfam⟩ :=
        ((F.multiple ν).algebraMap_mul_frac (F.elem u₀ ^ ν u₀)
          (Finsupp.single u₀ (k+1)) p hpfam1).trans
        ((F.multiple ν).frac_drop u₀ k p hpfam (by
          rw [familyPow_single', pow_succ']
          exact Ideal.mul_mem_mul helem hpk))
      rw [hchain]
      exact F.frac_mem_map_of_mem_mul ν k p (by rwa [mul_comm] at hp) hpfam
    · -- q-part: drop one power and use the induction hypothesis
      have hchain : Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (k+1))
          ⟨(F.multiple ν).elem u₀ * q, hbqfam⟩ =
          Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ k)
            ⟨q, hqfam⟩ :=
        (F.multiple ν).frac_drop u₀ k q hqfam (hbqfam)
      rw [hchain]
      exact ih q hqfam hqM

end Multicenter

namespace Multicenter
variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) [Unique F.index]
  (ν : F.index → ℕ)
open Dilatation

local notation "u₀" => (default : F.index)

/-- Elements of the dilatation killed by `descQuot` lie in the lift ideal
(the hard inclusion of the kernel computation, via the key induction). -/
lemma descQuot_eq_zero_mem
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) (x : A[F.multiple ν]) :
    F.descQuot ν hb x = 0 → x ∈ F.liftIdeal ν u₀ := by
  induction x using Dilatation.induction_on with
  | h pd =>
    obtain ⟨w, m', hmem⟩ := pd
    intro hx
    have hw : w = Finsupp.single u₀ (w u₀) := Finsupp.unique_single w
    have hmem' : m' ∈ (F.multiple ν).LargeIdeal ^
        ((Finsupp.single u₀ (w u₀) : (F.multiple ν).index →₀ ℕ)) := by
      rw [← hw]; exact hmem
    have hfrac : Dilatation.mk ⟨w, m', hmem⟩ =
        Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (w u₀)) ⟨m', hmem'⟩ := by
      simp only [Dilatation.frac, Dilatation.mk_eq_mk]
      use 0
      show m' * (F.multiple ν).elem ^ ((0 : (F.multiple ν).index →₀ ℕ) +
          (Finsupp.single u₀ (w u₀) : (F.multiple ν).index →₀ ℕ)) =
        m' * (F.multiple ν).elem ^ ((0 : (F.multiple ν).index →₀ ℕ) + w)
      exact congrArg (fun t => m' * (F.multiple ν).elem ^
        ((0 : (F.multiple ν).index →₀ ℕ) + t)) hw.symm
    have hspec := dsc_spec (F.multiple ν) (Finsupp.single u₀ (w u₀)) ⟨m', hmem'⟩
      (F.descQuot_nzd ν hb) (F.descQuot_gen ν)
    have h0 : (algebraMap A (A ⧸ F.ideal u₀)) m' = 0 := by
      rw [← hspec,
        show desc (F.multiple ν) (F.descQuot_nzd ν hb) (F.descQuot_gen ν)
            (Dilatation.frac (F := F.multiple ν) (Finsupp.single u₀ (w u₀))
              ⟨m', hmem'⟩) =
          F.descQuot ν hb (Dilatation.mk ⟨w, m', hmem⟩) from by rw [hfrac]; rfl,
        hx, mul_zero]
    have hm'M : m' ∈ F.ideal u₀ := Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [hfrac]
    exact F.frac_mem_liftIdeal_of_mem_ideal ν hb (w u₀) m' hmem' hm'M

/-- The lift ideal is killed by `descQuot` (the easy inclusion). -/
lemma liftIdeal_le_ker
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    F.liftIdeal ν u₀ ≤ RingHom.ker (F.descQuot ν hb) := by
  intro x hx
  rw [RingHom.mem_ker]
  have hx' := (F.mem_liftIdeal).mp hx
  have hmem : (F.descQuot ν hb)
      (algebraMap A A[F.multiple ν] (F.elem u₀ ^ ν u₀) * x) ∈
      Ideal.map (F.descQuot ν hb).toRingHom
        (Ideal.map (algebraMap A A[F.multiple ν]) (F.ideal u₀)) :=
    Ideal.mem_map_of_mem _ hx'
  rw [Ideal.map_map,
    show (F.descQuot ν hb).toRingHom.comp (algebraMap A A[F.multiple ν]) =
      algebraMap A (A ⧸ F.ideal u₀) from RingHom.ext fun a =>
        (F.descQuot ν hb).commutes a,
    show (algebraMap A (A ⧸ F.ideal u₀)) = Ideal.Quotient.mk (F.ideal u₀) from rfl,
    Ideal.map_quotient_self] at hmem
  have h0 : (F.descQuot ν hb)
      (algebraMap A A[F.multiple ν] (F.elem u₀ ^ ν u₀) * x) = 0 :=
    Submodule.mem_bot _ |>.mp hmem
  rw [map_mul, AlgHom.commutes] at h0
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff
    (F.quot_elem_pow_nzd hb (ν u₀))).mp h0

/-- **The kernel of `descQuot` is the lift ideal** — the heart of [Ma24, Cor. 2.40]:
`ker (A[F.multiple ν] → A/M) = (M A[F.multiple ν] : aᵛ)`. -/
theorem ker_descQuot
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    RingHom.ker (F.descQuot ν hb) = F.liftIdeal ν u₀ :=
  le_antisymm (fun x hx => F.descQuot_eq_zero_mem ν hb x (RingHom.mem_ker.mp hx))
    (F.liftIdeal_le_ker ν hb)

theorem descQuot_surjective
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    Function.Surjective (F.descQuot ν hb) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap A A[F.multiple ν] a, (F.descQuot ν hb).commutes a⟩

/-- **[Ma24, Cor. 2.40], quotient form**: the exceptional quotient of the dilatation
along the lift ideal is the original quotient `A/M`. -/
noncomputable def liftQuotEquiv
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) :
    (A[F.multiple ν] ⧸ F.liftIdeal ν u₀) ≃ₐ[A] A ⧸ F.ideal u₀ :=
  (Ideal.quotientEquivAlgOfEq A (F.ker_descQuot ν hb).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (F.descQuot_surjective ν hb))

@[simp] lemma liftQuotEquiv_mk
    (hb : Ideal.Quotient.mk (F.ideal u₀) (F.elem u₀) ∈
      nonZeroDivisors (A ⧸ F.ideal u₀)) (x : A[F.multiple ν]) :
    F.liftQuotEquiv ν hb (Ideal.Quotient.mk (F.liftIdeal ν u₀) x) =
      F.descQuot ν hb x := by
  simp only [liftQuotEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_apply]
  exact RingHom.kerLift_mk _ x

end Multicenter
