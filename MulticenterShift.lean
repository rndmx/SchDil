import MulticenterSingleDivisor
import MulticenterMonopoly

suppress_compilation

universe u

open Family

namespace Multicenter

section Prop52

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A) (c : A)

open Dilatation

def shift : Multicenter A where
  index := F.index
  ideal := F.ideal
  elem i := F.elem i * c

@[simp] lemma shift_ideal (i : F.index) : (F.shift c).ideal i = F.ideal i := rfl

@[simp] lemma shift_elem (i : F.index) : (F.shift c).elem i = F.elem i * c := rfl

lemma shift_elem_nzd (i : F.index) :
    algebraMap A A[F.shift c] (F.elem i) ∈ nonZeroDivisors A[F.shift c] := by
  have h := nonzerodiv_image_single (F.shift c) i
  rw [shift_elem, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).1

lemma shift_c_nzd (i₀ : F.index) :
    algebraMap A A[F.shift c] c ∈ nonZeroDivisors A[F.shift c] := by
  have h := nonzerodiv_image_single (F.shift c) i₀
  rw [shift_elem, map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

lemma toShift_gen : ∀ i, Ideal.span {algebraMap A A[F.shift c] (F.elem i)} =
    Ideal.map (algebraMap A A[F.shift c]) (F.LargeIdeal i) := by
  intro i
  refine (gen_iff_le F i).mpr ?_
  refine le_trans (Multicenter.self_le (F.shift c) i) ?_
  rw [shift_elem, map_mul]
  exact Ideal.span_singleton_le_span_singleton.mpr
    ⟨algebraMap A A[F.shift c] c, rfl⟩

def toShift : A[F] →ₐ[A] A[F.shift c] :=
  desc F (F.shift_elem_nzd c) (F.toShift_gen c)

lemma toShift_frac (i : F.index) {m : A} (hm : m ∈ F.ideal i) :
    F.toShift c (Dilatation.frac (F := F) (Finsupp.single i 1)
        ⟨m, F.mem_largeIdealPow_single i hm⟩) =
      algebraMap A A[F.shift c] c *
        Dilatation.frac (F := F.shift c) (Finsupp.single i 1)
          ⟨m, (F.shift c).mem_largeIdealPow_single i hm⟩ := by
  have h1 := dsc_spec F (Finsupp.single i 1)
    ⟨m, F.mem_largeIdealPow_single i hm⟩ (F.shift_elem_nzd c) (F.toShift_gen c)
  rw [familyPow_single] at h1
  have h2 := (F.shift c).algebraMap_eq_pow_mul_frac (Finsupp.single i 1) m
    ((F.shift c).mem_largeIdealPow_single i hm)
  rw [familyPow_single, shift_elem, map_mul] at h2
  have hzero : algebraMap A A[F.shift c] (F.elem i) *
      (F.toShift c (Dilatation.frac (F := F) (Finsupp.single i 1)
          ⟨m, F.mem_largeIdealPow_single i hm⟩) -
        algebraMap A A[F.shift c] c *
          Dilatation.frac (F := F.shift c) (Finsupp.single i 1)
            ⟨m, (F.shift c).mem_largeIdealPow_single i hm⟩) = 0 := by
    rw [mul_sub, show algebraMap A A[F.shift c] (F.elem i) *
      F.toShift c (Dilatation.frac (F := F) (Finsupp.single i 1)
        ⟨m, F.mem_largeIdealPow_single i hm⟩) =
      algebraMap A A[F.shift c] m from h1]
    rw [h2]
    ring
  exact sub_eq_zero.mp
    ((mul_left_mem_nonZeroDivisors_eq_zero_iff (F.shift_elem_nzd c i)).mp hzero)

lemma genFracIdeal_le {J : Ideal A[F]}
    (h : ∀ (i : F.index) (m : A) (hm : m ∈ F.ideal i),
      Dilatation.frac (F := F) (Finsupp.single i 1)
        ⟨m, F.mem_largeIdealPow_single i hm⟩ ∈ J) :
    F.genFracIdeal ≤ J := by
  refine iSup_le fun i => ?_
  rw [Ideal.span_le]
  rintro x ⟨m, hm, rfl⟩
  exact h i m hm

def secondStage : Multicenter A[F] where
  index := PUnit
  ideal _ := F.genFracIdeal
  elem _ := algebraMap A A[F] c

@[simp] lemma secondStage_ideal (u : PUnit) :
    (F.secondStage c).ideal u = F.genFracIdeal := rfl

@[simp] lemma secondStage_elem (u : PUnit) :
    (F.secondStage c).elem u = algebraMap A A[F] c := rfl

local instance shiftAlgebra : Algebra A[F] A[F.shift c] :=
  (F.toShift c).toRingHom.toAlgebra

local instance : IsScalarTower A A[F] A[F.shift c] :=
  IsScalarTower.of_algebraMap_eq fun a => ((F.toShift c).commutes a).symm

local instance : IsScalarTower A A[F] ((A[F])[F.secondStage c]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma fromSecondStage_nzd (i₀ : F.index) :
    ∀ u : PUnit, (F.toShift c) ((F.secondStage c).elem u) ∈
      nonZeroDivisors A[F.shift c] := by
  intro u
  rw [secondStage_elem, (F.toShift c).commutes]
  exact F.shift_c_nzd c i₀

lemma fromSecondStage_gen :
    ∀ u : PUnit, Ideal.map (F.toShift c).toRingHom ((F.secondStage c).ideal u) ≤
      Ideal.span {(F.toShift c) ((F.secondStage c).elem u)} := by
  intro u
  rw [secondStage_ideal, secondStage_elem, (F.toShift c).commutes,
    Ideal.map_le_iff_le_comap]
  refine F.genFracIdeal_le (fun i m hm => ?_)
  rw [Ideal.mem_comap]
  show F.toShift c (Dilatation.frac (F := F) (Finsupp.single i 1)
      ⟨m, F.mem_largeIdealPow_single i hm⟩) ∈ _
  rw [F.toShift_frac c i hm]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def fromSecondStage (i₀ : F.index) :
    (A[F])[F.secondStage c] →ₐ[A[F]] A[F.shift c] :=
  desc (F.secondStage c) (F.fromSecondStage_nzd c i₀)
    (fun u => (gen_iff_le (F.secondStage c) u).mpr (F.fromSecondStage_gen c u))

lemma twoStage_elem_nzd (i : F.index) :
    algebraMap A ((A[F])[F.secondStage c]) (F.elem i) ∈
      nonZeroDivisors ((A[F])[F.secondStage c]) :=
  Dilatation.nonzerodiv_of_nonzerodiv (F := F.secondStage c)
    (nonzerodiv_image_single F i)

lemma twoStage_c_nzd :
    algebraMap A ((A[F])[F.secondStage c]) c ∈
      nonZeroDivisors ((A[F])[F.secondStage c]) :=
  nonzerodiv_image_single (F.secondStage c) PUnit.unit

lemma toSecondStage_nzd :
    ∀ i, algebraMap A ((A[F])[F.secondStage c]) ((F.shift c).elem i) ∈
      nonZeroDivisors ((A[F])[F.secondStage c]) := by
  intro i
  rw [shift_elem, map_mul]
  exact mul_mem (F.twoStage_elem_nzd c i) (F.twoStage_c_nzd c)

lemma toSecondStage_gen :
    ∀ i, Ideal.span {algebraMap A ((A[F])[F.secondStage c]) ((F.shift c).elem i)} =
      Ideal.map (algebraMap A ((A[F])[F.secondStage c])) ((F.shift c).LargeIdeal i) := by
  intro i
  refine (gen_iff_le (F.shift c) i).mpr ?_
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap, shift_elem, map_mul]
  have hA := F.algebraMap_eq_pow_mul_frac (Finsupp.single i 1) m
    (F.mem_largeIdealPow_single i hm)
  rw [familyPow_single] at hA
  have hQ : algebraMap A[F] ((A[F])[F.secondStage c])
      (Dilatation.frac (F := F) (Finsupp.single i 1)
        ⟨m, F.mem_largeIdealPow_single i hm⟩) ∈
      Ideal.span {algebraMap A[F] ((A[F])[F.secondStage c])
        ((F.secondStage c).elem PUnit.unit)} :=
    Multicenter.self_le (F.secondStage c) PUnit.unit
      (Ideal.mem_map_of_mem _ (F.frac_mem_genFracIdeal i hm))
  rw [secondStage_elem] at hQ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hQ
  refine Ideal.mem_span_singleton'.mpr ⟨z, ?_⟩
  have hpush : algebraMap A ((A[F])[F.secondStage c]) m =
      algebraMap A ((A[F])[F.secondStage c]) (F.elem i) *
        algebraMap A[F] ((A[F])[F.secondStage c])
          (Dilatation.frac (F := F) (Finsupp.single i 1)
            ⟨m, F.mem_largeIdealPow_single i hm⟩) := by
    show algebraMap A[F] ((A[F])[F.secondStage c])
        (algebraMap A A[F] m) = _
    rw [hA, map_mul]
    rfl
  rw [hpush, ← hz,
    show algebraMap A[F] ((A[F])[F.secondStage c]) (algebraMap A A[F] c) =
      algebraMap A ((A[F])[F.secondStage c]) c from rfl]
  ring

def toSecondStage : A[F.shift c] →ₐ[A] (A[F])[F.secondStage c] :=
  desc (F.shift c) (F.toSecondStage_nzd c) (F.toSecondStage_gen c)

lemma toSecondStage_comp_toShift :
    (F.toSecondStage c).comp (F.toShift c) =
      IsScalarTower.toAlgHom A A[F] ((A[F])[F.secondStage c]) := by
  refine lemma_exists_unique_morphism' F (fun i => ?_) (fun i => ?_) _ _
  · exact F.twoStage_elem_nzd c i
  · refine (gen_iff_le F i).mpr ?_
    have hpush : Ideal.map (algebraMap A[F] ((A[F])[F.secondStage c]))
        (Ideal.map (algebraMap A A[F]) (F.ideal i)) <=
        Ideal.map (algebraMap A[F] ((A[F])[F.secondStage c]))
          (Ideal.span {algebraMap A A[F] (F.elem i)}) :=
      Ideal.map_mono (Multicenter.self_le F i)
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at hpush
    exact hpush

def toSecondStageB :
    A[F.shift c] →ₐ[A[F]] (A[F])[F.secondStage c] where
  toRingHom := (F.toSecondStage c).toRingHom
  commutes' b := by
    have h := DFunLike.congr_fun (F.toSecondStage_comp_toShift c) b
    simpa using h

lemma toSecondStageB_comp_fromSecondStage (i0 : F.index) :
    (F.toSecondStageB c).comp (F.fromSecondStage c i0) =
      AlgHom.id A[F] ((A[F])[F.secondStage c]) :=
  lemma_exists_unique_morphism' (F.secondStage c)
    (fun u => nonzerodiv_image_single (F.secondStage c) u)
    (fun u => reciprocal_for_univ (F.secondStage c)
      (AlgHom.id A[F] ((A[F])[F.secondStage c])) u) _ _

lemma fromSecondStage_comp_toSecondStage (i0 : F.index) :
    ((F.fromSecondStage c i0).restrictScalars A).comp (F.toSecondStage c) =
      AlgHom.id A A[F.shift c] :=
  lemma_exists_unique_morphism' (F.shift c)
    (fun i => nonzerodiv_image_single (F.shift c) i)
    (fun i => reciprocal_for_univ (F.shift c) (AlgHom.id A A[F.shift c]) i) _ _

def shiftEquiv (i0 : F.index) :
    (A[F])[F.secondStage c] ≃ₐ[A] A[F.shift c] :=
  AlgEquiv.ofAlgHom ((F.fromSecondStage c i0).restrictScalars A)
    (F.toSecondStage c)
    (F.fromSecondStage_comp_toSecondStage c i0)
    (AlgHom.ext fun x =>
      DFunLike.congr_fun (F.toSecondStageB_comp_fromSecondStage c i0) x)

lemma shiftEquiv_unique (i0 : F.index)
    (chi : (A[F])[F.secondStage c] →ₐ[A] A[F.shift c]) :
    chi = ((F.fromSecondStage c i0).restrictScalars A) := by
  have h1 : chi.comp (IsScalarTower.toAlgHom A A[F]
      ((A[F])[F.secondStage c])) = F.toShift c := by
    refine lemma_exists_unique_morphism' F (fun i => ?_) (fun i => ?_) _ _
    · exact F.shift_elem_nzd c i
    · exact F.toShift_gen c i
  let chiB : (A[F])[F.secondStage c] →ₐ[A[F]] A[F.shift c] :=
    AlgHom.mk chi.toRingHom (fun b => by
      have h := DFunLike.congr_fun h1 b
      simpa using h)
  have h2 : chiB = F.fromSecondStage c i0 :=
    lemma_exists_unique_morphism' (F.secondStage c)
      (F.fromSecondStage_nzd c i0)
      (fun u => (gen_iff_le (F.secondStage c) u).mpr
        (F.fromSecondStage_gen c u)) _ _
  exact AlgHom.ext fun x => DFunLike.congr_fun h2 x

section Powers

variable {A : Type (u+1)} [CommRing A]

def ofPowers {ι : Type} (M : ι → Ideal A) (a : A) (s : ι → ℕ) :
    Multicenter A where
  index := ι
  ideal := M
  elem i := a ^ s i

@[simp] lemma ofPowers_ideal {ι : Type} (M : ι → Ideal A) (a : A) (s : ι → ℕ)
    (i : ι) : (ofPowers M a s).ideal i = M i := rfl

@[simp] lemma ofPowers_elem {ι : Type} (M : ι → Ideal A) (a : A) (s : ι → ℕ)
    (i : ι) : (ofPowers M a s).elem i = a ^ s i := rfl

theorem ofPowers_shift {ι : Type} (M : ι → Ideal A) (a : A) (s : ι → ℕ) (t : ℕ) :
    (ofPowers M a s).shift (a ^ t) = ofPowers M a (fun i => s i + t) := by
  show Multicenter.mk ι M (fun i => a ^ s i * a ^ t) =
    Multicenter.mk ι M (fun i => a ^ (s i + t))
  congr 1
  exact funext fun i => (pow_add a (s i) t).symm

def powersShiftEquiv {ι : Type} (M : ι → Ideal A) (a : A)
    (s : ι → ℕ) (t : ℕ)
    (i₀ : ι) :
    (A[ofPowers M a s])[(ofPowers M a s).secondStage (a ^ t)] ≃ₐ[A]
      A[ofPowers M a (fun i => s i + t)] := by
  rw [← ofPowers_shift M a s t]
  exact (ofPowers M a s).shiftEquiv (a ^ t) i₀

end Powers

end Prop52

end Multicenter
