import Project.Dilatation.Multicenter
import Mathlib.RingTheory.Ideal.Colon
import MulticenterNonZeroDivisor
import MulticenterTower

suppress_compilation

universe u

open Family

namespace Multicenter

variable {A : Type (u+1)} [CommRing A] (F : Multicenter A)

open Dilatation

def multiple (ν : F.index → ℕ) : Multicenter A where
  index := F.index
  ideal := F.ideal
  elem i := F.elem i ^ ν i

@[simp] lemma multiple_index (ν : F.index → ℕ) : (F.multiple ν).index = F.index := rfl
@[simp] lemma multiple_ideal (ν : F.index → ℕ) (i : F.index) :
    (F.multiple ν).ideal i = F.ideal i := rfl
@[simp] lemma multiple_elem (ν : F.index → ℕ) (i : F.index) :
    (F.multiple ν).elem i = F.elem i ^ ν i := rfl

lemma algebraMap_eq_pow_mul_frac (w : F.index →₀ ℕ) (m : A) (hm : m ∈ F.LargeIdeal^w) :
    algebraMap A A[F] m =
      algebraMap A A[F] (F.elem^w) * ((⟨m, hm⟩ : F.LargeIdeal^w) /. w) := by
  simp only [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
  use 0
  simp
  ring

lemma mem_largeIdealPow_single (i : F.index) {m : A}
    (hm : m ∈ F.ideal i) :
    m ∈ F.LargeIdeal^((Finsupp.single i 1 : F.index →₀ ℕ)) := by
  rw [familyPow_single]
  have h : F.ideal i ≤ F.LargeIdeal i := by
    show F.ideal i ≤ F.ideal i + Ideal.span {F.elem i}
    rw [Submodule.add_eq_sup]
    exact le_sup_left
  exact h hm

def liftIdeal (ν : F.index → ℕ) (i : F.index) : Ideal A[F.multiple ν] :=
  Submodule.colon (Ideal.map (algebraMap A A[F.multiple ν]) (F.ideal i))
    (Submodule.span _ {algebraMap A A[F.multiple ν] (F.elem i ^ ν i)})

lemma mem_liftIdeal {ν : F.index → ℕ} {i : F.index} {x : A[F.multiple ν]} :
    x ∈ F.liftIdeal ν i ↔
      algebraMap A A[F.multiple ν] (F.elem i ^ ν i) * x ∈
        Ideal.map (algebraMap A A[F.multiple ν]) (F.ideal i) := by
  rw [liftIdeal, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]

lemma frac_mem_liftIdeal (ν : F.index → ℕ) (i : F.index) {m : A} (hm : m ∈ F.ideal i) :
    (Dilatation.frac ((Finsupp.single i 1 : (F.multiple ν).index →₀ ℕ))
      ⟨m, (F.multiple ν).mem_largeIdealPow_single i hm⟩) ∈ F.liftIdeal ν i := by
  rw [mem_liftIdeal]
  have hkey := (F.multiple ν).algebraMap_eq_pow_mul_frac
    (Finsupp.single i 1) m ((F.multiple ν).mem_largeIdealPow_single i hm)
  rw [familyPow_single, multiple_elem] at hkey
  rw [← hkey]
  exact Ideal.mem_map_of_mem _ hm

def iterated (ν n : F.index → ℕ) : Multicenter A[F.multiple ν] where
  index := F.index
  ideal := F.liftIdeal ν
  elem i := algebraMap A A[F.multiple ν] (F.elem i) ^ n i

@[simp] lemma iterated_ideal (ν n : F.index → ℕ) (i : F.index) :
    (F.iterated ν n).ideal i = F.liftIdeal ν i := rfl
@[simp] lemma iterated_elem (ν n : F.index → ℕ) (i : F.index) :
    (F.iterated ν n).elem i = algebraMap A A[F.multiple ν] (F.elem i) ^ n i := rfl

lemma nzd_of_pow_nzd {R : Type (u+1)} [CommRing R] {a : R} {k : ℕ} (hk : k ≠ 0)
    (h : a ^ k ∈ nonZeroDivisors R) : a ∈ nonZeroDivisors R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

lemma elem_pow_img_nzd (μ : F.index → ℕ) (i : F.index) (k : ℕ)
    (h : k = 0 ∨ μ i ≠ 0) :
    algebraMap A A[F.multiple μ] (F.elem i) ^ k ∈ nonZeroDivisors A[F.multiple μ] := by
  rcases h with h0 | hne
  · rw [h0, pow_zero]; exact Submonoid.one_mem _
  · have hbase : algebraMap A A[F.multiple μ] (F.elem i) ∈
        nonZeroDivisors A[F.multiple μ] := by
      have h1 := nonzerodiv_image_single (F.multiple μ) i
      rw [multiple_elem, map_pow] at h1
      exact nzd_of_pow_nzd hne h1
    exact pow_mem hbase k

variable (ν n : F.index → ℕ)

lemma sum_img_nzd (i : F.index) (k : ℕ) (hk : k = 0 ∨ (ν i + n i) ≠ 0) :
    algebraMap A A[F.multiple (ν + n)] (F.elem i) ^ k ∈
      nonZeroDivisors A[F.multiple (ν + n)] :=
  F.elem_pow_img_nzd (ν + n) i k (by simpa using hk)

lemma sum_self_le (i : F.index) :
    Ideal.map (algebraMap A A[F.multiple (ν + n)]) (F.ideal i) ≤
      Ideal.span {algebraMap A A[F.multiple (ν + n)] (F.elem i) ^ (ν i + n i)} := by
  have h := (gen_iff_le (F.multiple (ν + n)) i).mp
    (reciprocal_for_univ (F.multiple (ν + n))
      (AlgHom.id A A[F.multiple (ν + n)]) i)
  rw [multiple_elem, map_pow] at h
  simpa using h

noncomputable def stageOne : A[F.multiple ν] →ₐ[A] A[F.multiple (ν + n)] :=
  desc (F.multiple ν)
    (fun i => by
      rw [multiple_elem, map_pow]
      refine F.sum_img_nzd ν n i (ν i) ?_
      rcases Nat.eq_zero_or_pos (ν i) with h | h
      · exact Or.inl h
      · exact Or.inr (by omega))
    (fun i => (gen_iff_le (F.multiple ν) i).mpr (by
      rw [multiple_ideal, multiple_elem, map_pow]
      refine le_trans (F.sum_self_le ν n i) ?_
      exact Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow _ (Nat.le_add_right _ _))))

lemma stageOne_algebraMap (a : A) :
    F.stageOne ν n (algebraMap A A[F.multiple ν] a) =
      algebraMap A A[F.multiple (ν + n)] a :=
  F.stageOne ν n |>.commutes a

lemma twoStage_ideal_le (i : F.index) :
    Ideal.map (algebraMap A (A[F.multiple ν])[F.iterated ν n]) (F.ideal i) ≤
      Ideal.span {algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^
        (ν i + n i)} := by
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap, Ideal.mem_span_singleton']
  have hkeyB := (F.multiple ν).algebraMap_eq_pow_mul_frac
    (Finsupp.single i 1) m ((F.multiple ν).mem_largeIdealPow_single i hm)
  rw [familyPow_single, multiple_elem] at hkeyB
  have hfrac := F.frac_mem_liftIdeal ν i hm
  have hspan : algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
      (Dilatation.frac ((Finsupp.single i 1 : (F.multiple ν).index →₀ ℕ))
        ⟨m, (F.multiple ν).mem_largeIdealPow_single i hm⟩) ∈
      Ideal.span {algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
        ((F.iterated ν n).elem i)} := by
    refine (gen_iff_le (F.iterated ν n) i).mp
      (reciprocal_for_univ (F.iterated ν n)
        (AlgHom.id A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]) i) ?_
    exact Ideal.mem_map_of_mem _ hfrac
  rw [Ideal.mem_span_singleton'] at hspan
  obtain ⟨c, hc⟩ := hspan
  refine ⟨c, ?_⟩
  have hcomp : algebraMap A (A[F.multiple ν])[F.iterated ν n] m =
      algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
        (algebraMap A A[F.multiple ν] m) := rfl
  rw [hcomp, hkeyB, map_mul, ← hc]
  have he : algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
      ((F.iterated ν n).elem i) =
      algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ n i := by
    rw [iterated_elem, map_pow]
    rfl
  have ha : algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
      (algebraMap A A[F.multiple ν] (F.elem i ^ ν i)) =
      algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ ν i := by
    rw [map_pow, map_pow]
    rfl
  rw [he, ha, pow_add]
  ring

lemma twoStage_img_nzd (i : F.index) (k : ℕ) (hk : k = 0 ∨ ν i + n i ≠ 0) :
    algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ k ∈
      nonZeroDivisors ((A[F.multiple ν])[F.iterated ν n]) := by
  rcases hk with h0 | hne
  · rw [h0, pow_zero]; exact Submonoid.one_mem _
  ·
    have hν : algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ ν i ∈
        nonZeroDivisors ((A[F.multiple ν])[F.iterated ν n]) := by
      have hB : algebraMap A A[F.multiple ν] (F.elem i ^ ν i) ∈
          nonZeroDivisors A[F.multiple ν] := by
        have h1 := nonzerodiv_image_single (F.multiple ν) i
        rwa [multiple_elem] at h1
      have h2 := Dilatation.nonzerodiv_of_nonzerodiv (F := F.iterated ν n) hB
      rwa [show algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
          (algebraMap A A[F.multiple ν] (F.elem i ^ ν i)) =
          algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ ν i by
        rw [map_pow, map_pow]; rfl] at h2
    have hn : algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ n i ∈
        nonZeroDivisors ((A[F.multiple ν])[F.iterated ν n]) := by
      have h1 := nonzerodiv_image_single (F.iterated ν n) i
      rwa [show algebraMap A[F.multiple ν] (A[F.multiple ν])[F.iterated ν n]
          ((F.iterated ν n).elem i) =
          algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^ n i by
        rw [iterated_elem, map_pow]; rfl] at h1
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero]; exact Submonoid.one_mem _
    · have hsum : algebraMap A (A[F.multiple ν])[F.iterated ν n] (F.elem i) ^
          (ν i + n i) ∈ nonZeroDivisors ((A[F.multiple ν])[F.iterated ν n]) := by
        rw [pow_add]; exact mul_mem hν hn
      have hbase := nzd_of_pow_nzd hne hsum
      exact pow_mem hbase k

noncomputable def toTwoStage :
    A[F.multiple (ν + n)] →ₐ[A] (A[F.multiple ν])[F.iterated ν n] :=
  desc (F.multiple (ν + n))
    (fun i => by
      rw [multiple_elem, map_pow]
      refine F.twoStage_img_nzd ν n i ((ν + n) i) ?_
      rcases Nat.eq_zero_or_pos ((ν + n) i) with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [Pi.add_apply] at h ⊢; omega))
    (fun i => (gen_iff_le (F.multiple (ν + n)) i).mpr (by
      rw [multiple_ideal, multiple_elem, map_pow]
      have h := F.twoStage_ideal_le ν n i
      simpa using h))

noncomputable local instance stageAlgebra :
    Algebra A[F.multiple ν] A[F.multiple (ν + n)] :=
  (F.stageOne ν n).toRingHom.toAlgebra

lemma fromTwoStage_nzd (i : F.index) :
    (F.stageOne ν n) ((F.iterated ν n).elem i) ∈
      nonZeroDivisors A[F.multiple (ν + n)] := by
  rw [iterated_elem, map_pow, stageOne_algebraMap]
  refine F.sum_img_nzd ν n i (n i) ?_
  rcases Nat.eq_zero_or_pos (n i) with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

lemma fromTwoStage_gen (i : F.index) :
    Ideal.map (F.stageOne ν n).toRingHom ((F.iterated ν n).ideal i) ≤
      Ideal.span {(F.stageOne ν n) ((F.iterated ν n).elem i)} := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [iterated_ideal, mem_liftIdeal] at hx
  rw [Ideal.mem_comap]
  have hψ : (F.stageOne ν n) (algebraMap A A[F.multiple ν] (F.elem i ^ ν i) * x) ∈
      Ideal.map (algebraMap A A[F.multiple (ν + n)]) (F.ideal i) := by
    have h1 : (F.stageOne ν n) (algebraMap A A[F.multiple ν] (F.elem i ^ ν i) * x) ∈
        Ideal.map (F.stageOne ν n).toRingHom
          (Ideal.map (algebraMap A A[F.multiple ν]) (F.ideal i)) :=
      Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_map] at h1
    rwa [show (F.stageOne ν n).toRingHom.comp
        (algebraMap A A[F.multiple ν]) =
        algebraMap A A[F.multiple (ν + n)] from
      RingHom.ext fun a => (F.stageOne ν n).commutes a] at h1
  have h2 := F.sum_self_le ν n i hψ
  rw [pow_add, ← Ideal.span_singleton_mul_span_singleton] at h2
  obtain ⟨c, hc, hce⟩ := Ideal.mem_span_singleton_mul.mp h2
  have hnzd : algebraMap A A[F.multiple (ν + n)] (F.elem i) ^ ν i ∈
      nonZeroDivisors A[F.multiple (ν + n)] := by
    refine F.sum_img_nzd ν n i (ν i) ?_
    rcases Nat.eq_zero_or_pos (ν i) with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hψx : (F.stageOne ν n) (algebraMap A A[F.multiple ν] (F.elem i ^ ν i) * x) =
      algebraMap A A[F.multiple (ν + n)] (F.elem i) ^ ν i * (F.stageOne ν n) x := by
    rw [map_mul, stageOne_algebraMap, map_pow]
  rw [hψx] at hce
  have hsub : algebraMap A A[F.multiple (ν + n)] (F.elem i) ^ ν i *
      (c - (F.stageOne ν n) x) = 0 := by
    rw [mul_sub, hce, sub_self]
  have hcψ : c = (F.stageOne ν n) x :=
    sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd).mp hsub)
  show (F.stageOne ν n) x ∈
    Ideal.span {(F.stageOne ν n) ((F.iterated ν n).elem i)}
  rw [iterated_elem, map_pow, stageOne_algebraMap]
  exact hcψ ▸ hc

noncomputable def fromTwoStage :
    (A[F.multiple ν])[F.iterated ν n] →ₐ[A[F.multiple ν]] A[F.multiple (ν + n)] :=
  desc (F.iterated ν n) (F.fromTwoStage_nzd ν n)
    (fun i => (gen_iff_le (F.iterated ν n) i).mpr (F.fromTwoStage_gen ν n i))

noncomputable local instance : Algebra A[F.multiple ν] A[F.multiple (ν + n)] :=
  (F.stageOne ν n).toRingHom.toAlgebra

local instance : IsScalarTower A A[F.multiple ν] A[F.multiple (ν + n)] :=
  IsScalarTower.of_algebraMap_eq fun a => ((F.stageOne ν n).commutes a).symm

local instance : IsScalarTower A A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma twoStage_stageElem_nzd (i : F.index) :
    algebraMap A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n])
      (algebraMap A A[F.multiple ν] ((F.multiple ν).elem i)) ∈
      nonZeroDivisors ((A[F.multiple ν])[F.iterated ν n]) :=
  Dilatation.nonzerodiv_of_nonzerodiv (F := F.iterated ν n)
    (nonzerodiv_image_single (F.multiple ν) i)

lemma toTwoStage_comp_stageOne :
    (F.toTwoStage ν n).comp (F.stageOne ν n) =
      IsScalarTower.toAlgHom A A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n]) := by
  refine lemma_exists_unique_morphism' (F.multiple ν) (fun i => ?_) (fun i => ?_) _ _
  ·
    have h := F.twoStage_stageElem_nzd ν n i
    rwa [show algebraMap A ((A[F.multiple ν])[F.iterated ν n])
        ((F.multiple ν).elem i) =
        algebraMap A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n])
          (algebraMap A A[F.multiple ν] ((F.multiple ν).elem i)) from rfl]
  · refine (gen_iff_le (F.multiple ν) i).mpr ?_
    rw [multiple_ideal, multiple_elem, map_pow]
    refine le_trans (F.twoStage_ideal_le ν n i) ?_
    exact Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow _ (Nat.le_add_right _ _))

noncomputable def toTwoStageB :
    A[F.multiple (ν + n)] →ₐ[A[F.multiple ν]] (A[F.multiple ν])[F.iterated ν n] where
  toRingHom := (F.toTwoStage ν n).toRingHom
  commutes' b := by
    have h := DFunLike.congr_fun (F.toTwoStage_comp_stageOne ν n) b
    simpa using h

lemma toTwoStageB_comp_fromTwoStage :
    (F.toTwoStageB ν n).comp (F.fromTwoStage ν n) =
      AlgHom.id A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n]) :=
  lemma_exists_unique_morphism' (F.iterated ν n)
    (fun i => nonzerodiv_image_single (F.iterated ν n) i)
    (fun i => reciprocal_for_univ (F.iterated ν n)
      (AlgHom.id A[F.multiple ν] ((A[F.multiple ν])[F.iterated ν n])) i) _ _

lemma fromTwoStage_comp_toTwoStage :
    ((F.fromTwoStage ν n).restrictScalars A).comp (F.toTwoStage ν n) =
      AlgHom.id A A[F.multiple (ν + n)] :=
  lemma_exists_unique_morphism' (F.multiple (ν + n))
    (fun i => nonzerodiv_image_single (F.multiple (ν + n)) i)
    (fun i => reciprocal_for_univ (F.multiple (ν + n))
      (AlgHom.id A A[F.multiple (ν + n)]) i) _ _

noncomputable def iterateEquiv :
    (A[F.multiple ν])[F.iterated ν n] ≃ₐ[A] A[F.multiple (ν + n)] :=
  AlgEquiv.ofAlgHom ((F.fromTwoStage ν n).restrictScalars A) (F.toTwoStage ν n)
    (F.fromTwoStage_comp_toTwoStage ν n)
    (AlgHom.ext fun x =>
      DFunLike.congr_fun (F.toTwoStageB_comp_fromTwoStage ν n) x)

lemma iterateEquiv_unique
    (χ : (A[F.multiple ν])[F.iterated ν n] →ₐ[A] A[F.multiple (ν + n)]) :
    χ = ((F.fromTwoStage ν n).restrictScalars A) := by
  have h1 : χ.comp (IsScalarTower.toAlgHom A A[F.multiple ν]
      ((A[F.multiple ν])[F.iterated ν n])) = F.stageOne ν n := by
    refine lemma_exists_unique_morphism' (F.multiple ν) (fun i => ?_) (fun i => ?_) _ _
    · rw [multiple_elem, map_pow]
      refine F.sum_img_nzd ν n i (ν i) ?_
      rcases Nat.eq_zero_or_pos (ν i) with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · refine (gen_iff_le (F.multiple ν) i).mpr ?_
      rw [multiple_ideal, multiple_elem, map_pow]
      refine le_trans (F.sum_self_le ν n i) ?_
      exact Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow _ (Nat.le_add_right _ _))
  let χB : (A[F.multiple ν])[F.iterated ν n] →ₐ[A[F.multiple ν]]
      A[F.multiple (ν + n)] :=
    AlgHom.mk χ.toRingHom (fun b => by
      have h := DFunLike.congr_fun h1 b
      simpa using h)
  have h2 : χB = F.fromTwoStage ν n :=
    lemma_exists_unique_morphism' (F.iterated ν n) (F.fromTwoStage_nzd ν n)
      (fun i => (gen_iff_le (F.iterated ν n) i).mpr (F.fromTwoStage_gen ν n i)) _ _
  exact AlgHom.ext fun x => DFunLike.congr_fun h2 x

end Multicenter
