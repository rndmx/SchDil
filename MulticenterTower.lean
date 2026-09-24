import Project.Dilatation.Multicenter

suppress_compilation

universe u

open DirectSum Family

section AppendixC

open Family

namespace Multicenter

section restrict

variable {A' : Type (u+1)} [CommRing A'] (M : Multicenter A') (K : Set M.index)

def restrict : Multicenter A' where
  index := K
  ideal := fun i => M.ideal i.1
  elem  := fun i => M.elem i.1

@[simp] lemma restrict_ideal (i : K) : (M.restrict K).ideal i = M.ideal i.1 := rfl
@[simp] lemma restrict_elem (i : K) : (M.restrict K).elem i = M.elem i.1 := rfl
@[simp] lemma restrict_LargeIdeal (i : K) :
    (M.restrict K).LargeIdeal i = M.LargeIdeal i.1 := rfl

def complement : Multicenter (A'[M.restrict K]) where
  index := (Kᶜ : Set M.index)
  ideal := fun j => Ideal.map (algebraMap A' A'[M.restrict K]) (M.ideal j.1)
  elem  := fun j => algebraMap A' A'[M.restrict K] (M.elem j.1)

@[simp] lemma complement_ideal (j : (Kᶜ : Set M.index)) :
    (M.complement K).ideal j = Ideal.map (algebraMap A' A'[M.restrict K]) (M.ideal j.1) := rfl

@[simp] lemma complement_elem (j : (Kᶜ : Set M.index)) :
    (M.complement K).elem j = algebraMap A' A'[M.restrict K] (M.elem j.1) := rfl

end restrict

lemma gen_iff_le {A' B' : Type (u+1)} [CommRing A'] [CommRing B'] [Algebra A' B']
    (M : Multicenter A') (i : M.index) :
    Ideal.span {(algebraMap A' B') (M.elem i)} =
        Ideal.map (algebraMap A' B') (M.LargeIdeal i) ↔
      Ideal.map (algebraMap A' B') (M.ideal i) ≤
        Ideal.span {(algebraMap A' B') (M.elem i)} := by
  rw [LargeIdeal, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  constructor
  · intro h; rw [h]; exact le_sup_left
  · intro h; exact (sup_eq_right.mpr h).symm

namespace Dilatation

lemma nonzerodiv_algebraMap_of_mem_nonZeroDivisors {A' : Type (u+1)} [CommRing A']
    {M : Multicenter A'} {c : A'} (hc : c ∈ nonZeroDivisors A') :
    algebraMap A' A'[M] c ∈ nonZeroDivisors A'[M] := by
  have key : ∀ x : A'[M], x * algebraMap A' A'[M] c = 0 → x = 0 := by
    intro x h
    induction x using induction_on with
    | h x =>
      simp only [algebraMap_apply, mk_mul_mk, zero_def, mk_eq_mk] at h
      obtain ⟨β, hβ⟩ := h
      simp only [mul'_num, mul'_pow, add_zero, zero_mul] at hβ
      have hβ' : c * (x.num * M.elem ^ β) = 0 := by rw [← hβ]; ring
      have hx0 : x.num * M.elem ^ β = 0 := (mem_nonZeroDivisors_iff.mp hc).1 _ hβ'
      simp only [zero_def, mk_eq_mk]
      exact ⟨β, by simp [hx0]⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

end Dilatation

lemma nonzerodiv_image_single {A' : Type (u+1)} [CommRing A'] (M : Multicenter A')
    (i : M.index) : algebraMap A' A'[M] (M.elem i) ∈ nonZeroDivisors A'[M] := by
  have h := Multicenter.Dilatation.nonzerodiv_image (F := M) (Finsupp.single i 1)
  rwa [familyPow_single] at h

end Multicenter

section Prop224

open Multicenter Multicenter.Dilatation

variable {A' : Type (u+1)} [CommRing A'] (M : Multicenter A') (K : Set M.index)

local notation "B224" => A'[Multicenter.restrict M K]
local notation "C224" =>
  (A'[Multicenter.restrict M K])[Multicenter.complement M K]

def psi224 : B224 →ₐ[A'] A'[M] :=
  Multicenter.desc (M.restrict K)
    (fun i => nonzerodiv_image_single M i.1)
    (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i.1)

instance algebra224 : Algebra B224 A'[M] := (psi224 M K).toRingHom.toAlgebra

lemma algebraMap224_eq : (algebraMap B224 A'[M]) = (psi224 M K).toRingHom := rfl

instance scalarTower224 : IsScalarTower A' B224 A'[M] :=
  IsScalarTower.of_algebraMap_eq fun a => ((psi224 M K).commutes a).symm

instance algebra224' : Algebra A' C224 :=
  ((algebraMap B224 C224).comp (algebraMap A' B224)).toAlgebra

instance scalarTower224' : IsScalarTower A' B224 C224 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma hnzd_chi (j : (Multicenter.complement M K).index) :
    (algebraMap B224 A'[M]) ((Multicenter.complement M K).elem j) ∈ nonZeroDivisors A'[M] := by
  rw [algebraMap224_eq, complement_elem]
  show psi224 M K (algebraMap A' B224 (M.elem j.1)) ∈ nonZeroDivisors A'[M]
  rw [(psi224 M K).commutes]
  exact nonzerodiv_image_single M j.1

lemma hgen_chi (j : (Multicenter.complement M K).index) :
    Ideal.span {(algebraMap B224 A'[M]) ((Multicenter.complement M K).elem j)} =
      Ideal.map (algebraMap B224 A'[M]) ((Multicenter.complement M K).LargeIdeal j) := by
  rw [gen_iff_le, complement_ideal, complement_elem, Ideal.map_map]
  have hcomm : (algebraMap B224 A'[M]).comp (algebraMap A' B224) = algebraMap A' A'[M] :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply A' B224 A'[M] a).symm
  rw [hcomm, show (algebraMap B224 A'[M]) (algebraMap A' B224 (M.elem j.1)) =
      algebraMap A' A'[M] (M.elem j.1) from
    (IsScalarTower.algebraMap_apply A' B224 A'[M] (M.elem j.1)).symm]
  exact (gen_iff_le M j.1).mp (reciprocal_for_univ M (AlgHom.id A' A'[M]) j.1)

lemma hnzd_rho (i : M.index) :
    (algebraMap A' C224) (M.elem i) ∈ nonZeroDivisors C224 := by
  rw [IsScalarTower.algebraMap_apply A' B224 C224]
  by_cases hi : i ∈ K
  ·
    exact nonzerodiv_algebraMap_of_mem_nonZeroDivisors
      (nonzerodiv_image_single (M.restrict K) (⟨i, hi⟩ : K))
  ·
    exact nonzerodiv_image_single (Multicenter.complement M K) (⟨i, hi⟩ : (Kᶜ : Set M.index))

lemma hgen_rho (i : M.index) :
    Ideal.span {(algebraMap A' C224) (M.elem i)} =
      Ideal.map (algebraMap A' C224) (M.LargeIdeal i) := by
  rw [gen_iff_le, IsScalarTower.algebraMap_eq A' B224 C224, ← Ideal.map_map, RingHom.comp_apply]
  by_cases hi : i ∈ K
  · have h : Ideal.map (algebraMap A' B224) (M.ideal i) ≤
        Ideal.span {(algebraMap A' B224) (M.elem i)} :=
      (gen_iff_le (M.restrict K) (⟨i, hi⟩ : K)).mp
        (reciprocal_for_univ (M.restrict K) (AlgHom.id A' B224) (⟨i, hi⟩ : K))
    calc Ideal.map (algebraMap B224 C224) (Ideal.map (algebraMap A' B224) (M.ideal i))
        ≤ Ideal.map (algebraMap B224 C224) (Ideal.span {(algebraMap A' B224) (M.elem i)}) :=
          Ideal.map_mono h
      _ = Ideal.span {(algebraMap B224 C224) ((algebraMap A' B224) (M.elem i))} := by
          rw [Ideal.map_span, Set.image_singleton]
  · have h : Ideal.map (algebraMap B224 C224)
        ((Multicenter.complement M K).ideal (⟨i, hi⟩ : (Kᶜ : Set M.index))) ≤
          Ideal.span {(algebraMap B224 C224)
            ((Multicenter.complement M K).elem (⟨i, hi⟩ : (Kᶜ : Set M.index)))} :=
      (gen_iff_le (Multicenter.complement M K) (⟨i, hi⟩ : (Kᶜ : Set M.index))).mp
        (reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224)
          (⟨i, hi⟩ : (Kᶜ : Set M.index)))
    exact h

def chi224 : C224 →ₐ[B224] A'[M] :=
  Multicenter.desc (Multicenter.complement M K) (hnzd_chi M K) (hgen_chi M K)

def rho224 : A'[M] →ₐ[A'] C224 :=
  Multicenter.desc M (hnzd_rho M K) (hgen_rho M K)

lemma rho224_psi224 (b : B224) : rho224 M K (psi224 M K b) = algebraMap B224 C224 b := by
  have h1 := Multicenter.lemma_exists_unique_morphism (M.restrict K)
    (fun i => hnzd_rho M K i.1) (fun i => hgen_rho M K i.1)
    ((rho224 M K).comp (psi224 M K))
  have h2 := Multicenter.lemma_exists_unique_morphism (M.restrict K)
    (fun i => hnzd_rho M K i.1) (fun i => hgen_rho M K i.1)
    (IsScalarTower.toAlgHom A' B224 C224)
  exact AlgHom.congr_fun (h1.trans h2.symm) b

def prop_2_24 : C224 ≃ₐ[B224] A'[M] where
  toFun := chi224 M K
  invFun := rho224 M K
  left_inv := by
    have hcommutes : ∀ b : B224,
        (rho224 M K) ((chi224 M K) (algebraMap B224 C224 b)) = algebraMap B224 C224 b := by
      intro b
      rw [(chi224 M K).commutes b, algebraMap224_eq]
      exact rho224_psi224 M K b
    let composite : C224 →ₐ[B224] C224 :=
      { toFun := fun y => rho224 M K (chi224 M K y)
        map_one' := by simp
        map_mul' := by intro x y; simp
        map_zero' := by simp
        map_add' := by intro x y; simp
        commutes' := hcommutes }
    have h1 := Multicenter.lemma_exists_unique_morphism (Multicenter.complement M K)
      (fun j => nonzerodiv_image_single (Multicenter.complement M K) j)
      (fun j => reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224) j)
      composite
    have h2 := Multicenter.lemma_exists_unique_morphism (Multicenter.complement M K)
      (fun j => nonzerodiv_image_single (Multicenter.complement M K) j)
      (fun j => reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224) j)
      (AlgHom.id B224 C224)
    intro y
    exact AlgHom.congr_fun (h1.trans h2.symm) y
  right_inv := by
    have h1 := Multicenter.lemma_exists_unique_morphism M
      (fun i => nonzerodiv_image_single M i)
      (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i)
      (((chi224 M K).restrictScalars A').comp (rho224 M K))
    have h2 := Multicenter.lemma_exists_unique_morphism M
      (fun i => nonzerodiv_image_single M i)
      (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i)
      (AlgHom.id A' A'[M])
    intro x
    exact AlgHom.congr_fun (h1.trans h2.symm) x
  map_mul' := map_mul (chi224 M K)
  map_add' := map_add (chi224 M K)
  commutes' := (chi224 M K).commutes

theorem chi224_unique (f : C224 →ₐ[B224] A'[M]) : f = chi224 M K :=
  Multicenter.lemma_exists_unique_morphism _ (hnzd_chi M K) (hgen_chi M K) f

theorem prop_2_24_unique (e : C224 ≃ₐ[B224] A'[M]) : e = prop_2_24 M K := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun (chi224_unique M K e.toAlgHom) x

theorem prop_2_24_existsUnique :
    ∃! e : C224 ≃ₐ[B224] A'[M],
      ∀ b : B224, e (algebraMap B224 C224 b) = algebraMap B224 A'[M] b :=
  ⟨prop_2_24 M K, (prop_2_24 M K).commutes, fun e _ => prop_2_24_unique M K e⟩

end Prop224

end AppendixC
