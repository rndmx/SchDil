import ReesMu
import ProjSurj
import HomogDecomp

suppress_compilation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

universe u

open HomogeneousSubmonoid AlgebraicGeometry CategoryTheory
open GoodPotionIngredient ReesCovering ChartBar
open scoped Family

namespace ReesChartCover

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : Type (u+1)} [CommRing A] (L : ι → Ideal A)
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

local notation "𝒜L" => ReesAlgebra.intGrading L

theorem gens_homogeneous (S : GoodPotionIngredient (𝒜L))
    (s : Finset (ReesAlgebra L)) (hs : Submonoid.closure (s : Set (ReesAlgebra L)) =
      S.toSubmonoid) :
    ∀ x ∈ (s : Set (ReesAlgebra L)), SetLike.IsHomogeneousElem (𝒜L) x := by
  intro x hx
  exact S.toHomogeneousSubmonoid.homogeneous
    (hs ▸ Submonoid.subset_closure hx : x ∈ S.toSubmonoid)

theorem prod_gens_mem (S : GoodPotionIngredient (𝒜L))
    (s : Finset (ReesAlgebra L)) (hs : Submonoid.closure (s : Set (ReesAlgebra L)) =
      S.toSubmonoid) :
    (∏ x ∈ s, x) ∈ S.toHomogeneousSubmonoid := by
  rw [show ((∏ x ∈ s, x) ∈ S.toHomogeneousSubmonoid) = ((∏ x ∈ s, x) ∈ S.toSubmonoid) from rfl,
    ← hs]
  exact Submonoid.prod_mem _ fun x hx => Submonoid.subset_closure hx

theorem bar_eq_gen_prod (S : GoodPotionIngredient (𝒜L))
    (s : Finset (ReesAlgebra L)) (hs : Submonoid.closure (s : Set (ReesAlgebra L)) =
      S.toSubmonoid) :
    S.toHomogeneousSubmonoid.bar =
      (gen (∏ x ∈ s, x) (isHomogeneousElem_prod s (gens_homogeneous L S s hs))).bar := by
  have hclos : HomogeneousSubmonoid.closure (s : Set (ReesAlgebra L))
      (gens_homogeneous L S s hs) = S.toHomogeneousSubmonoid := by
    apply HomogeneousSubmonoid.toSubmonoid_injective
    exact hs
  rw [← hclos]
  exact bar_closure_prod_eq s (gens_homogeneous L S s hs)

theorem prod_gens_not_nilpotent (S : GoodPotionIngredient (𝒜L))
    (s : Finset (ReesAlgebra L)) (hs : Submonoid.closure (s : Set (ReesAlgebra L)) =
      S.toSubmonoid)
    (x : Spec (CommRingCat.of (S.Potion))) (k : ℕ) : (∏ y ∈ s, y) ^ k ≠ 0 := by
  intro hk
  have h0 : (0 : ReesAlgebra L) ∈ S.toSubmonoid := by
    rw [← hk]
    exact pow_mem (prod_gens_mem L S s hs) k
  have : Subsingleton (S.Potion) := HomogeneousLocalization.subsingleton _ h0
  exact (inferInstanceAs (IsEmpty (PrimeSpectrum (S.Potion)))).elim x

theorem prod_gens_relevant (S : GoodPotionIngredient (𝒜L))
    (s : Finset (ReesAlgebra L)) (hs : Submonoid.closure (s : Set (ReesAlgebra L)) =
      S.toSubmonoid) :
    ElemIsRelevant (𝒜 := 𝒜L) (∏ x ∈ s, x)
      (isHomogeneousElem_prod s (gens_homogeneous L S s hs)) := by
  have hbar := bar_eq_gen_prod L S s hs
  intro i
  obtain ⟨n, hn, hmem⟩ := S.relevant i
  rw [hbar] at hmem
  exact ⟨n, hn, hmem⟩

theorem prodGen_relevant {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    (gen (prodGen L ha)
      ⟨ρNatToInt ι oneVec, ReesAlgebra.single_has_degree' L _ _⟩).IsRelevant := by
  have hbar := ReesMu.clo_mu_bar_eq' L ha
  intro i
  obtain ⟨n, hn, hmem⟩ := (map_index L (ReesMu.muOf L ha)).relevant i
  rw [show (map_index L (ReesMu.muOf L ha)).toHomogeneousSubmonoid =
    clo_mu L (ReesMu.muOf L ha) from rfl, hbar] at hmem
  exact ⟨n, hn, hmem⟩

theorem gen_fg {x : ReesAlgebra L} (hx : SetLike.IsHomogeneousElem (𝒜L) x) :
    (gen x hx).toSubmonoid.FG :=
  ⟨{x}, by simp [gen, HomogeneousSubmonoid.closure]⟩

theorem gen_congr {x y : ReesAlgebra L} (hx : SetLike.IsHomogeneousElem (𝒜L) x)
    (hy : SetLike.IsHomogeneousElem (𝒜L) y) (h : x = y) : gen x hx = gen y hy := by
  subst h; rfl

theorem range_mul_subset (m b : ReesAlgebra L)
    (hm : SetLike.IsHomogeneousElem (𝒜L) m) (hb : SetLike.IsHomogeneousElem (𝒜L) b)
    (hrelm : (gen m hm).IsRelevant) (hrelmb : (gen (b * m) (hb.mul hm)).IsRelevant) :
    Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
        ⟨gen (b * m) (hb.mul hm), hrelmb, gen_fg L _⟩).base ⊆
      Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
        ⟨gen m hm, hrelm, gen_fg L _⟩).base := by
  refine ProjChartRange.range_subset_of_bar_eq _ _ _ ?_
  show (gen (b * m) (hb.mul hm)).bar =
    ((gen (b * m) (hb.mul hm)) * (gen m hm)).bar
  rw [mul_comm (gen (b * m) (hb.mul hm)) (gen m hm)]
  have h := bar_gen_mul_left m b hm hb
  rw [gen_congr L (hm.mul hb) (hb.mul hm) (mul_comm m b)] at h
  exact h.symm

theorem range_prodGen_subset {a : ι → A} (ha : ∀ i, a i ∈ L i) :
    Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
        ⟨gen (prodGen L ha) ⟨ρNatToInt ι oneVec, ReesAlgebra.single_has_degree' L _ _⟩,
          prodGen_relevant L ha, gen_fg L _⟩).base ⊆
      Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
        (map_index L (ReesMu.muOf L ha))).base := by
  refine ProjChartRange.range_subset_of_bar_eq _ _ _ ?_
  refine (ChartEq.bar_mul_eq_of_bar_eq ?_).symm
  exact (ReesMu.clo_mu_bar_eq' L ha).symm

theorem covering (S : GoodPotionIngredient (𝒜L))
    (x : Spec (CommRingCat.of (S.Potion))) :
    ∃ T ∈ Set.range (map_index L),
      ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι S).base x ∈
        Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι T).base := by
  classical
  obtain ⟨s, hs⟩ := S.fg
  set f : ReesAlgebra L := ∏ y ∈ s, y with hfdef
  have hhom : SetLike.IsHomogeneousElem (𝒜L) f :=
    isHomogeneousElem_prod s (gens_homogeneous L S s hs)
  obtain ⟨d, hd⟩ := id hhom
  have hrel : ElemIsRelevant (𝒜 := 𝒜L) f hhom := prod_gens_relevant L S s hs
  have hnil : ∀ k : ℕ, f ^ k ≠ 0 := prod_gens_not_nilpotent L S s hs x
  have hfS : f ∈ S.toHomogeneousSubmonoid := prod_gens_mem L S s hs

  have hmem : f ∈ prodIdeal L := relevant_mem_prodIdeal L hhom hrel hnil

  obtain ⟨K, c, hKT, hc, hfsum⟩ :=
    HomogDecomp.exists_homogeneous_decomposition (𝒜 := 𝒜L) hd (prodGenSet L)
      (prodGenSet_homogeneous L) (by rwa [← prodIdeal_eq_span])

  set e : ι →₀ ℤ := ρNatToInt ι oneVec with he
  have hKe : ∀ j : {m // m ∈ K}, (j : ReesAlgebra L) ∈ 𝒜L e :=
    fun j => prodGenSet_homogeneous L _ (hKT j.2)
  have hG : ∀ j : {m // m ∈ K}, c j * (j : ReesAlgebra L) ∈ 𝒜L d := by
    intro j
    have := SetLike.mul_mem_graded (hc (j : ReesAlgebra L)) (hKe j)
    rwa [sub_add_cancel] at this
  have hsum : ∑ j ∈ (Finset.univ : Finset {m // m ∈ K}),
      c (j : ReesAlgebra L) * (j : ReesAlgebra L) = f := by
    rw [hfsum]
    exact Finset.sum_attach K (fun m => c m * m)
  have hrel' : ∀ j : {m // m ∈ K},
      (gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩).IsRelevant := by
    intro j
    obtain ⟨a, ha, hja⟩ := hKT j.2
    have hprod : (gen (j : ReesAlgebra L) ⟨e, hKe j⟩).IsRelevant := by
      intro i
      obtain ⟨n, hn, hmem⟩ := prodGen_relevant L ha i
      rw [← ChartBar.gen_congr' (𝒜 := 𝒜L) ⟨e, hKe j⟩ _ hja] at hmem
      exact ⟨n, hn, hmem⟩
    have hb := bar_gen_mul_left (j : ReesAlgebra L) (c (j : ReesAlgebra L)) ⟨e, hKe j⟩
      ⟨d - e, hc _⟩
    rw [gen_congr L _ ⟨d, hG j⟩ (mul_comm (j : ReesAlgebra L) (c (j : ReesAlgebra L)))] at hb
    have h1 : gen (j : ReesAlgebra L) ⟨e, hKe j⟩ ≤
        (gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩).bar := by
      calc gen (j : ReesAlgebra L) ⟨e, hKe j⟩
          ≤ gen (j : ReesAlgebra L) ⟨e, hKe j⟩ *
            gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩ := left_le_mul _ _
        _ ≤ (gen (j : ReesAlgebra L) ⟨e, hKe j⟩ *
            gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩).bar := le_bar _
        _ = (gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩).bar := hb
    have h2 : ((gen (c (j : ReesAlgebra L) * (j : ReesAlgebra L)) ⟨d, hG j⟩).bar).IsRelevant :=
      HomogeneousSubmonoid.IsRelevant.ofLE _ _ h1 hprod
    intro i
    obtain ⟨n, hn, hmem⟩ := h2 i
    rw [HomogeneousSubmonoid.bar_bar] at hmem
    exact ⟨n, hn, hmem⟩
  obtain ⟨j, -, hjmem⟩ := ProjChartRange.exists_chart_of_sum S hd hfS
    (Finset.univ : Finset {m // m ∈ K})
    (fun j => c (j : ReesAlgebra L) * (j : ReesAlgebra L)) hG hsum hrel'
    (fun j => gen_fg L _) x
  obtain ⟨a, ha, hja⟩ := hKT j.2
  refine ⟨map_index L (ReesMu.muOf L ha), ⟨ReesMu.muOf L ha, rfl⟩, ?_⟩
  have hprod : (gen (j : ReesAlgebra L) ⟨e, hKe j⟩).IsRelevant := by
    intro i
    obtain ⟨n, hn, hmem⟩ := prodGen_relevant L ha i
    rw [← ChartBar.gen_congr' (𝒜 := 𝒜L) ⟨e, hKe j⟩ _ hja] at hmem
    exact ⟨n, hn, hmem⟩

  have hstep1 := range_mul_subset L (j : ReesAlgebra L) (c (j : ReesAlgebra L))
    ⟨e, hKe j⟩ ⟨d - e, hc _⟩ hprod (hrel' j)

  have hbar : (gen (j : ReesAlgebra L) ⟨e, hKe j⟩).bar =
      (map_index L (ReesMu.muOf L ha)).toHomogeneousSubmonoid.bar := by
    rw [ChartBar.gen_congr' (𝒜 := 𝒜L) ⟨e, hKe j⟩
      ⟨ρNatToInt ι oneVec, ReesAlgebra.single_has_degree' L _ _⟩ hja]
    exact (ReesMu.clo_mu_bar_eq' L ha).symm
  have hstep2 : Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
      ⟨gen (j : ReesAlgebra L) ⟨e, hKe j⟩, hprod, gen_fg L _⟩).base ⊆
      Set.range ((glueData (id : GoodPotionIngredient (𝒜L) → _)).ι
        (map_index L (ReesMu.muOf L ha))).base := by
    refine ProjChartRange.range_subset_of_bar_eq _ _ _ ?_
    exact (ChartEq.bar_mul_eq_of_bar_eq hbar).symm
  exact hstep2 (hstep1 hjmem)

theorem surjective_projHom :
    Function.Surjective
      (projHomOfLE (ProjSurj.leOfSet (Set.range (map_index L)))).base :=
  ProjSurj.surjective_of_covering _ (covering L)

end ReesChartCover
