import PolyptychKernelFormula

/-!
# The panelization isomorphism, ring level (Theorem 3.7)

Ring-level form of Proposition `theopanelization-mor` and Theorem `theo-iso-panelization`
of Dubouloz-Mayeux, *A polyptych of multi-centered deformation spaces* (arXiv:2411.15606).

Fix a deformation datum `(M, d)` on `A` indexed by a finite totally ordered set `I`,
satisfying Assumption 3.1 (`Cartier`), and a subset `J ⊆ I`.  The `J`-th panel of the
deformation space is the second-stage dilatation

`B_J = R_J[{ ker (F_J(i)^*) / σ_J^*(∏_{s ∈ (I∖J)≥i} d_s) }_{i ∈ I∖J}]`

of `R_J` along the panel centers (`panelCenter` / `PanelRing`).

* `theta` — the panelization homomorphism `Θ_J^* : R_I → B_J` of Proposition 3.2, obtained
  from the universal property of `R_I`; the required containments are `panel_map_M_le`,
  proved by the four case distinctions `eq:Inclus-I-1`, `eq:inclus-I-2`, `eq:inclus-J-1`,
  `eq:inclus-J-2` of the paper, all reduced to the single "anchor" lemma
  `algebraMap_mem_mul_ker`.
* `upsilonPanel` — the inverse `Υ_I^* : B_J → R_I` of Theorem 3.7, obtained from the
  universal property of `B_J`; the required containment `upsilon_ker_le` is exactly where
  the kernel formula `ker_panelHom_eq` is used, term by term as in `eq:term-1`,
  `eq:term-2-case1`, `eq:term-2-case2`.
* `panelizationEquiv` — **Theorem 3.7**: `B_J ≃ₐ[A] R_I`, with `panelizationEquiv_unique`.
* `condR1_of_gt`, `condR2_of_gt` — **Corollary `KsupS`**: if `(I∖J) > J` then the datum is
  automatically dilatation-regular with respect to `J`.
-/

suppress_compilation

universe u

open Family Multicenter Dilatation

namespace Polyptych

variable {A : Type (u+1)} [CommRing A] {I : Type} [LinearOrder I] [Fintype I]
variable (M : I → Ideal A) (d : I → A)

section ElemOf

/-- Splitting the divisor of `k` in `K` into its `J`-part and its `K ∖ J`-part. -/
lemma elemOf_mul_of_subset {J K : Finset I} (hJK : J ⊆ K) (k : I) :
    elemOf d K k = elemOf d J k * elemOf d (K \ J) k := by
  classical
  have hsplit : K.filter (fun s => k ≤ s) =
      J.filter (fun s => k ≤ s) ∪ (K \ J).filter (fun s => k ≤ s) := by
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset hJK]
  have hdisj : Disjoint (J.filter (fun s => k ≤ s)) ((K \ J).filter (fun s => k ≤ s)) := by
    refine Finset.disjoint_left.mpr fun a ha ha' => ?_
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha').1).2 (Finset.mem_filter.mp ha).1
  simp only [elemOf, hsplit]
  exact Finset.prod_union hdisj

/-- The divisor of a larger index divides the divisor of a smaller one. -/
lemma elemOf_dvd_of_le (S : Finset I) {a b : I} (hab : a ≤ b) :
    elemOf d S b ∣ elemOf d S a := by
  classical
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, le_trans hab hs.2⟩

/-- If `j₀` is the least element of `S≥k`, then `S≥j₀ = S≥k`. -/
lemma elemOf_eq_of_min (S : Finset I) (k j₀ : I) (hkj₀ : k ≤ j₀)
    (hmin : ∀ s ∈ S, k ≤ s → j₀ ≤ s) : elemOf d S j₀ = elemOf d S k := by
  classical
  simp only [elemOf]
  congr 1
  ext s
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, le_trans hkj₀ h.2⟩, fun h => ⟨h.1, hmin s h.1 h.2⟩⟩

/-- If `S≥k` is empty the divisor of `k` in `S` is `1`. -/
lemma elemOf_eq_one (S : Finset I) (k : I)
    (h : S.filter (fun s => k ≤ s) = ∅) : elemOf d S k = 1 := by
  simp only [elemOf, h, Finset.prod_empty]

end ElemOf

/-- `𝔻_I` at ring level: the deformation space of the whole index set. -/
abbrev Full : Type (u+1) := Ring M d (Finset.univ : Finset I)

/-- `I ∖ J`. -/
abbrev Comp (J : Finset I) : Finset I := (Finset.univ : Finset I) \ J

/-- `υ_{I,J} : R_J → R_I`. -/
def upsilonFull (J : Finset I) : (Ring M d J) →ₐ[A] Full M d :=
  upsilon M d (Finset.subset_univ J)

variable {M d}

/-- `R_I` is an `R_J`-algebra via `υ_{I,J}`. -/
local instance instAlgFull (J : Finset I) : Algebra (Ring M d J) (Full M d) :=
  (upsilonFull M d J).toRingHom.toAlgebra

local instance instTowerFull (J : Finset I) : IsScalarTower A (Ring M d J) (Full M d) :=
  IsScalarTower.of_algebraMap_eq fun a => ((upsilonFull M d J).commutes a).symm

lemma algebraMap_full_apply (J : Finset I) (x : Ring M d J) :
    algebraMap (Ring M d J) (Full M d) x = upsilonFull M d J x := rfl

@[simp] lemma upsilonFull_algebraMap (J : Finset I) (a : A) :
    upsilonFull M d J (algebraMap A (Ring M d J) a) = algebraMap A (Full M d) a :=
  (upsilonFull M d J).commutes a

@[simp] lemma algebraMap_full_comp (J : Finset I) (a : A) :
    algebraMap (Ring M d J) (Full M d) (algebraMap A (Ring M d J) a) =
      algebraMap A (Full M d) a := (upsilonFull M d J).commutes a

/-- **The panel multicenter** on `R_J`: index `I ∖ J`, ideals the kernels `ker F_J(i)^*`,
distinguished elements `σ_J^*(∏_{s ∈ (I∖J)≥i} d_s)`. -/
def panelCenter (hC : Cartier M d) (J : Finset I) : Multicenter (Ring M d J) where
  index := {i // i ∈ Comp J}
  ideal i := RingHom.ker (panelHom M d hC J i.1)
  elem i := algebraMap A (Ring M d J) (elemOf d (Comp J) i.1)

/-- `B_J = 𝔻𝔻_J` at ring level. -/
abbrev PanelRing (hC : Cartier M d) (J : Finset I) : Type (u+1) :=
  (Ring M d J)[panelCenter hC J]

@[simp] lemma panelCenter_ideal (hC : Cartier M d) (J : Finset I)
    (i : (panelCenter hC J).index) :
    (panelCenter hC J).ideal i = RingHom.ker (panelHom M d hC J i.1) := rfl

@[simp] lemma panelCenter_elem (hC : Cartier M d) (J : Finset I)
    (i : (panelCenter hC J).index) :
    (panelCenter hC J).elem i = algebraMap A (Ring M d J) (elemOf d (Comp J) i.1) := rfl

local instance instTowerPanel (hC : Cartier M d) (J : Finset I) :
    IsScalarTower A (Ring M d J) (PanelRing hC J) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

section NonZeroDivisors

/-- Every `d s` is a non-zero-divisor in `B_J`. -/
lemma algebraMap_d_nzd_panel (hC : Cartier M d) (J : Finset I) (s : I) :
    algebraMap A (PanelRing hC J) (d s) ∈ nonZeroDivisors (PanelRing hC J) := by
  classical
  by_cases hsJ : s ∈ J
  · exact Dilatation.nonzerodiv_of_nonzerodiv (F := panelCenter hC J)
      (algebraMap_d_nzd M d J s hsJ)
  · have hsC : s ∈ Comp J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, hsJ⟩
    obtain ⟨c, hc⟩ := d_dvd_elemOf d (Comp J) s hsC
    have h := nonzerodiv_image_single (panelCenter hC J) ⟨s, hsC⟩
    have hrw : algebraMap (Ring M d J) (PanelRing hC J)
        ((panelCenter hC J).elem ⟨s, hsC⟩) =
        algebraMap A (PanelRing hC J) (d s) * algebraMap A (PanelRing hC J) c := by
      show algebraMap A (PanelRing hC J) (elemOf d (Comp J) s) = _
      rw [hc, map_mul]
    rw [hrw] at h
    exact (mul_mem_nonZeroDivisors.mp h).1

/-- Every divisor `∏_{s ∈ S≥k} d_s` is a non-zero-divisor in `B_J`. -/
lemma algebraMap_elemOf_nzd_panel (hC : Cartier M d) (J S : Finset I) (k : I) :
    algebraMap A (PanelRing hC J) (elemOf d S k) ∈ nonZeroDivisors (PanelRing hC J) := by
  classical
  simp only [elemOf, map_prod]
  exact prod_mem fun s _ => algebraMap_d_nzd_panel hC J s

end NonZeroDivisors

section Theta

/-- **The anchor lemma**: if `m ∈ M j₀ ∩ M i` with `j₀ ∈ J`, then
`σ_J^*(m) ∈ (σ_J^*(∏_{s ∈ J≥j₀} d_s)) · ker(F_J(i)^*)`.  This packages the four
inclusions `eq:Inclus-I-1`–`eq:inclus-J-2` in the proof of Proposition 3.2. -/
lemma algebraMap_mem_mul_ker (hC : Cartier M d) (J : Finset I) (i : I)
    (j₀ : (restCenter M d J).index) {m : A} (hmj : m ∈ M j₀.1) (hmi : m ∈ M i) :
    algebraMap A (Ring M d J) m ∈
      Ideal.span {algebraMap A (Ring M d J) (elemOf d J j₀.1)} *
        RingHom.ker (panelHom M d hC J i) := by
  have hmL : m ∈ ((restCenter M d J).LargeIdeal ^
      (Finsupp.single j₀ 1 : (restCenter M d J).index →₀ ℕ) : Ideal A) :=
    (restCenter M d J).mem_largeIdealPow_single j₀ hmj
  have hkey := (restCenter M d J).algebraMap_eq_pow_mul_frac
    (Finsupp.single j₀ 1) m hmL
  rw [familyPow_single] at hkey
  rw [hkey]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
    (panelSubIdeal_le_ker M d hC J i
      (frac_single_mem_panelSubIdeal M d J i j₀ m hmj hmi hmL))

/-- **The containment `eq:inclusion_ideals-3.5(ii)`**: in `B_J` the image of `M k` is
contained in the ideal generated by `ρ_J^*(∏_{s ∈ I≥k} d_s)`, for every `k ∈ I`. -/
theorem panel_map_M_le (hC : Cartier M d) (hM : Mono M) (J : Finset I) (k : I) :
    Ideal.map (algebraMap A (PanelRing hC J)) (M k) ≤
      Ideal.span {algebraMap A (PanelRing hC J)
        (elemOf d (Finset.univ : Finset I) k)} := by
  classical
  -- reduce to producing an intermediate ideal `N` of `R_J`
  have step : ∀ N : Ideal (Ring M d J),
      Ideal.map (algebraMap A (Ring M d J)) (M k) ≤
        Ideal.span {algebraMap A (Ring M d J) (elemOf d J k)} * N →
      Ideal.map (algebraMap (Ring M d J) (PanelRing hC J)) N ≤
        Ideal.span {algebraMap A (PanelRing hC J) (elemOf d (Comp J) k)} →
      Ideal.map (algebraMap A (PanelRing hC J)) (M k) ≤
        Ideal.span {algebraMap A (PanelRing hC J)
          (elemOf d (Finset.univ : Finset I) k)} := by
    intro N h1 h2
    have hcomp : (algebraMap A (PanelRing hC J)) =
        (algebraMap (Ring M d J) (PanelRing hC J)).comp
          (algebraMap A (Ring M d J)) := rfl
    calc Ideal.map (algebraMap A (PanelRing hC J)) (M k)
        = Ideal.map (algebraMap (Ring M d J) (PanelRing hC J))
            (Ideal.map (algebraMap A (Ring M d J)) (M k)) := by
          rw [hcomp, Ideal.map_map]
      _ ≤ Ideal.map (algebraMap (Ring M d J) (PanelRing hC J))
            (Ideal.span {algebraMap A (Ring M d J) (elemOf d J k)} * N) :=
          Ideal.map_mono h1
      _ = Ideal.span {algebraMap A (PanelRing hC J) (elemOf d J k)} *
            Ideal.map (algebraMap (Ring M d J) (PanelRing hC J)) N := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
          rfl
      _ ≤ Ideal.span {algebraMap A (PanelRing hC J) (elemOf d J k)} *
            Ideal.span {algebraMap A (PanelRing hC J) (elemOf d (Comp J) k)} :=
          Ideal.mul_mono le_rfl h2
      _ = Ideal.span {algebraMap A (PanelRing hC J)
            (elemOf d (Finset.univ : Finset I) k)} := by
          rw [Ideal.span_singleton_mul_span_singleton, ← map_mul,
            ← elemOf_mul_of_subset d (Finset.subset_univ J) k]
  by_cases hkJ : k ∈ J
  · -- `k ∈ J`: cases `eq:inclus-J-1` and `eq:inclus-J-2`
    by_cases hne : ((Comp J).filter (fun s => k ≤ s)).Nonempty
    · obtain ⟨i₀, hi₀mem⟩ : ∃ i₀, i₀ = ((Comp J).filter (fun s => k ≤ s)).min' hne :=
        ⟨_, rfl⟩
      have hi₀f : i₀ ∈ (Comp J).filter (fun s => k ≤ s) := by
        rw [hi₀mem]; exact Finset.min'_mem _ hne
      have hi₀C : i₀ ∈ Comp J := (Finset.mem_filter.mp hi₀f).1
      have hki₀ : k ≤ i₀ := (Finset.mem_filter.mp hi₀f).2
      have hmin : ∀ s ∈ Comp J, k ≤ s → i₀ ≤ s := by
        intro s hs hks
        rw [hi₀mem]
        exact Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hks⟩)
      have heq : elemOf d (Comp J) i₀ = elemOf d (Comp J) k :=
        elemOf_eq_of_min d (Comp J) k i₀ hki₀ hmin
      refine step (RingHom.ker (panelHom M d hC J i₀)) ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [Ideal.mem_comap]
        exact algebraMap_mem_mul_ker hC J i₀ ⟨k, hkJ⟩ hm (hM hki₀ hm)
      · rw [← heq]
        exact Multicenter.self_le (panelCenter hC J) ⟨i₀, hi₀C⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine step ⊤ ?_ ?_
      · rw [Ideal.mul_top]
        exact Multicenter.self_le (restCenter M d J) ⟨k, hkJ⟩
      · rw [elemOf_eq_one d (Comp J) k hne, map_one, Ideal.span_singleton_one]
        exact le_top
  · -- `k ∈ I ∖ J`: cases `eq:Inclus-I-1` and `eq:inclus-I-2`
    have hkC : k ∈ Comp J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkJ⟩
    refine step (RingHom.ker (panelHom M d hC J k)) ?_ ?_
    · by_cases hne : (J.filter (fun s => k ≤ s)).Nonempty
      · obtain ⟨j₀, hj₀mem⟩ : ∃ j₀, j₀ = (J.filter (fun s => k ≤ s)).min' hne := ⟨_, rfl⟩
        have hj₀f : j₀ ∈ J.filter (fun s => k ≤ s) := by
          rw [hj₀mem]; exact Finset.min'_mem _ hne
        have hj₀J : j₀ ∈ J := (Finset.mem_filter.mp hj₀f).1
        have hkj₀ : k ≤ j₀ := (Finset.mem_filter.mp hj₀f).2
        have hmin : ∀ s ∈ J, k ≤ s → j₀ ≤ s := by
          intro s hs hks
          rw [hj₀mem]
          exact Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hks⟩)
        have heq : elemOf d J j₀ = elemOf d J k := elemOf_eq_of_min d J k j₀ hkj₀ hmin
        rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [Ideal.mem_comap, ← heq]
        exact algebraMap_mem_mul_ker hC J k ⟨j₀, hj₀J⟩ (hM hkj₀ hm) hm
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [elemOf_eq_one d J k hne, map_one, Ideal.span_singleton_one, Ideal.top_mul]
        exact le_trans le_sup_left (panelSubIdeal_le_ker M d hC J k)
    · exact Multicenter.self_le (panelCenter hC J) ⟨k, hkC⟩

/-- Restricted form of `panel_map_M_le` used for the `J`-indices. -/
lemma panel_map_M_le_J (hC : Cartier M d) (hM : Mono M) (J : Finset I) (k : I) :
    Ideal.map (algebraMap A (PanelRing hC J)) (M k) ≤
      Ideal.span {algebraMap A (PanelRing hC J) (elemOf d J k)} := by
  refine le_trans (panel_map_M_le hC hM J k) ?_
  obtain ⟨c, hc⟩ := elemOf_dvd_of_subset d (Finset.subset_univ J) k
  rw [hc, map_mul]
  exact Ideal.span_singleton_le_span_singleton.mpr ⟨_, rfl⟩

/-- **`Θ_J^* : R_I → B_J`**, the panelization homomorphism of Proposition 3.2. -/
def theta (hC : Cartier M d) (hM : Mono M) (J : Finset I) :
    (Full M d) →ₐ[A] (PanelRing hC J) :=
  desc (restCenter M d (Finset.univ : Finset I))
    (fun k => algebraMap_elemOf_nzd_panel hC J (Finset.univ : Finset I) k.1)
    (fun k => (gen_iff_le (restCenter M d (Finset.univ : Finset I)) k).mpr
      (panel_map_M_le hC hM J k.1))

end Theta

section Upsilon

/-- **The containment of Theorem 3.7**: `υ_{I,J}(ker F_J(i)^*)` is contained in the ideal
generated by `σ_I^*(∏_{s ∈ (I∖J)≥i} d_s)`.  This is where the kernel formula enters. -/
theorem upsilon_ker_le (hC : Cartier M d) (hM : Mono M) (J : Finset I) (i : I)
    (hiC : i ∈ Comp J) (hR1 : CondR1 M J i) (hR2 : CondR2 M d J i) :
    Ideal.map (algebraMap (Ring M d J) (Full M d))
        (RingHom.ker (panelHom M d hC J i)) ≤
      Ideal.span {algebraMap A (Full M d) (elemOf d (Comp J) i)} := by
  classical
  have hiJ : i ∉ J := (Finset.mem_sdiff.mp hiC).2
  have hEnzd : ∀ j : I, algebraMap A (Full M d) (elemOf d J j) ∈
      nonZeroDivisors (Full M d) :=
    fun j => algebraMap_elemOf_nzd M d (Finset.subset_univ J) j
  rw [ker_panelHom_eq hC hM J i hiJ hR1 hR2, panelSubIdeal, Ideal.map_le_iff_le_comap]
  refine sup_le ?_ (iSup_le fun j => ?_)
  · -- `eq:term-1`
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, Ideal.mem_comap, algebraMap_full_comp]
    have h1 : algebraMap A (Full M d) m ∈
        Ideal.span {algebraMap A (Full M d)
          (elemOf d (Finset.univ : Finset I) i)} :=
      Multicenter.self_le (restCenter M d (Finset.univ : Finset I))
        ⟨i, Finset.mem_univ i⟩ (Ideal.mem_map_of_mem _ hm)
    rw [elemOf_mul_of_subset d (Finset.subset_univ J) i, map_mul] at h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h1
    exact Ideal.mem_span_singleton'.mpr
      ⟨w * algebraMap A (Full M d) (elemOf d J i), by rw [← hw]; ring⟩
  · -- `eq:term-2-case1` and `eq:term-2-case2`
    rw [Ideal.span_le]
    rintro x ⟨m, hmj, hmi, rfl⟩
    have hmL : m ∈ ((restCenter M d J).LargeIdeal ^
        (Finsupp.single j 1 : (restCenter M d J).index →₀ ℕ) : Ideal A) :=
      (restCenter M d J).mem_largeIdealPow_single j hmj
    have hkey := (restCenter M d J).algebraMap_eq_pow_mul_frac
      (Finsupp.single j 1) m hmL
    rw [familyPow_single] at hkey
    have hkey' : algebraMap A (Ring M d J) m =
        algebraMap A (Ring M d J) (elemOf d J j.1) *
          Dilatation.frac (F := restCenter M d J) (Finsupp.single j 1) ⟨m, hmL⟩ := hkey
    have hup := congrArg (upsilonFull M d J) hkey'
    rw [map_mul, upsilonFull_algebraMap, upsilonFull_algebraMap] at hup
    -- pick the right "anchor" index `t` according to the position of `j` relative to `i`
    obtain ⟨t, c, hmt, ht⟩ : ∃ (t : I) (c : A), m ∈ M t ∧
        elemOf d (Finset.univ : Finset I) t =
          elemOf d J j.1 * (elemOf d (Comp J) i * c) := by
      by_cases hij : i ≤ j.1
      · obtain ⟨c, hc⟩ := elemOf_dvd_of_le d J hij
        refine ⟨i, c, hmi, ?_⟩
        rw [elemOf_mul_of_subset d (Finset.subset_univ J) i, hc]; ring
      · obtain ⟨c, hc⟩ := elemOf_dvd_of_le d (Comp J) (le_of_not_le hij)
        refine ⟨j.1, c, hmj, ?_⟩
        rw [elemOf_mul_of_subset d (Finset.subset_univ J) j.1, hc]
    have hmem : algebraMap A (Full M d) m ∈
        Ideal.span {algebraMap A (Full M d)
          (elemOf d (Finset.univ : Finset I) t)} :=
      Multicenter.self_le (restCenter M d (Finset.univ : Finset I))
        ⟨t, Finset.mem_univ t⟩ (Ideal.mem_map_of_mem _ hmt)
    rw [ht, map_mul, map_mul] at hmem
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    -- cancel the non-zero-divisor `σ_I^*(∏_{s ∈ J≥j} d_s)`
    have hcancel : upsilonFull M d J
        (Dilatation.frac (F := restCenter M d J) (Finsupp.single j 1) ⟨m, hmL⟩) =
        w * algebraMap A (Full M d) c *
          algebraMap A (Full M d) (elemOf d (Comp J) i) := by
      refine (mul_cancel_left_mem_nonZeroDivisors (hEnzd j.1)).mp ?_
      rw [← hup, ← hw]
      ring
    rw [SetLike.mem_coe, Ideal.mem_comap, algebraMap_full_apply, hcancel]
    exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩

/-- **`Υ_I^* : B_J → R_I`**, the inverse of the panelization homomorphism. -/
def upsilonPanel (hC : Cartier M d) (hM : Mono M) (J : Finset I)
    (hR1 : ∀ i ∈ Comp J, CondR1 M J i) (hR2 : ∀ i ∈ Comp J, CondR2 M d J i) :
    (PanelRing hC J) →ₐ[Ring M d J] (Full M d) :=
  desc (panelCenter hC J)
    (fun i => by
      rw [panelCenter_elem, algebraMap_full_comp]
      exact algebraMap_elemOf_nzd M d (Finset.subset_univ (Comp J)) i.1)
    (fun i => (gen_iff_le (panelCenter hC J) i).mpr (by
      rw [panelCenter_ideal, panelCenter_elem, algebraMap_full_comp]
      exact upsilon_ker_le hC hM J i.1 i.2 (hR1 i.1 i.2) (hR2 i.1 i.2)))

end Upsilon

section Iso

variable (hC : Cartier M d) (hM : Mono M) (J : Finset I)
  (hR1 : ∀ i ∈ Comp J, CondR1 M J i) (hR2 : ∀ i ∈ Comp J, CondR2 M d J i)

include hC hM in
/-- `Θ_J^*` restricted along `υ_{I,J}` is the canonical map `R_J → B_J`. -/
theorem theta_comp_upsilonFull :
    (theta hC hM J).comp (upsilonFull M d J) =
      IsScalarTower.toAlgHom A (Ring M d J) (PanelRing hC J) :=
  lemma_exists_unique_morphism' (restCenter M d J)
    (fun j => algebraMap_elemOf_nzd_panel hC J J j.1)
    (fun j => (gen_iff_le (restCenter M d J) j).mpr (panel_map_M_le_J hC hM J j.1)) _ _

include hC hM in
/-- `Θ_J^*` as a map of `R_J`-algebras. -/
def thetaB : (Full M d) →ₐ[Ring M d J] (PanelRing hC J) where
  toRingHom := (theta hC hM J).toRingHom
  commutes' b := by
    have h := DFunLike.congr_fun (theta_comp_upsilonFull hC hM J) b
    simpa using h

include hC hM hR1 hR2 in
/-- `Θ_J^* ∘ Υ_I^* = id` on `B_J`. -/
theorem thetaB_comp_upsilonPanel :
    (thetaB hC hM J).comp (upsilonPanel hC hM J hR1 hR2) =
      AlgHom.id (Ring M d J) (PanelRing hC J) :=
  lemma_exists_unique_morphism' (panelCenter hC J)
    (fun i => nonzerodiv_image_single (panelCenter hC J) i)
    (fun i => reciprocal_for_univ (panelCenter hC J)
      (AlgHom.id (Ring M d J) (PanelRing hC J)) i) _ _

include hC hM hR1 hR2 in
/-- `Υ_I^* ∘ Θ_J^* = id` on `R_I`. -/
theorem upsilonPanel_comp_theta :
    ((upsilonPanel hC hM J hR1 hR2).restrictScalars A).comp (theta hC hM J) =
      AlgHom.id A (Full M d) :=
  lemma_exists_unique_morphism' (restCenter M d (Finset.univ : Finset I))
    (fun k => nonzerodiv_image_single (restCenter M d (Finset.univ : Finset I)) k)
    (fun k => reciprocal_for_univ (restCenter M d (Finset.univ : Finset I))
      (AlgHom.id A (Full M d)) k) _ _

include hC hM hR1 hR2 in
/-- **Theorem 3.7, ring level**: for a deformation datum satisfying Assumption 3.1 and
dilatation-regular with respect to `J`, the panelization homomorphism is an isomorphism

`Θ_J : 𝔻𝔻_J ≅ 𝔻_I`. -/
def panelizationEquiv : (PanelRing hC J) ≃ₐ[A] (Full M d) :=
  AlgEquiv.ofAlgHom ((upsilonPanel hC hM J hR1 hR2).restrictScalars A) (theta hC hM J)
    (upsilonPanel_comp_theta hC hM J hR1 hR2)
    (AlgHom.ext fun x =>
      DFunLike.congr_fun (thetaB_comp_upsilonPanel hC hM J hR1 hR2) x)

include hC hM in
/-- The panelization isomorphism is the unique `A`-algebra homomorphism `R_I → B_J`
(uniqueness in Proposition 3.2). -/
theorem theta_unique (χ : (Full M d) →ₐ[A] (PanelRing hC J)) : χ = theta hC hM J :=
  lemma_exists_unique_morphism' (restCenter M d (Finset.univ : Finset I))
    (fun k => algebraMap_elemOf_nzd_panel hC J (Finset.univ : Finset I) k.1)
    (fun k => (gen_iff_le (restCenter M d (Finset.univ : Finset I)) k).mpr
      (panel_map_M_le hC hM J k.1)) _ _

include hC hM hR1 hR2 in
@[simp] theorem panelizationEquiv_symm_apply (x : Full M d) :
    (panelizationEquiv hC hM J hR1 hR2).symm x = theta hC hM J x := rfl

end Iso

section AutoRegular

/-- **Corollary `KsupS`, condition `(R₁)`**: if every index outside `J` dominates every
index of `J`, then `(R₁)` holds vacuously. -/
theorem condR1_of_gt (J : Finset I) (i : I) (hi : ∀ j ∈ J, j < i) : CondR1 M J i := by
  intro j₀ _ hj₀ _
  exact absurd (hi j₀.1 j₀.2) (not_lt.mpr (le_of_lt hj₀))

/-- **Corollary `KsupS`, condition `(R₂)`**: likewise `(R₂)` holds vacuously, its guard
`J≥i ≠ ∅` being unsatisfiable. -/
theorem condR2_of_gt (J : Finset I) (i : I) (hi : ∀ j ∈ J, j < i) : CondR2 M d J i := by
  intro hguard
  obtain ⟨s, hs⟩ := hguard
  rw [Finset.mem_filter] at hs
  exact absurd (hi s hs.1) (not_lt.mpr hs.2)

/-- **Corollary `KsupS`**: a deformation datum satisfying Assumption 3.1 is automatically
dilatation-regular with respect to any `J` with `(I ∖ J) > J`, so the panelization
homomorphism is then an isomorphism unconditionally. -/
def panelizationEquivOfGt (hC : Cartier M d) (hM : Mono M) (J : Finset I)
    (hgt : ∀ i ∈ Comp J, ∀ j ∈ J, j < i) :
    (PanelRing hC J) ≃ₐ[A] (Full M d) :=
  panelizationEquiv hC hM J (fun i hi => condR1_of_gt J i (hgt i hi))
    (fun i hi => condR2_of_gt J i (hgt i hi))

end AutoRegular

end Polyptych
