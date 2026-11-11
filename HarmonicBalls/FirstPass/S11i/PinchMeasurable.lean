import HarmonicBalls.FirstPass.S11i.CanonicalGood
import HarmonicBalls.Steps.Sec11.PinchJointMeasure

/-!
# Measurability of the pinch events in `(ω, z)` (open item `hpin` of `CanonicalGood`)

Each supremum or infimum in `pinchPointEvent` runs over an affine image `x ↦ r x + z` of a fixed set, or over a
product of two such images. For a continuous integrand it equals its value over a countable dense subset of the
fixed set (`iSup_eq_of_closure`, `sInf_image_eq_of_closure`), so it is a countable `⨆`/`⨅` of functions that are
measurable in `(ω, z)`. The annular Green potential is measurable by `measurable_kernel_annulusGreenPotentialSup`.
No measurability of `T`, `Q'`, `Q` is used; `U` enters only through `κ ω (rescaledSet U r z)`.
-/

namespace HarmonicBalls.PinchMeasurable

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11n

section Density

variable {X : Type*} [TopologicalSpace X]

/-- Every subset of `ℂ` contains a countable subset with the same closure-hull. -/
lemma exists_countable_subset_closure (A : Set ℂ) : ∃ C ⊆ A, C.Countable ∧ A ⊆ closure C := by
  obtain ⟨t, ht, hts, hA⟩ := TopologicalSpace.exists_countable_dense_subset A
  exact ⟨t, hts, ht, hA⟩

/-- A supremum of a continuous `ℝ≥0∞`-valued function over `A` equals its supremum over any `C ⊆ A`
with `A ⊆ closure C`. -/
lemma iSup_eq_of_closure {f : X → ℝ≥0∞} (hf : Continuous f) {A C : Set X} (hCA : C ⊆ A)
    (hA : A ⊆ closure C) : (⨆ x ∈ A, f x) = ⨆ x ∈ C, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => le_iSup₂_of_le x (hCA hx) le_rfl)
  have hsub : C ⊆ {y | f y ≤ ⨆ c ∈ C, f c} := fun c hc => le_iSup₂ (f := fun c (_ : c ∈ C) => f c) c hc
  exact closure_minimal hsub (isClosed_le hf continuous_const) (hA hx)

/-- The real infimum (`sInf` of the image) of a continuous function over `A` equals its value over any
`C ⊆ A` with `A ⊆ closure C`; the empty and unbounded-below cases are covered by the convention `sInf = 0`. -/
lemma sInf_image_eq_of_closure {g : X → ℝ} (hg : Continuous g) {A C : Set X} (hCA : C ⊆ A)
    (hA : A ⊆ closure C) : sInf (g '' A) = sInf (g '' C) := by
  by_cases hb : BddBelow (g '' C)
  · have hbA : BddBelow (g '' A) := by
      obtain ⟨m, hm⟩ := hb
      refine ⟨m, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hsub : g '' C ⊆ {y | m ≤ y} := fun y hy => hm hy
      exact closure_minimal hsub (isClosed_le continuous_const continuous_id)
        (image_closure_subset_closure_image hg ⟨x, hA hx, rfl⟩)
    rcases A.eq_empty_or_nonempty with hAe | hAne
    · have hCe : C = ∅ := subset_empty_iff.1 (hAe ▸ hCA)
      simp [hAe, hCe]
    · have hCne : C.Nonempty := closure_nonempty_iff.mp (hAne.mono hA)
      refine le_antisymm (csInf_le_csInf hbA (hCne.image g) (image_mono hCA)) ?_
      refine le_csInf (hAne.image g) ?_
      rintro _ ⟨x, hx, rfl⟩
      have hsub : g '' C ⊆ {y | sInf (g '' C) ≤ y} := fun y hy => csInf_le hb hy
      exact closure_minimal hsub (isClosed_le continuous_const continuous_id)
        (image_closure_subset_closure_image hg ⟨x, hA hx, rfl⟩)
  · have hbA : ¬ BddBelow (g '' A) := fun h => hb (h.mono (image_mono hCA))
    rw [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hbA]

/-- Countable parametrised form of the real infimum: `sInf (g '' A) = ⨅ s : S₀, g (ψ s)` whenever the
parameters `ψ s` for `s ∈ S₀` lie in `A` and `A ⊆ closure (ψ '' S₀)`. -/
lemma sInf_image_eq_iInf {σ : Type*} {g : X → ℝ} (hg : Continuous g) (ψ : σ → X) (S₀ : Set σ) {A : Set X}
    (hsub : ∀ s ∈ S₀, ψ s ∈ A) (hdense : A ⊆ closure (ψ '' S₀)) :
    sInf (g '' A) = ⨅ s : S₀, g (ψ s) := by
  have hCA : ψ '' S₀ ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hsub s hs
  rw [sInf_image_eq_of_closure hg hCA hdense, Set.image_image, Set.image_eq_range]
  rfl

/-- Countable parametrised form of the supremum: `⨆ x ∈ A, f x = ⨆ s : S₀, f (ψ s)`. -/
lemma iSup_image_eq_iSup {σ : Type*} {f : X → ℝ≥0∞} (hf : Continuous f) (ψ : σ → X) (S₀ : Set σ) {A : Set X}
    (hsub : ∀ s ∈ S₀, ψ s ∈ A) (hdense : A ⊆ closure (ψ '' S₀)) :
    (⨆ x ∈ A, f x) = ⨆ s : S₀, f (ψ s) := by
  have hCA : ψ '' S₀ ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hsub s hs
  rw [iSup_eq_of_closure hf hCA hdense, iSup_image, iSup_subtype']

/-- A double supremum over `A × A` is the supremum over the product. -/
lemma iSup_prod_eq {F : ℂ → ℂ → ℝ≥0∞} {A : Set ℂ} :
    (⨆ x ∈ A, ⨆ y ∈ A, F x y) = ⨆ q ∈ A ×ˢ A, F q.1 q.2 :=
  le_antisymm (iSup₂_le fun x hx => iSup₂_le fun y hy => le_iSup₂_of_le (x, y) ⟨hx, hy⟩ le_rfl)
    (iSup₂_le fun q hq => le_iSup₂_of_le q.1 hq.1 (le_iSup₂_of_le q.2 hq.2 le_rfl))

end Density

section Affine

/-- Affine images preserve the closure relation `A ⊆ closure C`. -/
lemma affine_closure {A C : Set ℂ} {r : ℝ} {z : ℂ} (hA : A ⊆ closure C) :
    (fun x : ℂ => (r : ℂ) * x + z) '' A ⊆ closure ((fun x : ℂ => (r : ℂ) * x + z) '' C) := by
  have hc : Continuous fun x : ℂ => (r : ℂ) * x + z := by fun_prop
  exact (image_mono hA).trans (image_closure_subset_closure_image hc)

/-- The sphere `sphere z ρ` is the affine image of the unit circle (`rescaledSet` form). -/
lemma sphere_eq_affine {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    sphere z ρ = (fun x : ℂ => (ρ : ℂ) * x + z) '' sphere (0 : ℂ) 1 := by
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  ext x
  constructor
  · intro hx
    have hx' : ‖x - z‖ = ρ := by simpa [dist_eq_norm] using hx
    refine ⟨(x - z) / ρ, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, hx', Complex.norm_real, Real.norm_of_nonneg hρ.le,
        div_self hρ.ne']
    · show (ρ : ℂ) * ((x - z) / ρ) + z = x
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hρc, sub_add_cancel]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hw
    show (ρ : ℂ) * w + z ∈ sphere z ρ
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_right, norm_mul, hw, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]

/-- The frontier commutes with the affine map `x ↦ r x + z` (a homeomorphism for `r ≠ 0`). -/
lemma frontier_affine {Q : Set ℂ} {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    frontier ((fun x : ℂ => (r : ℂ) * x + z) '' Q) = (fun x : ℂ => (r : ℂ) * x + z) '' frontier Q := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let h : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) hr').trans (Homeomorph.addRight z)
  have hh : (⇑h) = fun x : ℂ => (r : ℂ) * x + z := by
    funext x
    simp [h]
  rw [← hh]
  exact (h.image_frontier Q).symm

/-- Membership in an affine image, as a condition on the preimage. -/
lemma mem_affine_image_iff {U : Set ℂ} {r : ℝ} (hr : r ≠ 0) (z y : ℂ) :
    y ∈ (fun x : ℂ => (r : ℂ) * x + z) '' U ↔ (r : ℂ)⁻¹ * (y - z) ∈ U := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  constructor
  · rintro ⟨x, hx, rfl⟩
    show (r : ℂ)⁻¹ * ((r : ℂ) * x + z - z) ∈ U
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hr', one_mul]
    exact hx
  · intro hy
    refine ⟨(r : ℂ)⁻¹ * (y - z), hy, ?_⟩
    show (r : ℂ) * ((r : ℂ)⁻¹ * (y - z)) + z = y
    rw [← mul_assoc, mul_inv_cancel₀ hr', one_mul, sub_add_cancel]

/-- Products of affine images: the product of the two closures is the closure of the image of the product. -/
lemma prod_affine_closure {A B C D : Set ℂ} {f : ℂ → ℂ} (hA : A ⊆ closure (f '' C))
    (hB : B ⊆ closure (f '' D)) :
    A ×ˢ B ⊆ closure ((fun q : ℂ × ℂ => (f q.1, f q.2)) '' (C ×ˢ D)) := by
  rw [← Set.prod_image_image_eq, closure_prod_eq]
  exact Set.prod_mono hA hB

/-- The `setDist` of two sets, parametrised by a countable family of pairs. -/
lemma setDist_eq_iInf (D : ℂ → ℂ → ℝ) (hD : Continuous fun q : ℂ × ℂ => D q.1 q.2) {A B : Set ℂ} {σ : Type*}
    (ψ : σ → ℂ × ℂ) (S₀ : Set σ) (hsub : ∀ s ∈ S₀, ψ s ∈ A ×ˢ B)
    (hdense : A ×ˢ B ⊆ closure (ψ '' S₀)) :
    setDist D A B = ⨅ s : S₀, D (ψ s).1 (ψ s).2 := by
  unfold setDist
  rw [← Set.image_uncurry_prod]
  exact sInf_image_eq_iInf hD ψ S₀ hsub hdense

/-- The `setDist` from a point to a set, parametrised by a countable family of points. -/
lemma setDist_singleton_eq_iInf (D : ℂ → ℂ → ℝ) (hD : Continuous fun q : ℂ × ℂ => D q.1 q.2) (z : ℂ)
    {B : Set ℂ} {σ : Type*} (ψ : σ → ℂ) (S₀ : Set σ) (hsub : ∀ s ∈ S₀, ψ s ∈ B)
    (hdense : B ⊆ closure (ψ '' S₀)) : setDist D {z} B = ⨅ s : S₀, D z (ψ s) := by
  unfold setDist
  rw [Set.image2_singleton_left]
  exact sInf_image_eq_iInf (g := fun x => D z x) (hD.comp (continuous_const.prodMk continuous_id)) ψ S₀
    hsub hdense

end Affine

section Joint

variable {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}

/-- `(ω, z) ↦ D ω z (a + z)`: a jointly measurable metric evaluated at a moving point. -/
lemma measurable_D_point (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2) (a : ℂ) :
    Measurable fun p : Ω × ℂ => D p.1 p.2 (a + p.2) :=
  hDm.comp (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const.add measurable_snd)))

/-- `(ω, z) ↦ D ω (a + z) (b + z)`: a jointly measurable metric evaluated at two moving points. -/
lemma measurable_D_shift (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2) (a b : ℂ) :
    Measurable fun p : Ω × ℂ => D p.1 (a + p.2) (b + p.2) :=
  hDm.comp (measurable_fst.prodMk
    ((measurable_const.add measurable_snd).prodMk (measurable_const.add measurable_snd)))

/-- The supremum over the sphere `sphere z ρ` of `D ω z ·` is measurable in `(ω, z)`
(countable dense set of the unit circle; `sphere z ρ = ρ • sphere 0 1 + z`). -/
lemma measurable_sphere_sup (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {ρ : ℝ} (hρ : 0 < ρ)
    {SC : Set ℂ} (hSCs : SC ⊆ sphere (0 : ℂ) 1) (hSCc : SC.Countable)
    (hSCd : sphere (0 : ℂ) 1 ⊆ closure SC) :
    Measurable fun p : Ω × ℂ => ⨆ x ∈ sphere p.2 ρ, ENNReal.ofReal (D p.1 p.2 x) := by
  have : Countable SC := hSCc.to_subtype
  have key : ∀ p : Ω × ℂ, (⨆ x ∈ sphere p.2 ρ, ENNReal.ofReal (D p.1 p.2 x)) =
      ⨆ s : SC, ENNReal.ofReal (D p.1 p.2 (((ρ : ℝ) : ℂ) * (s : ℂ) + p.2)) := by
    intro p
    have hcont : Continuous fun x : ℂ => ENNReal.ofReal (D p.1 p.2 x) :=
      ENNReal.continuous_ofReal.comp ((hDc p.1).comp (continuous_const.prodMk continuous_id))
    refine iSup_image_eq_iSup (f := fun x : ℂ => ENNReal.ofReal (D p.1 p.2 x)) hcont
      (fun s : ℂ => ((ρ : ℝ) : ℂ) * s + p.2) SC ?_ ?_
    · intro s hs
      rw [sphere_eq_affine hρ]
      exact mem_image_of_mem _ (hSCs hs)
    · rw [sphere_eq_affine hρ]
      exact affine_closure hSCd
  have hfun : (fun p : Ω × ℂ => ⨆ x ∈ sphere p.2 ρ, ENNReal.ofReal (D p.1 p.2 x)) =
      fun p => ⨆ s : SC, ENNReal.ofReal (D p.1 p.2 (((ρ : ℝ) : ℂ) * (s : ℂ) + p.2)) :=
    funext key
  rw [hfun]
  exact Measurable.iSup fun s => (measurable_D_point hDm (((ρ : ℝ) : ℂ) * (s : ℂ))).ennreal_ofReal

/-- The supremum over `rescaledSet T r z × rescaledSet T r z` of `D ω`, measurable in `(ω, z)`. -/
lemma measurable_pair_sup (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {r : ℝ} {T ST : Set ℂ}
    (hSTs : ST ⊆ T) (hSTc : ST.Countable) (hSTd : T ⊆ closure ST) :
    Measurable fun p : Ω × ℂ =>
      ⨆ x ∈ rescaledSet T r p.2, ⨆ y ∈ rescaledSet T r p.2, ENNReal.ofReal (D p.1 x y) := by
  have : Countable (ST ×ˢ ST) := (hSTc.prod hSTc).to_subtype
  have key : ∀ p : Ω × ℂ, (⨆ x ∈ rescaledSet T r p.2, ⨆ y ∈ rescaledSet T r p.2, ENNReal.ofReal (D p.1 x y)) =
      ⨆ s : ST ×ˢ ST, ENNReal.ofReal (D p.1 ((r : ℂ) * s.1.1 + p.2) ((r : ℂ) * s.1.2 + p.2)) := by
    intro p
    have hcont : Continuous fun q : ℂ × ℂ => ENNReal.ofReal (D p.1 q.1 q.2) :=
      ENNReal.continuous_ofReal.comp (hDc p.1)
    refine (iSup_prod_eq (F := fun x y => ENNReal.ofReal (D p.1 x y))).trans ?_
    refine iSup_image_eq_iSup (f := fun q : ℂ × ℂ => ENNReal.ofReal (D p.1 q.1 q.2)) hcont
      (fun s : ℂ × ℂ => ((r : ℂ) * s.1 + p.2, (r : ℂ) * s.2 + p.2)) (ST ×ˢ ST) ?_ ?_
    · rintro s ⟨hs1, hs2⟩
      exact ⟨mem_image_of_mem _ (hSTs hs1), mem_image_of_mem _ (hSTs hs2)⟩
    · exact prod_affine_closure (affine_closure hSTd) (affine_closure hSTd)
  have hfun : (fun p : Ω × ℂ => ⨆ x ∈ rescaledSet T r p.2, ⨆ y ∈ rescaledSet T r p.2,
      ENNReal.ofReal (D p.1 x y)) =
      fun p => ⨆ s : ST ×ˢ ST, ENNReal.ofReal (D p.1 ((r : ℂ) * s.1.1 + p.2) ((r : ℂ) * s.1.2 + p.2)) :=
    funext key
  rw [hfun]
  exact Measurable.iSup fun s => (measurable_D_shift hDm _ _).ennreal_ofReal

/-- The `setDist` from the rescaled `Q'` to the frontier of the rescaled `Q`, measurable in `(ω, z)`. -/
lemma measurable_setDist_frontier (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {r : ℝ} (hr : r ≠ 0) {Q Q' SQ SF : Set ℂ}
    (hSQs : SQ ⊆ Q') (hSQc : SQ.Countable) (hSQd : Q' ⊆ closure SQ)
    (hSFs : SF ⊆ frontier Q) (hSFc : SF.Countable) (hSFd : frontier Q ⊆ closure SF) :
    Measurable fun p : Ω × ℂ =>
      ENNReal.ofReal (setDist (D p.1) (rescaledSet Q' r p.2) (frontier (rescaledSet Q r p.2))) := by
  have : Countable (SQ ×ˢ SF) := (hSQc.prod hSFc).to_subtype
  have key : ∀ p : Ω × ℂ, setDist (D p.1) (rescaledSet Q' r p.2) (frontier (rescaledSet Q r p.2)) =
      ⨅ s : SQ ×ˢ SF, D p.1 ((r : ℂ) * s.1.1 + p.2) ((r : ℂ) * s.1.2 + p.2) := by
    intro p
    have hB : frontier (rescaledSet Q r p.2) = (fun x : ℂ => (r : ℂ) * x + p.2) '' frontier Q :=
      frontier_affine hr p.2
    rw [hB]
    refine setDist_eq_iInf (D p.1) (hDc p.1)
      (fun s : ℂ × ℂ => ((r : ℂ) * s.1 + p.2, (r : ℂ) * s.2 + p.2)) (SQ ×ˢ SF) ?_ ?_
    · rintro s ⟨hs1, hs2⟩
      exact ⟨mem_image_of_mem _ (hSQs hs1), mem_image_of_mem _ (hSFs hs2)⟩
    · exact prod_affine_closure (affine_closure hSQd) (affine_closure hSFd)
  have hR : Measurable fun p : Ω × ℂ =>
      ⨅ s : SQ ×ˢ SF, D p.1 ((r : ℂ) * s.1.1 + p.2) ((r : ℂ) * s.1.2 + p.2) :=
    Measurable.iInf fun s => measurable_D_shift hDm _ _
  have hfun : (fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (rescaledSet Q' r p.2)
      (frontier (rescaledSet Q r p.2)))) =
      fun p => ENNReal.ofReal (⨅ s : SQ ×ˢ SF, D p.1 ((r : ℂ) * s.1.1 + p.2) ((r : ℂ) * s.1.2 + p.2)) :=
    funext fun p => by rw [key p]
  rw [hfun]
  exact ENNReal.measurable_ofReal.comp hR

/-- The `setDist` from the centre to the sphere `sphere z ρ`, measurable in `(ω, z)`. -/
lemma measurable_setDist_sphere (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {ρ : ℝ} (hρ : 0 < ρ)
    {SC : Set ℂ} (hSCs : SC ⊆ sphere (0 : ℂ) 1) (hSCc : SC.Countable)
    (hSCd : sphere (0 : ℂ) 1 ⊆ closure SC) :
    Measurable fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) {p.2} (sphere p.2 ρ)) := by
  have : Countable SC := hSCc.to_subtype
  have key : ∀ p : Ω × ℂ, setDist (D p.1) {p.2} (sphere p.2 ρ) =
      ⨅ s : SC, D p.1 p.2 (((ρ : ℝ) : ℂ) * (s : ℂ) + p.2) := by
    intro p
    refine setDist_singleton_eq_iInf (D p.1) (hDc p.1) p.2 (fun s : ℂ => ((ρ : ℝ) : ℂ) * s + p.2) SC ?_ ?_
    · intro s hs
      rw [sphere_eq_affine hρ]
      exact mem_image_of_mem _ (hSCs hs)
    · rw [sphere_eq_affine hρ]
      exact affine_closure hSCd
  have hR : Measurable fun p : Ω × ℂ => ⨅ s : SC, D p.1 p.2 (((ρ : ℝ) : ℂ) * (s : ℂ) + p.2) :=
    Measurable.iInf fun s => measurable_D_point hDm _
  have hfun : (fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) {p.2} (sphere p.2 ρ))) =
      fun p => ENNReal.ofReal (⨅ s : SC, D p.1 p.2 (((ρ : ℝ) : ℂ) * (s : ℂ) + p.2)) :=
    funext fun p => by rw [key p]
  rw [hfun]
  exact ENNReal.measurable_ofReal.comp hR

/-- `(ω, z) ↦ κ ω (rescaledSet U r z)` is measurable for a measurable `U` and an s-finite kernel `κ`. -/
lemma measurable_kernel_rescaled {κ : Kernel Ω ℂ} [IsSFiniteKernel κ] {U : Set ℂ} (hU : MeasurableSet U)
    {r : ℝ} (hr : r ≠ 0) : Measurable fun p : Ω × ℂ => κ p.1 (rescaledSet U r p.2) := by
  have hmeas : Measurable fun q : (Ω × ℂ) × ℂ => (r : ℂ)⁻¹ * (q.2 - q.1.2) :=
    (measurable_snd.sub (measurable_snd.comp measurable_fst)).const_mul _
  have ht : MeasurableSet {q : (Ω × ℂ) × ℂ | (r : ℂ)⁻¹ * (q.2 - q.1.2) ∈ U} := hU.preimage hmeas
  let κ' : Kernel (Ω × ℂ) ℂ := κ.comap (fun p : Ω × ℂ => p.1) measurable_fst
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ') ht
  have heq : (fun p : Ω × ℂ => κ p.1 (rescaledSet U r p.2)) =
      fun a => κ' a (Prod.mk a ⁻¹' {q : (Ω × ℂ) × ℂ | (r : ℂ)⁻¹ * (q.2 - q.1.2) ∈ U}) := by
    funext a
    show κ a.1 (rescaledSet U r a.2) =
      κ a.1 (Prod.mk a ⁻¹' {q : (Ω × ℂ) × ℂ | (r : ℂ)⁻¹ * (q.2 - q.1.2) ∈ U})
    congr 1
    ext y
    exact mem_affine_image_iff hr a.2 y
  rw [heq]
  exact hm

end Joint

section Final

/-- A measurable family of continuous metrics `d : Ω → C(ℂ × ℂ, ℝ)` is jointly measurable in `(ω, x, y)`. -/
lemma measurable_uncurry_of_continuousMap {Ω : Type*} [MeasurableSpace Ω]
    {d : Ω → C(ℂ × ℂ, ℝ)} (hd : Measurable d) :
    Measurable fun q : Ω × (ℂ × ℂ) => d q.1 q.2 := by
  have hu : Measurable (Function.uncurry fun (y : ℂ × ℂ) (ω : Ω) => d ω y) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => (d ω).continuous) (fun y => (ContinuousMap.measurable_eval y).comp hd)
  exact hu.comp measurable_swap

/-- The pinch events `{(ω, z) | pinchPointEvent (κ ω) (D ω) U T Q' Q M (2⁻¹)^n z}` are measurable, for an
s-finite kernel `κ` of measures, a jointly measurable family `D` of metrics continuous in `(x, y)`, and a
measurable `U`. This is `hpin` of `CanonicalGood` (sec. 5.1). -/
theorem measurableSet_pinchSet {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (D : Ω → ℂ → ℂ → ℝ) (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) (M : ℝ) {U T Q' Q : Set ℂ}
    (hU : MeasurableSet U) (n : ℕ) :
    MeasurableSet {p : Ω × ℂ | pinchPointEvent (κ p.1) (D p.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) p.2} := by
  obtain ⟨SC, hSCs, hSCc, hSCd⟩ := exists_countable_subset_closure (sphere (0 : ℂ) 1)
  obtain ⟨ST, hSTs, hSTc, hSTd⟩ := exists_countable_subset_closure T
  obtain ⟨SQ, hSQs, hSQc, hSQd⟩ := exists_countable_subset_closure Q'
  obtain ⟨SF, hSFs, hSFc, hSFd⟩ := exists_countable_subset_closure (frontier Q)
  have hr : (2 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have h1 := measurable_sphere_sup hDm hDc (ρ := 5 * (2 : ℝ)⁻¹ ^ n) (by positivity) hSCs hSCc hSCd
  have h2 := measurable_pair_sup hDm hDc (r := (2 : ℝ)⁻¹ ^ n) hSTs hSTc hSTd
  have h3 := measurable_setDist_frontier hDm hDc hr hSQs hSQc hSQd hSFs hSFc hSFd
  have h4 := measurable_setDist_sphere hDm hDc (ρ := 5 * (2 : ℝ)⁻¹ ^ n) (by positivity) hSCs hSCc hSCd
  have h5 : Measurable fun p : Ω × ℂ =>
      ENNReal.ofReal M * annulusGreenPotentialSup (κ p.1) p.2 (3 * (2 : ℝ)⁻¹ ^ n) (6 * (2 : ℝ)⁻¹ ^ n) :=
    (measurable_kernel_annulusGreenPotentialSup κ _ _).const_mul _
  have h6 := measurable_kernel_rescaled (κ := κ) hU hr
  exact (measurableSet_lt h1 h3).inter ((measurableSet_lt h2 h4).inter (measurableSet_lt h5 h6))

/-- For the strengthened canonical decoders (a measurable `d : CanonSpace → C(ℂ × ℂ, ℝ)` with kernel `κ`), the
pinch events are measurable in `(L, z)`: this discharges `hpin` of `CanonicalGood` for those decoders. -/
theorem measurableSet_pinchSet_decoder (κ : Kernel CanonSpace ℂ) [IsSFiniteKernel κ]
    (d : CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d) (M : ℝ) {U T Q' Q : Set ℂ}
    (hU : MeasurableSet U) (n : ℕ) :
    MeasurableSet (CanonicalGood.pinchSet κ (fun L x y => d L (x, y)) M U T Q' Q n) :=
  measurableSet_pinchSet κ (fun L x y => d L (x, y)) (measurable_uncurry_of_continuousMap hd)
    (fun ω => (d ω).continuous) M hU n

universe u

/-- `CanonicalPinchConullStmt` for the strengthened canonical decoders, from the probabilistic clause `hP`
(eq. (35), the Campbell argument; still a named input). -/
theorem canonicalPinchConull_of_decoder {α₀ M δ : ℝ} {U T Q' Q : Set ℂ} (κ : Kernel CanonSpace ℂ)
    [IsSFiniteKernel κ] (d : CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d) (hU : MeasurableSet U)
    (hP : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P,
        alphaCanon α₀ hC ω ∈ CanonicalGood.goodSet κ (fun L x y => d L (x, y)) M δ U T Q' Q) :
    CanonicalPinchConullStmt.{u} α₀ M δ U T Q' Q (fun L => κ L) (fun L x y => d L (x, y)) :=
  CanonicalGood.canonicalPinchConull_of_kernel κ (fun L x y => d L (x, y))
    (fun n => measurableSet_pinchSet_decoder κ d hd M hU n) hP

end Final

end HarmonicBalls.PinchMeasurable
