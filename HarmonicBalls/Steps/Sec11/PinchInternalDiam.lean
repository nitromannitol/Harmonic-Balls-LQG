import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.InternalPinchScales

/-! # Internal diameters at closure points

These estimates support the diameter decomposition in the proof of
Lemma 11.12, including junctions lying on the boundaries of the pieces.
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

/-- The internal distance of closure points is bounded by the internal
diameter, provided the local neighborhoods lie in the target domain. -/
theorem IsEuclideanLengthMetric.internalMetric_le_internalDiam_of_mem_closure
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V A : Set ℂ} (hV : IsOpen V)
    (hcl : closure A ⊆ V) {δ : ℝ} (hsub : thickening δ A ⊆ V)
    {x y : ℂ} (hx : x ∈ closure A) (hy : y ∈ closure A) :
    internalMetric D V x y ≤ internalDiam D δ A := by
  have hpair : (x, y) ∈ closure (A ×ˢ A) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  let : NeBot (𝓝[A ×ˢ A] (x, y)) := mem_closure_iff_nhdsWithin_neBot.mp hpair
  apply le_of_tendsto (x := 𝓝[A ×ˢ A] (x, y)) ((hD.continuousAt_internalMetric_pair hnonneg hV
    (hcl hx) (hcl hy)).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (internalMetric_anti D hsub p.1 p.2).trans
    (le_iSup_of_le p.1 (le_iSup_of_le hp.1
      (le_iSup_of_le p.2 (le_iSup_of_le hp.2 le_rfl))))

/-- Two pieces whose closures meet are joined inside the target domain at a
cost bounded by the sum of their internal diameters. -/
theorem IsEuclideanLengthMetric.internalMetric_le_internalDiam_add
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V A B : Set ℂ} (hV : IsOpen V)
    (hAcl : closure A ⊆ V) (hBcl : closure B ⊆ V) {δ : ℝ}
    (hAsub : thickening δ A ⊆ V) (hBsub : thickening δ B ⊆ V)
    {x y : ℂ} (hx : x ∈ closure A) (hy : y ∈ closure B)
    (hmeet : (closure A ∩ closure B).Nonempty) :
    internalMetric D V x y ≤ internalDiam D δ A + internalDiam D δ B := by
  obtain ⟨z, hzA, hzB⟩ := hmeet
  exact (hD.internalMetric_triangle V x z y).trans
    (add_le_add (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hAcl hAsub hx hzA)
      (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hBcl hBsub hzB hy))

/-- Three pieces joined in a chain have internal distance bounded by the sum
of their internal diameters, including for boundary junctions. -/
theorem IsEuclideanLengthMetric.internalMetric_le_internalDiam_add_three
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V A B C : Set ℂ} (hV : IsOpen V)
    (hAcl : closure A ⊆ V) (hBcl : closure B ⊆ V) (hCcl : closure C ⊆ V)
    {δ : ℝ} (hAsub : thickening δ A ⊆ V) (hBsub : thickening δ B ⊆ V)
    (hCsub : thickening δ C ⊆ V) {x y : ℂ}
    (hx : x ∈ closure A) (hy : y ∈ closure C)
    (hAB : (closure A ∩ closure B).Nonempty)
    (hBC : (closure B ∩ closure C).Nonempty) :
    internalMetric D V x y ≤ internalDiam D δ A + internalDiam D δ B + internalDiam D δ C := by
  obtain ⟨u, huA, huB⟩ := hAB
  obtain ⟨v, hvB, hvC⟩ := hBC
  calc
    internalMetric D V x y ≤ internalMetric D V x u + internalMetric D V u y :=
      hD.internalMetric_triangle V x u y
    _ ≤ internalMetric D V x u + (internalMetric D V u v + internalMetric D V v y) :=
      add_le_add le_rfl (hD.internalMetric_triangle V u v y)
    _ ≤ internalDiam D δ A + (internalDiam D δ B + internalDiam D δ C) :=
      add_le_add (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hAcl hAsub hx huA)
        (add_le_add
          (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hBcl hBsub huB hvB)
          (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hCcl hCsub hvC hy))
    _ = _ := (add_assoc _ _ _).symm

/-- A set covered by three pieces joined through their closures has internal
diameter at most the sum of the three local internal diameters. -/
theorem IsEuclideanLengthMetric.iSup_internalMetric_le_internalDiam_add_three
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V T A B C : Set ℂ} (hV : IsOpen V)
    (hAcl : closure A ⊆ V) (hBcl : closure B ⊆ V) (hCcl : closure C ⊆ V)
    {δ : ℝ} (hAsub : thickening δ A ⊆ V) (hBsub : thickening δ B ⊆ V)
    (hCsub : thickening δ C ⊆ V) (hcover : T ⊆ closure A ∪ closure B ∪ closure C)
    (hAB : (closure A ∩ closure B).Nonempty)
    (hBC : (closure B ∩ closure C).Nonempty) :
    (⨆ x ∈ T, ⨆ y ∈ T, internalMetric D V x y) ≤
      internalDiam D δ A + internalDiam D δ B + internalDiam D δ C := by
  let a := internalDiam D δ A
  let b := internalDiam D δ B
  let c := internalDiam D δ C
  have ha : a ≤ a + b + c := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hb : b ≤ a + b + c := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hc : c ≤ a + b + c := le_add_left le_rfl
  have hab : a + b ≤ a + b + c := le_add_right le_rfl
  have hbc : b + c ≤ a + b + c := by
    calc
      b + c ≤ (b + c) + a := le_add_right le_rfl
      _ = _ := by ac_rfl
  have hAA x y (hx : x ∈ closure A) (hy : y ∈ closure A) :
      internalMetric D V x y ≤ a + b + c :=
    (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hAcl hAsub hx hy).trans ha
  have hBB x y (hx : x ∈ closure B) (hy : y ∈ closure B) :
      internalMetric D V x y ≤ a + b + c :=
    (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hBcl hBsub hx hy).trans hb
  have hCC x y (hx : x ∈ closure C) (hy : y ∈ closure C) :
      internalMetric D V x y ≤ a + b + c :=
    (hD.internalMetric_le_internalDiam_of_mem_closure hnonneg hV hCcl hCsub hx hy).trans hc
  have hAB' x y (hx : x ∈ closure A) (hy : y ∈ closure B) :
      internalMetric D V x y ≤ a + b + c :=
    (hD.internalMetric_le_internalDiam_add hnonneg hV hAcl hBcl hAsub hBsub hx hy hAB).trans hab
  have hBC' x y (hx : x ∈ closure B) (hy : y ∈ closure C) :
      internalMetric D V x y ≤ a + b + c :=
    (hD.internalMetric_le_internalDiam_add hnonneg hV hBcl hCcl hBsub hCsub hx hy hBC).trans hbc
  have hAC' x y (hx : x ∈ closure A) (hy : y ∈ closure C) :
      internalMetric D V x y ≤ a + b + c :=
    hD.internalMetric_le_internalDiam_add_three hnonneg hV hAcl hBcl hCcl hAsub hBsub hCsub
      hx hy hAB hBC
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  rcases hcover hx with (hx | hx) | hx <;> rcases hcover hy with (hy | hy) | hy
  · exact hAA x y hx hy
  · exact hAB' x y hx hy
  · exact hAC' x y hx hy
  · rw [hD.internalMetric_symm V x y]; exact hAB' y x hy hx
  · exact hBB x y hx hy
  · exact hBC' x y hx hy
  · rw [hD.internalMetric_symm V x y]; exact hAC' y x hy hx
  · rw [hD.internalMetric_symm V x y]; exact hBC' y x hy hx
  · exact hCC x y hx hy

open Classical in
/-- The three auxiliary diameter inequalities imply the second strengthened
pinch inequality, once the radial crossing bound and the stated geometric
containment and closure-intersection properties have been established. -/
theorem pinchSecondInternalBound_of_auxiliary_events
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (μ : MeasureTheory.Measure ℂ)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ)
    (hclA : closure (T \ thickening (3 * δ) W) ⊆ ball 0 6)
    (hclB : closure (thickening (3 * δ) W \ V) ⊆ ball 0 6)
    (hclC : closure V ⊆ ball 0 6)
    (hsubA : thickening δ (T \ thickening (3 * δ) W) ⊆ ball 0 6)
    (hsubB : thickening δ (thickening (3 * δ) W \ V) ⊆ ball 0 6)
    (hsubC : thickening δ V ⊆ ball 0 6)
    (hAB : (closure (T \ thickening (3 * δ) W) ∩
      closure (thickening (3 * δ) W \ V)).Nonempty)
    (hBC : (closure (thickening (3 * δ) W \ V) ∩ closure V).Nonempty)
    (hcross : ENNReal.ofReal (setDist D {0} (sphere 0 δ)) +
        ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) +
        ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) ≤
      ENNReal.ofReal (setDist D {0} (sphere 0 5))) :
    (⨆ x ∈ T, ⨆ y ∈ T, internalMetric D (ball 0 6) x y) <
      ENNReal.ofReal (setDist D {0} (sphere 0 5)) := by
  have hcover : T ⊆ closure (T \ thickening (3 * δ) W) ∪
      closure (thickening (3 * δ) W \ V) ∪ closure V := by
    intro x hx
    by_cases hw : x ∈ thickening (3 * δ) W
    · by_cases hv : x ∈ V
      · exact Or.inr (subset_closure hv)
      · exact Or.inl (Or.inr (subset_closure ⟨hw, hv⟩))
    · exact Or.inl (Or.inl (subset_closure ⟨hx, hw⟩))
  have hdiam := hD.iSup_internalMetric_le_internalDiam_add_three hnonneg isOpen_ball
    hclA hclB hclC hsubA hsubB hsubC hcover hAB hBC
  exact hdiam.trans_lt ((ENNReal.add_lt_add (ENNReal.add_lt_add hfirst.2 hthird)
    hsecond.1).trans_le hcross)

end HarmonicBalls
