import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness

/-! # Gluing small tile diameters through a connected core -/

namespace HarmonicBalls
open MeasureTheory Set Metric
open scoped ENNReal

/-- If every point of a set can reach a core at cost at most `a`, and the
    core has internal diameter at most `b`, its internal diameter is bounded
    by the sum of the two entrance costs and the core cost. -/
theorem IsEuclideanLengthMetric.iSup_internalMetric_le_core_gluing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O K C : Set ℂ} {a b : ℝ≥0∞}
    (hnear : ∀ x ∈ K, ∃ u ∈ C, internalMetric D O x u ≤ a)
    (hcore : ∀ u ∈ C, ∀ v ∈ C, internalMetric D O u v ≤ b) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D O x y) ≤ a + b + a := by
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨u, hu, hxu⟩ := hnear x hx
  obtain ⟨v, hv, hyv⟩ := hnear y hy
  calc
    internalMetric D O x y ≤ internalMetric D O x u + internalMetric D O u y :=
      hD.internalMetric_triangle O x u y
    _ ≤ internalMetric D O x u + (internalMetric D O u v + internalMetric D O v y) :=
      add_le_add le_rfl (hD.internalMetric_triangle O u v y)
    _ ≤ a + (b + a) := add_le_add hxu (add_le_add (hcore u hu v hv) (by
      rw [hD.internalMetric_symm O v y]
      exact hyv))
    _ = a + b + a := (add_assoc _ _ _).symm

/-- The core-gluing bound supplies the strict diameter estimate whenever the
    combined entrance and core budgets are strictly below the target. -/
theorem IsEuclideanLengthMetric.iSup_internalMetric_lt_of_core_gluing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O K C : Set ℂ} {a b ε : ℝ≥0∞}
    (hnear : ∀ x ∈ K, ∃ u ∈ C, internalMetric D O x u ≤ a)
    (hcore : ∀ u ∈ C, ∀ v ∈ C, internalMetric D O u v ≤ b)
    (hbudget : a + b + a < ε) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D O x y) < ε :=
  (hD.iSup_internalMetric_le_core_gluing hnear hcore).trans_lt hbudget

/-- The same gluing argument controls the buffered diameter used in the
    second pinch event when the gluing domain lies in the buffer. -/
theorem IsEuclideanLengthMetric.internalDiam_lt_of_core_gluing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O K C : Set ℂ} {δ : ℝ} {a b ε : ℝ≥0∞}
    (hO : O ⊆ thickening δ K)
    (hnear : ∀ x ∈ K, ∃ u ∈ C, internalMetric D O x u ≤ a)
    (hcore : ∀ u ∈ C, ∀ v ∈ C, internalMetric D O u v ≤ b)
    (hbudget : a + b + a < ε) : internalDiam D δ K < ε := by
  apply lt_of_le_of_lt _ (hD.iSup_internalMetric_lt_of_core_gluing hnear hcore hbudget)
  unfold internalDiam
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact (internalMetric_anti D hO x y).trans
    (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl))))

/-- A cover by a core and attached pieces supplies the entrance bounds used
    in the core-gluing estimate. Each piece may use its own smaller domain. -/
theorem IsEuclideanLengthMetric.internalDiam_lt_of_attached_pieces
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {ι : Type*}
    {O K C : Set ℂ} {H J : ι → Set ℂ} {δ : ℝ} {a b ε : ℝ≥0∞}
    (hopen : IsOpen O) (hC : C ⊆ O) (hO : O ⊆ thickening δ K)
    (hcover : ∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i)
    (hattach : ∀ i, (H i ∩ C).Nonempty)
    (hJ : ∀ i, J i ⊆ O)
    (hsmall : ∀ i, ∀ x ∈ H i, ∀ y ∈ H i, internalMetric D (J i) x y ≤ a)
    (hcore : ∀ u ∈ C, ∀ v ∈ C, internalMetric D O u v ≤ b)
    (hbudget : a + b + a < ε) : internalDiam D δ K < ε := by
  apply hD.internalDiam_lt_of_core_gluing hO _ hcore hbudget
  intro x hx
  rcases hcover x hx with hc | ⟨i, hi⟩
  · refine ⟨x, hc, ?_⟩
    rw [hD.internalMetric_self_of_mem_open hnonneg hopen (hC hc)]
    exact zero_le
  · obtain ⟨u, hu, huc⟩ := hattach i
    exact ⟨u, huc, (internalMetric_anti D (hJ i) x u).trans (hsmall i x hi u hu)⟩

#print axioms IsEuclideanLengthMetric.iSup_internalMetric_le_core_gluing
#print axioms IsEuclideanLengthMetric.iSup_internalMetric_lt_of_core_gluing
#print axioms IsEuclideanLengthMetric.internalDiam_lt_of_core_gluing
#print axioms IsEuclideanLengthMetric.internalDiam_lt_of_attached_pieces
end HarmonicBalls
