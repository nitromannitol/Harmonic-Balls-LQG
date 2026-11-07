import HarmonicBalls.Proofs.GFF.LogInsertionCircleAverages

/-! # Fixed circles under random logarithmic insertion

The distribution-valued GFF and its circle mollifiers are due to Leonardo Bonanno.
The exceptional events below depend on the fixed circle, not on the insertion. -/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- At a fixed circle, one event gives both the actual mollifier limit and the
chosen circle average for every insertion root and coefficient. -/
theorem IsWholePlaneGFF.ae_mollAvg_circleAvg_all_logInsertions
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (a : ℝ),
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg
        (reconstructedGFF hC ω + logInsertionDistribution z a) n w r) atTop
        (𝓝 (hcirc ω r w + a * Real.log (max r ‖w - z‖))) ∧
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution z a) r w =
        hcirc ω r w + a * Real.log (max r ‖w - z‖) := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg
    hh.reconstructedGFF_normalized.1 w hr, hh.ae_circleAvg_reconstructedGFF hr w] with ω ⟨b, hb⟩ hc
  rw [LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hb] at hc
  intro z a
  have hs := hb.add (tendsto_mollAvg_logInsertion z w a hr)
  have ht : Tendsto (fun n => LQGMetric.CircleAvg.mollAvg
      (reconstructedGFF hC ω + logInsertionDistribution z a) n w r) atTop
      (𝓝 (hcirc ω r w + a * Real.log (max r ‖w - z‖))) := by
    rw [hc]
    convert hs using 1
    funext n
    simp only [LQGMetric.CircleAvg.mollAvg_eq, add_apply]
  exact ⟨ht, LQGMetric.CircleAvg.circleAvg_eq_of_tendsto ht⟩

/-- The centered circle average formula holds simultaneously for all insertions. -/
theorem IsWholePlaneGFF.ae_centered_circleAvg_all_logInsertions
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (a : ℝ),
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution z a) r w -
        LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution z a) 1 0 =
      hcirc ω r w + a * Real.log (max r ‖w - z‖) - a * Real.log (max 1 ‖z‖) := by
  filter_upwards [hh.ae_mollAvg_circleAvg_all_logInsertions w hr,
    hh.ae_mollAvg_circleAvg_all_logInsertions 0 one_pos,
    hh.ae_circleAvg_reconstructedGFF one_pos 0,
    hh.ae_circleAvg_one_zero_reconstructedGFF] with ω h h1 hraw hzero
  rw [hzero] at hraw
  intro z a
  rw [(h z a).2, (h1 z a).2, hraw]
  simp only [zero_add, zero_sub, norm_neg]

/-- The unit-circle value holds on one event for every insertion. -/
theorem IsWholePlaneGFF.ae_unit_circleAvg_all_logInsertions
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (a : ℝ),
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution z a) 1 0 =
        a * Real.log (max 1 ‖z‖) := by
  filter_upwards [hh.ae_mollAvg_circleAvg_all_logInsertions 0 one_pos,
    hh.ae_circleAvg_reconstructedGFF one_pos 0,
    hh.ae_circleAvg_one_zero_reconstructedGFF] with ω h hraw hzero
  rw [hzero] at hraw
  intro z a
  simpa only [hraw, zero_add, zero_sub, norm_neg] using (h z a).2

/-- Random roots and coefficients may depend arbitrarily on the field. -/
theorem IsWholePlaneGFF.ae_mollAvg_circleAvg_random_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (Z : Ω → ℂ) (A : Ω → ℝ)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, Tendsto (fun n => LQGMetric.CircleAvg.mollAvg
      (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) n w r) atTop
      (𝓝 (hcirc ω r w + A ω * Real.log (max r ‖w - Z ω‖))) ∧
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) r w =
        hcirc ω r w + A ω * Real.log (max r ‖w - Z ω‖) := by
  filter_upwards [hh.ae_mollAvg_circleAvg_all_logInsertions w hr] with ω h
  exact h (Z ω) (A ω)

/-- The centered formula also permits dependent random insertion parameters. -/
theorem IsWholePlaneGFF.ae_centered_circleAvg_random_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (Z : Ω → ℂ) (A : Ω → ℝ)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) r w -
        LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) 1 0 =
      hcirc ω r w + A ω * Real.log (max r ‖w - Z ω‖) -
        A ω * Real.log (max 1 ‖Z ω‖) := by
  filter_upwards [hh.ae_centered_circleAvg_all_logInsertions w hr] with ω h
  exact h (Z ω) (A ω)

/-- The unit-circle formula holds for arbitrary dependent random parameters. -/
theorem IsWholePlaneGFF.ae_unit_circleAvg_random_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (Z : Ω → ℂ) (A : Ω → ℝ) :
    ∀ᵐ ω ∂P,
      LQGMetric.circleAvg (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) 1 0 =
        A ω * Real.log (max 1 ‖Z ω‖) := by
  filter_upwards [hh.ae_unit_circleAvg_all_logInsertions] with ω h
  exact h (Z ω) (A ω)

/-- The inserted distribution is measurable for measurable, possibly dependent parameters. -/
theorem IsWholePlaneGFF.measurable_reconstructedGFF_add_random_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {Z : Ω → ℂ} {A : Ω → ℝ}
    (hZ : Measurable Z) (hA : Measurable A) :
    Measurable (fun ω => reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) := by
  apply LQGMetric.measurable_distOn_iff.mpr
  intro φ
  change Measurable (fun ω => reconstructedGFF hC ω φ + logInsertionDistribution (Z ω) (A ω) φ)
  exact ((LQGMetric.measurable_distOn_apply φ).comp hh.measurable_reconstructedGFF).add
    ((LQGMetric.measurable_distOn_apply φ).comp
      (measurable_logInsertionDistribution.comp (hZ.prodMk hA)))

/-- The explicit fixed-circle expression is measurable. -/
theorem IsWholePlaneGFF.measurable_random_logInsertion_circle_expression
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {Z : Ω → ℂ} {A : Ω → ℝ}
    (hZ : Measurable Z) (hA : Measurable A) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun ω => hcirc ω r w + A ω * Real.log (max r ‖w - Z ω‖)) :=
  (hh.measurable_circle r w hr).add (hA.mul (Real.measurable_log.comp
    (measurable_const.max ((measurable_const.sub hZ).norm))))

/-- The circle average of the measurable inserted distribution is measurable. -/
theorem IsWholePlaneGFF.measurable_random_logInsertion_circleAvg
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {Z : Ω → ℂ} {A : Ω → ℝ}
    (hZ : Measurable Z) (hA : Measurable A) (w : ℂ) (r : ℝ) :
    Measurable (fun ω => LQGMetric.circleAvg
      (reconstructedGFF hC ω + logInsertionDistribution (Z ω) (A ω)) r w) :=
  (LQGMetric.measurable_circleAvg_left r w).comp
    (hh.measurable_reconstructedGFF_add_random_logInsertion hZ hA)

/-- The explicit centered expression is measurable. -/
theorem IsWholePlaneGFF.measurable_centered_random_logInsertion_circle_expression
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {Z : Ω → ℂ} {A : Ω → ℝ}
    (hZ : Measurable Z) (hA : Measurable A) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun ω => hcirc ω r w + A ω * Real.log (max r ‖w - Z ω‖) -
      A ω * Real.log (max 1 ‖Z ω‖)) :=
  (hh.measurable_random_logInsertion_circle_expression hZ hA w hr).sub
    (hA.mul (Real.measurable_log.comp (measurable_const.max hZ.norm)))

#print axioms IsWholePlaneGFF.ae_mollAvg_circleAvg_all_logInsertions
#print axioms IsWholePlaneGFF.ae_centered_circleAvg_all_logInsertions
#print axioms IsWholePlaneGFF.ae_unit_circleAvg_all_logInsertions
#print axioms IsWholePlaneGFF.ae_mollAvg_circleAvg_random_logInsertion
#print axioms IsWholePlaneGFF.ae_centered_circleAvg_random_logInsertion
#print axioms IsWholePlaneGFF.ae_unit_circleAvg_random_logInsertion
#print axioms IsWholePlaneGFF.measurable_random_logInsertion_circleAvg
#print axioms IsWholePlaneGFF.measurable_centered_random_logInsertion_circle_expression
#print axioms IsWholePlaneGFF.measurable_reconstructedGFF_add_random_logInsertion
#print axioms IsWholePlaneGFF.measurable_random_logInsertion_circle_expression
end HarmonicBalls
