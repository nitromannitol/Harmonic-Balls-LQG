import HarmonicBalls.Proofs.Sec5.AnalyticSetNullMeasurable

/-! # Null measurability of uniform containment -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Each all-centre unit-containment event is null measurable under the law
of the LQG measure. The proof uses the analytic potential representation and
Lusin's theorem, rather than requiring a common buffer for all centres. -/
theorem IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentEvent_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (m : ℕ) : NullMeasurableSet (unitClusterContainmentEvent m) (Measure.map μ P) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ zero_lt_one
  obtain ⟨Q, hQ, hS⟩ := exists_analyticSet_unitClusterContainmentEvent_compl
  obtain ⟨S, hSa, hSeq⟩ := hS m
  have hnull : NullMeasurableSet (Q ⁻¹' S) (Measure.map μ P) :=
    (AnalyticSet.nullMeasurableSet_of_finite (Measure.map Q (Measure.map μ P)) hSa).preimage
      (hQ.quasiMeasurePreserving _)
  have heq : Q ⁻¹' S =ᵐ[Measure.map μ P] (unitClusterContainmentEvent m)ᶜ := by
    filter_upwards [hGae] with ν hν
    exact propext (hSeq ν (hGgood ν hν).1 (hGgood ν hν).2)
  simpa only [compl_compl] using (hnull.congr heq).compl

/-- The all-centre unit-containment event is also null measurable on the
original probability space, including when the measure map is only almost
surely measurable. -/
theorem IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentEvent
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (m : ℕ) : NullMeasurableSet (μ ⁻¹' unitClusterContainmentEvent m) P := by
  have hm := hGFF.aemeasurable_lqgMeasure hμ
  have hn := hGFF.nullMeasurableSet_unitClusterContainmentEvent_measureLaw hI2 hγ hγ2 hα hμ m
  have hmap : Measure.map μ P = Measure.map (hm.mk μ) P := Measure.map_congr hm.ae_eq_mk
  rw [hmap] at hn
  apply (hn.preimage (hm.measurable_mk.quasiMeasurePreserving P)).congr
  filter_upwards [hm.ae_eq_mk] with ω hω
  simp only [mem_preimage, ← hω]

/-- The cofinal interval step follows from the numbered input results and the
two explicit field-scaling inputs, without a containment-measurability premise. -/
theorem cofinalRegularizedClusterIntervals_of_analytic_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h54 : RegularizedClusterHarmonicBallsStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_unitContainmentMeasurable h32 h53 h54 h71 hAff hCC
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ m
  exact hGFF.nullMeasurableSet_unitClusterContainmentEvent_measureLaw hI2 hγ hγ2 hα hμ m

end HarmonicBalls
