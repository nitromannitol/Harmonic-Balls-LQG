import HarmonicBalls.Proofs.GFF.InsertedLocalJointCoordinates
import HarmonicBalls.FirstPass.S11ay
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds

/-! # Actual local pinch event observations -/

open HarmonicBalls MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The normalized coordinate event agrees almost surely with the actual local
pinch event together with its two finiteness conditions. -/
theorem IsWholePlaneGFF.ae_pinchCoordinateEvent_iff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ R : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hR : 6 < R)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ)
    (hd : ∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
      (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
      (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2))
    (b : Ω → ℝ) (hb : ∀ ω, 0 < b ω) (M : ℝ) :
    ∀ᵐ ω ∂P,
      ((normalizedRestriction (μ ω) (ball 0 R),
        fun n => ENNReal.ofReal (b ω) * internalMetric (D ω) (domain n)
          (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
        S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M ∧
          annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤ ∧ μ ω U ≠ ⊤) := by
  have hfull := lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ h hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hmass := (ae_referenceBall_pos_finite P μ hfull hloc).mono fun _ hω =>
    hω R (by linarith)
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ2 hα hDfield
  filter_upwards [hmass, hmetric] with ω hm hmet
  exact pinchCoordinateEvent_iff hgeo hR I domain pair hd (μ ω) hm.1 hm.2
    (D ω) hmet hmet.nonneg_apply (b ω) (hb ω) M

/-- The normalized observation identifies the actual local triple event almost surely. -/
theorem IsWholePlaneGFF.ae_pinchCoordinateEvent_iff_localRule
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ R : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hR : 6 < R)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ)
    (hd : ∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
      (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
      (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2))
    (b : Ω → ℝ) (hb : ∀ ω, 0 < b ω) (M : ℝ) :
    ∀ᵐ ω ∂P,
      ((normalizedRestriction (μ ω) (ball 0 R),
        fun n => ENNReal.ofReal (b ω) * internalMetric (D ω) (domain n)
          (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
        S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
  have hU : Bornology.IsBounded U := by
    obtain ⟨c, ρU, ρV, ρW, hU, -, -⟩ := hgeo.concentric
    rw [hU]
    exact Metric.isBounded_ball
  have hfin := (S11ay.ae_annulusGreenPotentialSup_ne_top_alpha h hγ hγ2 hα hμ
    lqgVolumeGrowthAllScalesStmt_holds).and (S11ay.ae_measure_ne_top_of_isBounded hμ U hU)
  filter_upwards [h.ae_pinchCoordinateEvent_iff hμ hγ hγ2 hα hDfield haxioms
    hgeo hR I domain pair hd b hb M, hfin] with ω he hf
  exact he.trans (and_iff_left ⟨hf.1, hf.2⟩)

/-- There are admissible metric coordinates whose normalized observation
identifies the actual local triple event. -/
theorem IsWholePlaneGFF.exists_pinchCoordinateEvent_iff_localRule
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ R : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hR : 6 < R)
    (I : S11am.PinchCountSets V W T Q' Q δ) :
    ∃ (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ),
      (∀ n, IsOpen (domain n) ∧ ((0 : ℂ) ∈ domain n → IsConnected (domain n)) ∧
        (pair n).1 ∈ domain n ∧ (pair n).2 ∈ domain n) ∧
      ∀ (b : Ω → ℝ), (∀ ω, 0 < b ω) → ∀ M : ℝ,
        ∀ᵐ ω ∂P,
          ((normalizedRestriction (μ ω) (ball 0 R),
            fun n => ENNReal.ofReal (b ω) * internalMetric (D ω) (domain n)
              (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
            S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
  obtain ⟨domain, pair, hv, _, hd⟩ := exists_pinch_countable_metric_coordinates hgeo I
  exact ⟨domain, pair, hv, fun b hb M =>
    h.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms
      hgeo hR I domain pair hd b hb M⟩

/-- The joint coordinate law and the actual local event use the same coordinates. -/
theorem IsWholePlaneGFF.exists_joint_shift_law_and_pinch_event
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1) (hξ : 0 ≤ ξ) :
    ∃ (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ) (R : ℝ),
      R ∈ Ioo (6 : ℝ) 7 ∧
      (∀ n, IsOpen (domain n) ∧ ((0 : ℂ) ∈ domain n → IsConnected (domain n)) ∧
        (pair n).1 ∈ domain n ∧ (pair n).2 ∈ domain n) ∧
      (∀ O x y, Measurable (coordinateReadout domain pair (O, (x, y)))) ∧
      (∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
        (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
        (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2)) ∧
      (∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (domain n) (pair n).1 (pair n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 7) ω,
           normalizedRestriction (μ ω) (ball 0 R), fun n =>
             ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
               internalMetric (D ω) (domain n) (pair n).1 (pair n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 7) ω,
           normalizedRestriction (μ ω) (ball 0 R), fun n =>
             ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
               internalMetric (D ω) (domain n) (pair n).1 (pair n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (domain n) (pair n).1 (pair n).2))) ∧
      ∀ (b : Ω → ℝ), (∀ ω, 0 < b ω) → ∀ M : ℝ,
        ∀ᵐ ω ∂P,
          ((normalizedRestriction (μ ω) (ball 0 R),
            fun n => ENNReal.ofReal (b ω) * internalMetric (D ω) (domain n)
              (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
            S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
  obtain ⟨domain, pair, R, hR, hv, hm, hd, hlaw⟩ :=
    h.exists_joint_smooth_shift_law_for_pinch_coordinates hμ hγ hγ2 hα hDfield haxioms
      hgeo I ψ hψ hψint hξ
  exact ⟨domain, pair, R, hR, hv, hm, hd, hlaw, fun b hb M =>
    h.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms
      hgeo hR.1 I domain pair hd b hb M⟩

end HarmonicBalls
