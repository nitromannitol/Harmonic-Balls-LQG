import HarmonicBalls.Proofs.GFF.InsertedLocalJointCoordinates
import HarmonicBalls.Proofs.Sec11.CorrectedLocalThirdPositive
import HarmonicBalls.FirstPass.S11ay
import HarmonicBalls.FirstPass.S11az
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma
import HarmonicBalls.FirstPass.S11p.FiniteWeighted
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuL8
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos

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

/-- For a fixed smooth compact shift, the coordinate event identifies the
local pinch rule of the Weyl-shifted measure and metric almost surely. -/
theorem IsWholePlaneGFF.ae_shifted_pinchCoordinateEvent_iff_localRule
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc) (hξ : 0 ≤ ξ)
    {U V W T Q' Q : Set ℂ} {δ R : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hR : 6 < R)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ)
    (hd : ∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
      (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
      (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2))
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (b : Ω → ℝ) (hb : ∀ ω, 0 < b ω) (M : ℝ) :
    ∀ᵐ ω ∂P,
      let ν := (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))
      let d := fun x y => (weylScaling (D ω) ξ g x y).toReal
      ((normalizedRestriction ν (ball 0 R),
        fun n => ENNReal.ofReal (b ω) * internalMetric d (domain n)
          (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
        S11m.LocalRule.pinchLocalRule ν d W T Q' Q U V δ M) := by
  obtain ⟨K, hK⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2.1
  have hbound : ∀ z ∈ (univ : Set ℂ), |g z| ≤ K := by
    intro z _
    simpa only [Real.norm_eq_abs] using hK z
  have hfull := lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ h hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hmass := (ae_referenceBall_pos_finite P μ hfull hloc).mono fun _ hω =>
    hω R (by linarith)
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ2 hα hDfield
  have hU : Bornology.IsBounded U := by
    obtain ⟨c, ρU, ρV, ρW, hU, -, -⟩ := hgeo.concentric
    rw [hU]
    exact Metric.isBounded_ball
  have hfin := (S11ay.ae_annulusGreenPotentialSup_ne_top_alpha h hγ hγ2 hα hμ
    lqgVolumeGrowthAllScalesStmt_holds).and (S11ay.ae_measure_ne_top_of_isBounded hμ U hU)
  filter_upwards [hmass, hmetric, hfin] with ω hm hmet hf
  have hball := LQGMetric.DG.withDensity_exp_bounds (μ₁ := μ ω) (K := univ) hγ.le
    (by simp) hbound (B := ball 0 R) measurableSet_ball
  have hu := LQGMetric.DG.withDensity_exp_bounds (μ₁ := μ ω) (K := univ) hγ.le
    (by simp) hbound (B := U) hgeo.isOpen_U.measurableSet
  have hpos : (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))) (ball 0 R) ≠ 0 := by
    have : 0 < ENNReal.ofReal (Real.exp (-(γ * K))) * μ ω (ball 0 R) := by
      exact pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hm.1)
    exact (lt_of_lt_of_le this hball.1).ne'
  have htop : (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))) (ball 0 R) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.2) hball.2
  have hutop : (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))) U ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2) hu.2
  have hgreen : annulusGreenPotentialSup
      ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) 0 3 6 ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.1)
    apply annulusGreenPotentialSup_withDensity_le _ _
      ((Real.continuous_exp.comp (continuous_const.mul hg.1.continuous)).measurable.ennreal_ofReal)
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound z (mem_univ _))) hγ.le
  have hshift := hmet.weylScaling_compact_isLengthMetric hξ g hg.1.continuous hg.2.1
  exact (pinchCoordinateEvent_iff hgeo hR I domain pair hd _ hpos htop _ hshift
    hshift.nonneg_apply (b ω) (hb ω) M).trans (and_iff_left ⟨hgreen, hutop⟩)


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
      (∀ (b : Ω → ℝ), (∀ ω, 0 < b ω) → ∀ M : ℝ,
        ∀ᵐ ω ∂P,
          ((normalizedRestriction (μ ω) (ball 0 R),
            fun n => ENNReal.ofReal (b ω) * internalMetric (D ω) (domain n)
              (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
            S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M)) ∧
      ∀ (g : ℂ → ℝ), IsTestFunction univ g → ∀ (b : Ω → ℝ), (∀ ω, 0 < b ω) → ∀ M : ℝ,
        ∀ᵐ ω ∂P,
          let ν := (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))
          let d := fun x y => (weylScaling (D ω) ξ g x y).toReal
          ((normalizedRestriction ν (ball 0 R),
            fun n => ENNReal.ofReal (b ω) * internalMetric d (domain n)
              (pair n).1 (pair n).2) ∈ pinchCoordinateEvent (U := U) I domain pair M ↔
            S11m.LocalRule.pinchLocalRule ν d W T Q' Q U V δ M) := by
  obtain ⟨domain, pair, R, hR, hv, hm, hd, hlaw⟩ :=
    h.exists_joint_smooth_shift_law_for_pinch_coordinates hμ hγ hγ2 hα hDfield haxioms
      hgeo I ψ hψ hψint hξ
  refine ⟨domain, pair, R, hR, hv, hm, hd, hlaw, ?_, ?_⟩
  · intro b hb M
    exact h.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms
      hgeo hR.1 I domain pair hd b hb M
  · intro g hg b hb M
    exact h.ae_shifted_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms hξ
      hgeo hR.1 I domain pair hd g hg b hb M




/-- Joint local-field and local triple events have equivalent null events
under every fixed smooth compact perturbation. -/
theorem IsWholePlaneGFF.pinchLocalRule_joint_smooth_shift_null_iff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc) (hξ : 0 ≤ ξ)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (E : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) (hE : MeasurableSet E)
    (M : ℝ) :
    P {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} = 0 ↔
    P {ω | localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule
        ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} = 0 := by
  let I := S11az.pinchCountSets V W T Q' Q δ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  obtain ⟨domain, pair, R, hR, _, _, hd, hlaw⟩ :=
    h.exists_joint_smooth_shift_law_and_aemeasurable_for_pinch_coordinates
      hμ hγ hγ2 hα hDfield haxioms hgeo I ψ hψ hψint hξ
  obtain ⟨hsb, hbs, hXm, hYm⟩ := hlaw g hg
  let X := fun ω =>
    (localModConstPairings α hC (ball 0 7) ω, normalizedRestriction (μ ω) (ball 0 R),
      fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
        internalMetric (D ω) (domain n) (pair n).1 (pair n).2)
  let Y := fun ω =>
    (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω,
      normalizedRestriction ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
      fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
        internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
          (domain n) (pair n).1 (pair n).2)
  let F := E ×ˢ pinchCoordinateEvent (U := U) I domain pair M
  have hF : MeasurableSet F := hE.prod (measurableSet_pinchCoordinateEvent hgeo.isOpen_U.measurableSet I domain pair M)
  have hx := h.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms
    hgeo hR.1 I domain pair hd (fun ω => Real.exp (ξ * (-hC ω ψ)))
      (fun _ => Real.exp_pos _) M
  have hy := h.ae_shifted_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms hξ
    hgeo hR.1 I domain pair hd g hg
      (fun ω => Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))))
      (fun _ => Real.exp_pos _) M
  have hxset : X ⁻¹' F =ᵐ[P] {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hx] with ω hω
    exact and_congr_right (fun _ => hω)
  have hyset : Y ⁻¹' F =ᵐ[P] {ω |
      localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule
        ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hy] with ω hω
    exact and_congr_right (fun _ => hω)
  have hxmap : P.map X F = P {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} := by
    rw [Measure.map_apply_of_aemeasurable hXm hF, measure_congr hxset]
  have hymap : P.map Y F = P {ω |
      localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule
        ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} := by
    rw [Measure.map_apply_of_aemeasurable hYm hF, measure_congr hyset]
  constructor
  · intro hzero
    rw [← hymap]
    exact hsb (hxmap.trans hzero)
  · intro hzero
    rw [← hxmap]
    exact hbs (hymap.trans hzero)


/-- The three literal local events have positive probability after a fixed
smooth compact shift if and only if they have positive probability before it. -/
theorem IsWholePlaneGFF.pinchLocal_events_smooth_shift_positive_iff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc) (hξ : 0 ≤ ξ)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g) (M : ℝ) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ} ↔
    0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) V W δ} := by
  have hzero := h.pinchLocalRule_joint_smooth_shift_null_iff hμ hγ hγ2 hα hDfield haxioms hξ
    hgeo g hg (univ : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) MeasurableSet.univ M
  simp only [mem_univ, true_and, S11m.LocalRule.pinchLocalRule] at hzero
  simpa only [pos_iff_ne_zero] using not_congr hzero

/-- The actual same-field form of the smooth-shift event law. -/
theorem IsWholePlaneGFF.pinchLocalRule_joint_smooth_shift_null_iff_actual
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (E : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) (hE : MeasurableSet E)
    (M : ℝ) :
    P {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} = 0 ↔
    P {ω | localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule
        ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} = 0 := by
  have hDfield' := hDfield
  obtain ⟨𝔇, h𝔇, _⟩ := hDfield'
  exact h.pinchLocalRule_joint_smooth_shift_null_iff hμ hγ hγ2 hα hDfield
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc)
    (isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇).le hgeo g hg E hE M

/-- The actual same-field form of the smooth-shift event law. -/
theorem IsWholePlaneGFF.pinchLocal_events_smooth_shift_positive_iff_actual
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g) (M : ℝ) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ} ↔
    0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) V W δ} := by
  have hDfield' := hDfield
  obtain ⟨𝔇, h𝔇, _⟩ := hDfield'
  exact h.pinchLocal_events_smooth_shift_positive_iff hμ hγ hγ2 hα hDfield
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc)
    (isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇).le hgeo g hg M

/-- The three local pinch events remain positive after a smooth compact shift. -/
theorem IsWholePlaneGFF.pinchLocal_shifted_three_positive
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g) (M : ℝ) (hM : 0 < M) :
    0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) V W δ} := by
  exact (h.pinchLocal_events_smooth_shift_positive_iff_actual hμ hγ hγ2 hα hDfield
    hgeo g hg M).mp (pinchLocal_three_positive hgeo hγ hγ2 hM hα P hC hcirc μ D h hμ hDfield)

end HarmonicBalls
