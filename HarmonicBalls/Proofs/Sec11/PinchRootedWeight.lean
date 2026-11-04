import HarmonicBalls.Proofs.Sec11.PinchRootedKernel
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Localizing the rooted sampling weight

A positive finite measurable weight can be bounded on a countable cover by
bounded Borel sets. Thus locally finite random measures have finite weighted
mass on that cover.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A bounded localization set for a finite weight. -/
noncomputable def weightedLocalization (w : ℂ → ℝ≥0∞) (n : ℕ) : Set ℂ :=
  ball 0 ((n : ℝ) + 1) ∩ {z | w z ≤ ENNReal.ofReal ((n : ℝ) + 1)}

/-- Measurable weights have measurable localization sets. -/
theorem measurableSet_weightedLocalization {w : ℂ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    MeasurableSet (weightedLocalization w n) :=
  measurableSet_ball.inter (measurableSet_le hw measurable_const)

/-- The localization sets cover the plane whenever the weight is finite. -/
theorem exists_mem_weightedLocalization {w : ℂ → ℝ≥0∞} (hw : ∀ z, w z ≠ ∞) (z : ℂ) :
    ∃ n, z ∈ weightedLocalization w n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ (w z).toReal)
  refine ⟨n, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    have := lt_of_le_of_lt (le_max_left ‖z‖ (w z).toReal) hn
    linarith
  · have ht : (w z).toReal < (n : ℝ) + 1 := by
      have := lt_of_le_of_lt (le_max_right ‖z‖ (w z).toReal) hn
      linarith
    change w z ≤ ENNReal.ofReal ((n : ℝ) + 1)
    rw [← ENNReal.ofReal_toReal (hw z)]
    exact ENNReal.ofReal_le_ofReal ht.le

/-- A locally finite measure gives finite weighted mass to every localization
set. No integrability near the origin is assumed. -/
theorem weightedLocalization_measure_ne_top (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {w : ℂ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    (μ.withDensity w) (weightedLocalization w n) ≠ ∞ := by
  have hB := measurableSet_weightedLocalization hw n
  have hbound : (μ.withDensity w) (weightedLocalization w n) ≤
      ENNReal.ofReal ((n : ℝ) + 1) * μ (ball 0 ((n : ℝ) + 1)) := by
    calc
      (μ.withDensity w) (weightedLocalization w n) =
          ∫⁻ z in weightedLocalization w n, w z ∂μ := withDensity_apply _ hB
      _ ≤ ∫⁻ _ in weightedLocalization w n, ENNReal.ofReal ((n : ℝ) + 1) ∂μ :=
          setLIntegral_mono' hB (fun _ hz => hz.2)
      _ = ENNReal.ofReal ((n : ℝ) + 1) * μ (weightedLocalization w n) :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((n : ℝ) + 1) * μ (ball 0 ((n : ℝ) + 1)) := by
          gcongr
          exact inter_subset_left
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) hbound

/-- The logarithmic density is the power weight away from the origin. Its
value at the origin is one, which makes it positive for every exponent. -/
noncomputable def logarithmicRootWeight (a : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a * Real.log ‖z‖))

theorem measurable_logarithmicRootWeight (a : ℝ) : Measurable (logarithmicRootWeight a) := by
  unfold logarithmicRootWeight
  exact (Real.measurable_exp.comp ((Real.measurable_log.comp measurable_norm).const_mul a)).ennreal_ofReal

theorem logarithmicRootWeight_ne_zero (a : ℝ) (z : ℂ) : logarithmicRootWeight a z ≠ 0 :=
  ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))

theorem logarithmicRootWeight_ne_top (a : ℝ) (z : ℂ) : logarithmicRootWeight a z ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem logarithmicRootWeight_eq_rpow (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    logarithmicRootWeight a z = ENNReal.ofReal (‖z‖ ^ a) := by
  rw [logarithmicRootWeight, Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm]

/-- The two versions of the power weight agree almost everywhere for a
measure with no atom at the origin. -/
theorem logarithmicRootWeight_ae_eq_rpow (μ : Measure ℂ) (h0 : μ {0} = 0) (a : ℝ) :
    logarithmicRootWeight a =ᵐ[μ] (fun z => ENNReal.ofReal (‖z‖ ^ a)) := by
  have hne : ∀ᵐ z ∂μ, z ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_eq_eq_singleton] using h0
  filter_upwards [hne] with z hz
  exact logarithmicRootWeight_eq_rpow a hz

/-- The staged non-atomicity input makes the logarithmic version and the
usual power-weighted LQG measure agree almost surely. -/
theorem IsWholePlaneGFF.ae_withDensity_logarithmicRootWeight_eq_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc) (a : ℝ) :
    ∀ᵐ ω ∂P, (μ ω).withDensity (logarithmicRootWeight a) =
      (μ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ a)) := by
  filter_upwards [hnonatom h hγ hγ₂ hα μ hμ] with ω hω
  exact withDensity_congr_ae (logarithmicRootWeight_ae_eq_rpow (μ ω) (hω 0) a)

/-- Finite positive weights and locally finite random measures discharge all
weight and localization assumptions of the rooted transfer. -/
theorem ae_ae_of_rooted_positive_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ν : ℕ → Measure (Ω × ℂ))
    (hac : ∀ n, P ⊗ₘ (weightedRestrictionKernel P μ hμ (weightedLocalization w n)
      (measurableSet_weightedLocalization hw n) w hw) ≪ ν n)
    {p : Ω → ℂ → Prop} (hp : ∀ n, ∀ᵐ x ∂ν n, p x.1 x.2) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  apply ae_ae_of_rooted_weighted_cover_of_aemeasurable P μ hμ
    (weightedLocalization w) (measurableSet_weightedLocalization hw)
    (exists_mem_weightedLocalization hfin) (fun _ => w) (fun _ => hw)
  · intro n
    exact Eventually.of_forall fun _ => Eventually.of_forall hpos
  · intro n
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact weightedLocalization_measure_ne_top (μ ω) hw n
  · exact hac
  · exact hp

/-- For an LQG measure, the logarithmic power weight yields a countable cover
with finite weighted masses. Only rooted-law comparison and its reference
almost-everywhere event remain to be supplied. -/
theorem IsWholePlaneGFF.ae_ae_of_rooted_logarithmicWeight
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (a : ℝ) (ν : ℕ → Measure (Ω × ℂ))
    (hac : ∀ n, P ⊗ₘ (weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (weightedLocalization (logarithmicRootWeight a) n)
      (measurableSet_weightedLocalization (measurable_logarithmicRootWeight a) n)
      (logarithmicRootWeight a) (measurable_logarithmicRootWeight a)) ≪ ν n)
    {p : Ω → ℂ → Prop} (hp : ∀ n, ∀ᵐ x ∂ν n, p x.1 x.2) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  exact ae_ae_of_rooted_positive_weight P μ (h.aemeasurable_lqgMeasure hμ) hloc
    (logarithmicRootWeight a) (measurable_logarithmicRootWeight a)
    (logarithmicRootWeight_ne_zero a) (logarithmicRootWeight_ne_top a) ν hac hp

#print axioms exists_mem_weightedLocalization
#print axioms weightedLocalization_measure_ne_top
#print axioms logarithmicRootWeight_eq_rpow
#print axioms logarithmicRootWeight_ae_eq_rpow
#print axioms IsWholePlaneGFF.ae_withDensity_logarithmicRootWeight_eq_rpow
#print axioms ae_ae_of_rooted_positive_weight
#print axioms IsWholePlaneGFF.ae_ae_of_rooted_logarithmicWeight

end HarmonicBalls
