import HarmonicBalls.Proofs.Sec6.CanonicalSingularMeasures
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec5.MeasureLawRegularity
import Mathlib.Probability.Kernel.WithDensity

/-! # Joint measurability of singular LQG measures

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The existence assumptions
below are literature inputs (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- Locally finite measures with their induced measurable structure. -/
abbrev LocallyFinitePlanarMeasure := {μ : Measure ℂ // IsLocallyFiniteMeasure μ}

/-- A finite normalized restriction, multiplied by its finite mass, is the
original restriction. -/
theorem mass_smul_normalizedRestriction (μ : Measure ℂ) (B : Set ℂ) (hfin : μ B ≠ ∞) :
    μ B • normalizedRestriction μ B = μ.restrict B := by
  rw [normalizedRestriction, smul_smul]
  by_cases hz : μ B = 0
  · have hzero : μ.restrict B = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using hz
    simp [hzero]
  · rw [ENNReal.mul_inv_cancel hz hfin, one_smul]

/-- Weighting a locally finite planar measure by a jointly measurable density
is jointly measurable in the measure and parameter. -/
theorem measurable_withDensity_locallyFinite {A : Type*} [MeasurableSpace A]
    (w : A → ℂ → ℝ≥0∞) (hw : Measurable (Function.uncurry w)) :
    Measurable (fun p : LocallyFinitePlanarMeasure × A => p.1.1.withDensity (w p.2)) := by
  rw [Measure.measurable_measure]
  intro S hS
  let B : ℕ → Set ℂ := fun n => closedBall 0 n
  have hB (n : ℕ) : MeasurableSet (B n) := isClosed_closedBall.measurableSet
  let κ (n : ℕ) : Kernel (LocallyFinitePlanarMeasure × A) ℂ :=
    (normalizedRestrictionKernel (B n) (hB n)).comap (fun p => p.1.1)
      (measurable_subtype_coe.comp measurable_fst)
  let a (n : ℕ) : LocallyFinitePlanarMeasure × A → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (p.1.1 (B n)).toReal
  have ha (n : ℕ) : Measurable (a n) := by
    exact (((Measure.measurable_coe (hB n)).comp
      (measurable_subtype_coe.comp measurable_fst)).ennreal_toReal).ennreal_ofReal
  let η (n : ℕ) : Kernel (LocallyFinitePlanarMeasure × A) ℂ :=
    (κ n).withDensity (fun p _ => a n p)
  have hη (n : ℕ) : IsSFiniteKernel (η n) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  have hηeq (n : ℕ) (p : LocallyFinitePlanarMeasure × A) : η n p = p.1.1.restrict (B n) := by
    let : IsLocallyFiniteMeasure p.1.1 := p.1.2
    have hfin : p.1.1 (B n) ≠ ∞ := (isCompact_closedBall (0 : ℂ) n).measure_ne_top
    change ((κ n).withDensity (fun p _ => a n p)) p = _
    have hunc : Measurable (Function.uncurry (fun p : LocallyFinitePlanarMeasure × A =>
        fun _ : ℂ => a n p)) := (ha n).comp measurable_fst
    rw [Kernel.withDensity_apply _ hunc, withDensity_const]
    change a n p • normalizedRestriction p.1.1 (B n) = _
    rw [show a n p = p.1.1 (B n) from ENNReal.ofReal_toReal hfin]
    exact mass_smul_normalizedRestriction _ _ hfin
  have hw' : Measurable (Function.uncurry (fun p : LocallyFinitePlanarMeasure × A => w p.2)) := by
    exact hw.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  let θ (n : ℕ) : Kernel (LocallyFinitePlanarMeasure × A) ℂ :=
    letI := hη n
    (η n).withDensity (fun p => w p.2)
  have hθ (n : ℕ) (p : LocallyFinitePlanarMeasure × A) :
      θ n p = (p.1.1.withDensity (w p.2)).restrict (B n) := by
    let := hη n
    change ((η n).withDensity (fun p => w p.2)) p = _
    rw [Kernel.withDensity_apply _ hw', hηeq, restrict_withDensity (hB n)]
  have hmeas (n : ℕ) : Measurable (fun p : LocallyFinitePlanarMeasure × A =>
      (p.1.1.withDensity (w p.2)) (S ∩ B n)) := by
    have ht := (θ n).measurable_coe hS
    convert ht using 1
    funext p
    rw [hθ, Measure.restrict_apply hS]
  have heq (p : LocallyFinitePlanarMeasure × A) :
      (p.1.1.withDensity (w p.2)) S =
        ⨆ n : ℕ, (p.1.1.withDensity (w p.2)) (S ∩ B n) := by
    have hm : Monotone (fun n : ℕ => S ∩ B n) := by
      intro i j hij
      exact inter_subset_inter_right S (closedBall_subset_closedBall (by exact_mod_cast hij))
    rw [← hm.measure_iUnion, iUnion_inter_closedBall_nat]
  simp_rw [heq]
  exact Measurable.iSup hmeas

/-- A measurable random-measure representative can be chosen locally
finite at every sample whenever the original measure is locally finite
a.e. -/
theorem exists_measurable_locallyFinite_modification
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hm : AEMeasurable μ P) (hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∃ ν : Ω → Measure ℂ, Measurable ν ∧ (∀ ω, IsLocallyFiniteMeasure (ν ω)) ∧ ν =ᵐ[P] μ := by
  classical
  let μm := hm.mk μ
  let E : Set Ω := {ω | IsLocallyFiniteMeasure (μm ω)}
  have hE : MeasurableSet E :=
    measurableSet_isLocallyFiniteMeasure_complex.preimage hm.measurable_mk
  let ν : Ω → Measure ℂ := E.piecewise μm (fun _ => 0)
  have hν : Measurable ν := hm.measurable_mk.piecewise hE measurable_const
  have hνl (ω : Ω) : IsLocallyFiniteMeasure (ν ω) := by
    by_cases h : ω ∈ E
    · have hlm : IsLocallyFiniteMeasure (μm ω) := h
      change IsLocallyFiniteMeasure (E.piecewise μm (fun _ => 0) ω)
      simpa only [Set.piecewise, ite_eq_left h] using hlm
    · simpa [ν, h] using (inferInstance : IsLocallyFiniteMeasure (0 : Measure ℂ))
  refine ⟨ν, hν, hνl, ?_⟩
  filter_upwards [hm.ae_eq_mk, hl] with ω hω hlω
  change μ ω = μm ω at hω
  have hωE : ω ∈ E := by
    change IsLocallyFiniteMeasure (μm ω)
    rw [← hω]
    exact hlω
  simpa [ν, hωE] using hω.symm

/-- A locally finite random measure admits a jointly measurable weighted
version simultaneously for all parameter values. -/
theorem exists_jointly_measurable_weighted_modification
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hm : AEMeasurable μ P)
    (hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : A → ℂ → ℝ≥0∞) (hw : Measurable (Function.uncurry w)) :
    ∃ M : Ω × A → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, ∀ a, M (ω, a) = (μ ω).withDensity (w a) := by
  obtain ⟨ν, hν, hνl, hνeq⟩ := exists_measurable_locallyFinite_modification P μ hm hl
  let νl : Ω → LocallyFinitePlanarMeasure := fun ω => ⟨ν ω, hνl ω⟩
  have hνlm : Measurable νl := hν.subtype_mk (h := hνl)
  let M : Ω × A → Measure ℂ := fun p => (ν p.1).withDensity (w p.2)
  have hpair : Measurable (fun p : Ω × A => (νl p.1, p.2)) :=
    (hνlm.comp measurable_fst).prodMk measurable_snd
  have hM0 := (measurable_withDensity_locallyFinite w hw).comp hpair
  have hM : Measurable M := hM0
  refine ⟨M, hM, ?_⟩
  filter_upwards [hνeq] with ω hω a
  change (ν ω).withDensity (w a) = (μ ω).withDensity (w a)
  rw [hω]

/-- A jointly measurable random measure realizes all subcritical singular
LQG measures on one full-measure event. No joint-measurability hypothesis on
the original choice of limits is needed. -/
theorem exists_jointly_measurable_subcritical_lqgMeasures
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀, hcanonical⟩ :=
    exists_ae_canonical_subcritical_lqgMeasures P γ hγ hγ2 hC hcirc hG hE
  have hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ₀ ω) := by
    filter_upwards [hμ₀] with ω hω
    exact hω.isLocallyFiniteMeasure
  let w : ℝ → ℂ → ℝ≥0∞ := fun α z =>
    ENNReal.ofReal (Real.exp (-(γ * α) * Real.log ‖z‖))
  have hw : Measurable (Function.uncurry w) := by
    exact ((measurable_const.mul measurable_fst).neg.mul
      (Real.measurable_log.comp measurable_snd.norm)).exp.ennreal_ofReal
  obtain ⟨M, hM, hMeq⟩ := exists_jointly_measurable_weighted_modification P μ₀
    (hG.aemeasurable_lqgMeasure hμ₀) hl w hw
  refine ⟨M, hM, ?_⟩
  filter_upwards [hμ₀, hcanonical, hMeq,
      ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE]
    with ω hm₀ hcanonical hMeq hzero α hα
  have hne : ∀ᵐ z ∂(μ₀ ω), z ≠ (0 : ℂ) := by
    simpa [ae_iff] using hzero 0 hQ (μ₀ ω) hm₀
  have heq : M (ω, α) = (μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
    rw [hMeq α]
    apply withDensity_congr_ae
    filter_upwards [hne] with z hz
    dsimp [w]
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 2
    ring
  rw [heq]
  exact (hcanonical α hα).1

end HarmonicBalls.Section6
