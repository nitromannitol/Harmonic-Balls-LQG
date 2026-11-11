import HarmonicBalls.Steps.Sec11.PinchJointMeasure

/-! # Kernel representation of a locally finite random measure

A countable disjoint bounded partition allows the canonical finite-mass
restriction kernels to be combined into an s-finite kernel. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

private def ballShell (n : ℕ) : Set ℂ :=
  disjointed (fun n : ℕ => ball (0 : ℂ) ((n : ℝ) + 1)) n

private theorem ballShell_measurable (n : ℕ) : MeasurableSet (ballShell n) :=
  MeasurableSet.disjointed (fun _ => measurableSet_ball) n

private theorem iUnion_ballShell : (⋃ n, ballShell n) = univ := by
  change (⋃ n, disjointed (fun n : ℕ => ball (0 : ℂ) ((n : ℝ) + 1)) n) = univ
  rw [iUnion_disjointed]
  apply eq_univ_iff_forall.mpr
  intro z
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  rw [mem_ball_zero_iff]
  linarith

/-- An s-finite kernel representing an almost-everywhere locally finite
random measure on a common full-measure set. -/
noncomputable def locallyFiniteRandomMeasureKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) : Kernel Ω ℂ :=
  Kernel.sum fun n => unnormalizedWeightedRestrictionKernel P μ hμ
    (ballShell n) (ballShell_measurable n) 1 measurable_const

instance locallyFiniteRandomMeasureKernel_sfinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) :
    IsSFiniteKernel (locallyFiniteRandomMeasureKernel P μ hμ) := by
  unfold locallyFiniteRandomMeasureKernel
  apply Kernel.isSFiniteKernel_sum_of_denumerable
  intro n
  exact unnormalizedWeightedRestrictionKernel_sfinite P μ hμ _ _ 1 measurable_const

/-- Local finiteness identifies the kernel with the original random measure
simultaneously on all Borel sets. -/
theorem ae_locallyFiniteRandomMeasureKernel_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∀ᵐ ω ∂P, locallyFiniteRandomMeasureKernel P μ hμ ω = μ ω := by
  have hfinite (n : ℕ) : ∀ᵐ ω ∂P, ((μ ω).withDensity 1) (ballShell n) ≠ ∞ := by
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    rw [withDensity_one]
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (disjointed_subset _ _))
  have heq (n : ℕ) : ∀ᵐ ω ∂P,
      unnormalizedWeightedRestrictionKernel P μ hμ (ballShell n)
        (ballShell_measurable n) 1 measurable_const ω = (μ ω).restrict (ballShell n) := by
    simpa only [withDensity_one] using
      ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ (ballShell n)
        (ballShell_measurable n) 1 measurable_const (hfinite n)
  filter_upwards [ae_all_iff.mpr heq] with ω hω
  rw [locallyFiniteRandomMeasureKernel, Kernel.sum_apply]
  simp_rw [hω]
  change (Measure.sum fun n => (μ ω).restrict
    (disjointed (fun n : ℕ => ball (0 : ℂ) ((n : ℝ) + 1)) n)) = μ ω
  rw [← Measure.restrict_iUnion (disjoint_disjointed _) ballShell_measurable]
  change (μ ω).restrict (⋃ n, ballShell n) = μ ω
  rw [iUnion_ballShell, Measure.restrict_univ]

/-- Moving-center annular Green suprema have a jointly measurable
representative, agreeing simultaneously at every center almost surely. -/
theorem exists_jointlyMeasurable_annulusGreenPotentialSup
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) (a b : ℝ) :
    ∃ G : Ω × ℂ → ℝ≥0∞, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z, G (ω, z) = annulusGreenPotentialSup (μ ω) z a b := by
  let κ := locallyFiniteRandomMeasureKernel P μ hμ
  refine ⟨fun p => annulusGreenPotentialSup (κ p.1) p.2 a b,
    measurable_kernel_annulusGreenPotentialSup κ a b, ?_⟩
  filter_upwards [ae_locallyFiniteRandomMeasureKernel_eq P μ hμ hloc] with ω hω
  intro z
  rw [hω]

/-- Moving-center masses of rescaled open sets have jointly measurable
representatives, agreeing simultaneously at every center almost surely. -/
theorem exists_jointlyMeasurable_rescaledSet_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (U : Set ℂ) (hU : IsOpen U) {r : ℝ} (hr : r ≠ 0) :
    ∃ F : Ω × ℂ → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ z, F (ω, z) = μ ω (rescaledSet U r z) := by
  let κ := locallyFiniteRandomMeasureKernel P μ hμ
  refine ⟨fun p => κ p.1 (rescaledSet U r p.2),
    measurable_kernel_rescaledSet_mass κ U hU hr, ?_⟩
  filter_upwards [ae_locallyFiniteRandomMeasureKernel_eq P μ hμ hloc] with ω hω
  intro z
  rw [hω]

/-- The mass-versus-potential part of the pinch event has a jointly
measurable representative, with one exceptional sample set for all centers. -/
theorem exists_jointlyMeasurable_pinch_mass_potential_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (U : Set ℂ) (hU : IsOpen U) (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ∃ E : Set (Ω × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ z, ((ω, z) ∈ E ↔
        ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r) <
          μ ω (rescaledSet U r z)) := by
  obtain ⟨G, hG, hGae⟩ := exists_jointlyMeasurable_annulusGreenPotentialSup P μ hμ hloc
    (3 * r) (6 * r)
  obtain ⟨F, hF, hFae⟩ := exists_jointlyMeasurable_rescaledSet_mass P μ hμ hloc U hU hr
  refine ⟨{p | ENNReal.ofReal M * G p < F p},
    measurableSet_lt (measurable_const.mul hG) hF, ?_⟩
  filter_upwards [hGae, hFae] with ω hg hf
  intro z
  simp only [hg z, hf z]


end HarmonicBalls
