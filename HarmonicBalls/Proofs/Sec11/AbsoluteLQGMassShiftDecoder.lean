import HarmonicBalls.Proofs.Sec11.RadialCirclePairingApproximation

/-! # Absolute LQG mass under pinned smooth shifts

The Section 8 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- Absolute finite-scale LQG masses on a buffered set are measurable
functions of the global modulo-constant field, simultaneously under continuous
shifts preserving the pinned circle average. -/
theorem IsWholePlaneGFF.exists_global_shifted_lqgApprox_mass_decoders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (A : Set ℂ) (hA : MeasurableSet A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞,
      (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ n (g : ℂ → ℝ), Continuous g → Real.circleAverage g 0 1 = 0 →
        F n (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
          lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) g) (dyadicScale n) A := by
  obtain ⟨D, hDm, hDeq⟩ := hGFF.exists_global_joint_absolute_circle_shift_decoders
    (α := α) (ε := ε) dyadicScale dyadicScale_pos
  let F : ℕ → (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞ := fun n v =>
    (volume.withDensity fun z => ENNReal.ofReal
      ((dyadicScale n) ^ (γ ^ 2 / 2) * Real.exp (γ * D n v z))) A
  refine ⟨F, ?_, ?_⟩
  · intro n
    apply (Measure.measurable_coe hA).comp
    apply measurable_withDensity
    exact (measurable_const.mul ((measurable_const.mul (hDm n)).exp)).ennreal_ofReal
  · filter_upwards [hDeq] with ω heq n g hg hpin
    dsimp [F, lqgApprox]
    rw [withDensity_apply _ hA, withDensity_apply _ hA]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hA] with z hz
    rw [heq n g hg hpin z (hbuffer n z hz)]
    rfl


/-- The absolute LQG mass of a bounded continuity set is decoded from the
global modulo-constant field, with one exceptional set for every continuous
shift that preserves the unit-circle normalization. -/
theorem IsWholePlaneGFF.exists_global_shifted_lqgMass_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set ℂ) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier A) = 0) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
          ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) A := by
  obtain ⟨M, hMm, hMe⟩ :=
    hGFF.exists_global_shifted_lqgApprox_mass_decoders (γ := γ) (α := α) A hA hbuffer
  let F := fun v => liminf (fun n => M n v) atTop
  have hF : Measurable F := Measurable.liminf hMm
  refine ⟨F, hF, ?_⟩
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [hμ, hc, hfront, hMe] with ω hω hcω hfrontω heqω g hg hpin
  let ν := (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))
  have hshift := Section6.isLQGLimit_addCircleAverage hω hcω g hg
  let : IsLocallyFiniteMeasure ν := hshift.isLocallyFiniteMeasure
  have hcshift : ∀ n, Continuous (addCircleAverage (fieldCircleAverage α (hcirc ω)) g
      (dyadicScale n)) := fun n => (hcω n).add
        ((Section6.continuous_circleAverage_radius_center hg).comp
          (continuous_const.prodMk continuous_id))
  let ρ : ℕ → Measure ℂ := fun n => lqgApprox γ
    (addCircleAverage (fieldCircleAverage α (hcirc ω)) g) (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (ρ n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ _ _ (hcshift n)
  have hνfront : ν (frontier A) = 0 := (withDensity_absolutelyContinuous _ _) hfrontω
  have ht : Tendsto (fun n => ρ n A) atTop (𝓝 (ν A)) :=
    tendsto_measure_of_tendsto_compactlySupported ρ ν hshift.tendsto_integral hbounded hνfront
  have ht' : Tendsto (fun n => M n (localModConstPairings α
      (fun ω => addFunPairing (hC ω) g) univ ω)) atTop (𝓝 (ν A)) := by
    convert ht using 1
    funext n
    exact heqω n g hg hpin
  exact ht'.liminf_eq

end HarmonicBalls
