import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedObservationIntegrability

/-!
# Observation integrability for finite sources

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Mixed integrability for a finite source concentrated in a bounded open domain. -/
theorem generalDomain_green_integrable_product_of_local_upper_growth
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) :
    Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R :=
    hν.mono fun _ hy => ball_subset_closedBall (hsub hy)
  obtain ⟨r₀, β, hr₀, hβ, hg⟩ := hup R hR
  have hb := green_disc_integrable_product_of_upper (ν := ν) hR hr₀ hβ hg
    (measure_ball_lt_top (μ := μ)).ne
  rw [Measure.restrict_eq_self_of_ae_mem hνR] at hb
  have hb' := hb.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  exact hb'.mono_nonneg (measurable_greenFunction_uncurry hV).aestronglyMeasurable
    (Eventually.of_forall fun p => greenFunction_nonneg hVb p.1 p.2)
    (Eventually.of_forall fun p =>
      Section6.greenFunction_le_of_subset hsub isBounded_ball p.1 p.2)

/-- The source kernel is integrable at almost every observer, and its literal
transposed potential is integrable against the restricted observer measure. -/
theorem finiteSource_transposedGreen_observation_integrability
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) :
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => greenFunction V y x) ν) ∧
    Integrable (fun x => ∫ y, greenFunction V y x ∂ν) (μ.restrict V) := by
  have hp := generalDomain_green_integrable_product_of_local_upper_growth hup hV hVb hν
  exact ⟨hp.prod_left_ae, hp.integral_prod_right⟩

universe u

/-- One I2 event works for every bounded open domain and finite source;
the exceptional observer set may depend on the domain and source. -/
theorem ae_lqg_finiteSource_transposedGreen_observation_integrability
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (V : Set ℂ) (ν : Measure ℂ),
      IsOpen V → Bornology.IsBounded V → IsFiniteMeasure ν →
      (∀ᵐ y ∂ν, y ∈ V) →
      (∀ᵐ x ∂(μ ω).restrict V, Integrable (fun y => greenFunction V y x) ν) ∧
      Integrable (fun x => ∫ y, greenFunction V y x ∂ν) ((μ ω).restrict V) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have ha : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    apply lt_min
    · have : 0 < 2 - γ := by linarith
      positivity
    · exact mul_pos hγ (sub_pos.mpr hα)
  let β : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβlt : β < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    dsimp [β]; linarith
  let B : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hB : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < B := by
    dsimp [B]; linarith
  filter_upwards [hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hgrowth hlocal
  let : IsLocallyFiniteMeasure (μ ω) := hlocal.isLocallyFiniteMeasure
  have hup : ∀ R : ℝ, 0 < R → ∃ r₀ b : ℝ, 0 < r₀ ∧ 0 < b ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ ω (ball z r) ≤ ENNReal.ofReal (r ^ b) := by
    intro R hR
    obtain ⟨r₀, hr₀, hg⟩ := hgrowth R hR β B hβ hβlt hB
    exact ⟨r₀, β, hr₀, hβ, fun r hr hrr z hz => (hg r hr hrr z hz).2⟩
  intro V ν hV hVb hf hν
  let : IsFiniteMeasure ν := hf
  exact finiteSource_transposedGreen_observation_integrability hup hV hVb hν

#print axioms ae_lqg_finiteSource_transposedGreen_observation_integrability
#print axioms generalDomain_green_integrable_product_of_local_upper_growth
#print axioms finiteSource_transposedGreen_observation_integrability

end HarmonicBalls
