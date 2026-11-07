import HarmonicBalls.Proofs.Potential.LQGGreenPotentialExceptionalSet
import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability

/-! # Transposed Green kernels at typical observers

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The observation exceptional set can depend on the domain and source.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- For a finite compact source, local upper growth removes the exceptional
observers for the literal transposed kernel, the Newton kernel, and atoms. -/
theorem ae_transposedGreen_integrable_of_local_upper_growth
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (s : ℝ) :
    ∀ᵐ x ∂μ.restrict (ball 0 s),
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (newtonKernel x) ν ∧ ν {x} = 0 := by
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  let R := max r 1
  have hsub : V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  filter_upwards [ae_greenPotential_of_local_upper_growth hup isOpen_ball isBounded_ball hK hν s,
    ae_logPotential_of_local_upper_growth hup hK hν s] with x hx hn
  have hi : Integrable (fun y => greenFunction (ball (0 : ℂ) R) y x) ν := by
    simpa only [greenFunction_ball_comm R] using hx.1
  refine ⟨?_, hn.1, hn.2.1⟩
  apply hi.mono_nonneg
    ((measurable_greenFunction_uncurry hV).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => greenFunction_nonneg hVb y x
  · exact Eventually.of_forall fun y =>
      Section6.greenFunction_le_of_subset hsub isBounded_ball y x

/-- The exceptional observers form a null set on the whole plane. -/
theorem ae_transposedGreen_integrable_of_local_upper_growth_global
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hν : ν Kᶜ = 0) :
    ∀ᵐ x ∂μ, Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (newtonKernel x) ν ∧ ν {x} = 0 := by
  have h := (ae_restrict_iUnion_iff (μ := μ) (s := fun n : ℕ => ball (0 : ℂ) n) _).2
    (fun n => ae_transposedGreen_integrable_of_local_upper_growth hup hV hVb hK hν n)
  simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h

universe u

/-- I2 gives one probability-one event for all domains and compact sources;
the observer null set may depend on those choices. -/
theorem ae_lqg_transposedGreen_integrable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (V K : Set ℂ) (ν : Measure ℂ),
      IsOpen V → Bornology.IsBounded V → IsCompact K → K ⊆ V →
      ν Kᶜ = 0 → IsFiniteMeasure ν →
      ∀ᵐ x ∂μ ω,
        Integrable (fun y => greenFunction V y x) ν ∧
        Integrable (newtonKernel x) ν ∧ ν {x} = 0 := by
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
  intro V K ν hV hVb hK _ hν hf
  let : IsFiniteMeasure ν := hf
  exact ae_transposedGreen_integrable_of_local_upper_growth_global hup hV hVb hK hν

#print axioms ae_transposedGreen_integrable_of_local_upper_growth
#print axioms ae_transposedGreen_integrable_of_local_upper_growth_global
#print axioms ae_lqg_transposedGreen_integrable

end HarmonicBalls
