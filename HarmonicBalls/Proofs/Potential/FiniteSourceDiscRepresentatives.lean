import HarmonicBalls.Proofs.Potential.FiniteSourceDiscCorrection
import HarmonicBalls.Proofs.Potential.LQGGreenPotentialExceptionalSet

/-!
# Finite-source disc representatives

This analytic leaf uses the potential-theoretic work of Leonardo Bonanno.
The almost-everywhere identity does not assert membership in a bounded pointwise
 test class or close a numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace
open scoped ENNReal

/-- For two finite compact sources, the two kernel integrability conditions and
uncharged diagonals hold simultaneously at almost every interior observer. The
whole-plane representative uses the explicitly signed harmonic correction. -/
theorem ae_finiteSource_disc_representative
    {μ ν₁ ν₂ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} {K₁ K₂ : Set ℂ} {q : ℂ → ℝ}
    (hR : 0 < R) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hKB₁ : K₁ ⊆ ball (0 : ℂ) R) (hKB₂ : K₂ ⊆ ball (0 : ℂ) R)
    (hν₁ : ν₁ K₁ᶜ = 0) (hν₂ : ν₂ K₂ᶜ = 0)
    (hq : HarmonicOnNhd q (ball 0 R)) :
    HarmonicOnNhd (fun x => q x - discSourceCorrection R ν₁ x +
      discSourceCorrection R ν₂ x) (ball 0 R) ∧
    ∀ᵐ x ∂μ.restrict (ball 0 R),
      Integrable (fun y => greenFunction univ x y) ν₁ ∧
      Integrable (greenFunction (ball 0 R) x) ν₁ ∧ ν₁ {x} = 0 ∧
      Integrable (fun y => greenFunction univ x y) ν₂ ∧
      Integrable (greenFunction (ball 0 R) x) ν₂ ∧ ν₂ {x} = 0 ∧
      q x + greenPotential (ball 0 R) ν₁ x - greenPotential (ball 0 R) ν₂ x =
        (q x - discSourceCorrection R ν₁ x + discSourceCorrection R ν₂ x) +
          greenPotential univ ν₁ x - greenPotential univ ν₂ x := by
  have hsrc₁ : ∀ᵐ y ∂ν₁, y ∈ ball (0 : ℂ) R :=
    (ae_iff.mpr hν₁).mono fun _ hy => hKB₁ hy
  have hsrc₂ : ∀ᵐ y ∂ν₂, y ∈ ball (0 : ℂ) R :=
    (ae_iff.mpr hν₂).mono fun _ hy => hKB₂ hy
  constructor
  · exact (hq.sub (harmonicOnNhd_discSourceCorrection hR hK₁ hKB₁ hν₁)).add
      (harmonicOnNhd_discSourceCorrection hR hK₂ hKB₂ hν₂)
  · filter_upwards [ae_logPotential_of_local_upper_growth hup hK₁ hν₁ R,
      ae_logPotential_of_local_upper_growth hup hK₂ hν₂ R,
      ae_greenPotential_of_local_upper_growth hup isOpen_ball isBounded_ball hK₁ hν₁ R,
      ae_greenPotential_of_local_upper_growth hup isOpen_ball isBounded_ball hK₂ hν₂ R,
      ae_restrict_mem measurableSet_ball] with x hu₁ hu₂ hb₁ hb₂ hx
    have hi₁ : Integrable (fun y => greenFunction univ x y) ν₁ := by
      simpa only [greenFunction_univ_eq_newtonKernel] using hu₁.1
    have hi₂ : Integrable (fun y => greenFunction univ x y) ν₂ := by
      simpa only [greenFunction_univ_eq_newtonKernel] using hu₂.1
    have he₁ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hsrc₁ hx hu₁.2.1 hi₁ hb₁.1
    have he₂ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hsrc₂ hx hu₂.2.1 hi₂ hb₂.1
    refine ⟨hi₁, hb₁.1, hu₁.2.1, hi₂, hb₂.1, hu₂.2.1, ?_⟩
    linarith

universe u

/-- I2 supplies the growth event simultaneously for every disc and finite
compact source pair. The exceptional observation set can depend on these choices. -/
theorem ae_lqg_finiteSource_disc_representative
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (R : ℝ) (K₁ K₂ : Set ℂ) (ν₁ ν₂ : Measure ℂ)
      (q : ℂ → ℝ),
      0 < R → IsCompact K₁ → IsCompact K₂ →
      K₁ ⊆ ball (0 : ℂ) R → K₂ ⊆ ball (0 : ℂ) R →
      ν₁ K₁ᶜ = 0 → ν₂ K₂ᶜ = 0 → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      HarmonicOnNhd q (ball 0 R) →
      HarmonicOnNhd (fun x => q x - discSourceCorrection R ν₁ x +
        discSourceCorrection R ν₂ x) (ball 0 R) ∧
      ∀ᵐ x ∂(μ ω).restrict (ball 0 R),
        Integrable (fun y => greenFunction univ x y) ν₁ ∧
        Integrable (greenFunction (ball 0 R) x) ν₁ ∧ ν₁ {x} = 0 ∧
        Integrable (fun y => greenFunction univ x y) ν₂ ∧
        Integrable (greenFunction (ball 0 R) x) ν₂ ∧ ν₂ {x} = 0 ∧
        q x + greenPotential (ball 0 R) ν₁ x - greenPotential (ball 0 R) ν₂ x =
          (q x - discSourceCorrection R ν₁ x + discSourceCorrection R ν₂ x) +
            greenPotential univ ν₁ x - greenPotential univ ν₂ x := by
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
  intro R K₁ K₂ ν₁ ν₂ q hR hK₁ hK₂ hKB₁ hKB₂ hν₁ hν₂ hf₁ hf₂ hq
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  exact ae_finiteSource_disc_representative hup hR hK₁ hK₂ hKB₁ hKB₂ hν₁ hν₂ hq



end HarmonicBalls
