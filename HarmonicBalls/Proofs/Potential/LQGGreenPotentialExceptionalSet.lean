import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet
import HarmonicBalls.Draft.Section2

/-!
# LQG Green-potential exceptional sets

The potential-theoretic infrastructure uses work of Leonardo Bonanno.  The
exceptional observation set may depend on the domain and the source measures.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- I2 and local finiteness give one event on which the extended and real
Green potentials agree almost everywhere on each bounded observation set.
The signed assertion is simultaneous in the sources, but its null set may
still depend on them. -/
theorem ae_lqg_greenPotential_exceptional_set
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P,
      (∀ (O K S : Set ℂ) (ν : Measure ℂ), IsOpen O → Bornology.IsBounded O →
        IsCompact K → ν Kᶜ = 0 → IsFiniteMeasure ν → Bornology.IsBounded S →
        ∀ᵐ x ∂(μ ω).restrict S,
          Integrable (greenFunction O x) ν ∧ ν {x} = 0 ∧
          (∫⁻ y, greenKernelExtended O x y ∂ν) < ⊤ ∧
          (∫⁻ y, greenKernelExtended O x y ∂ν) = ENNReal.ofReal (greenPotential O ν x)) ∧
      (∀ (O K₁ K₂ S : Set ℂ) (ν₁ ν₂ : Measure ℂ),
        IsOpen O → Bornology.IsBounded O → IsCompact K₁ → IsCompact K₂ →
        ν₁ K₁ᶜ = 0 → ν₂ K₂ᶜ = 0 → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
        Bornology.IsBounded S → ∀ᵐ x ∂(μ ω).restrict S,
          (∫⁻ y, greenKernelExtended O x y ∂ν₁) < ⊤ ∧
          (∫⁻ y, greenKernelExtended O x y ∂ν₂) < ⊤ ∧
          greenPotential O ν₁ x - greenPotential O ν₂ x =
            (∫⁻ y, greenKernelExtended O x y ∂ν₁).toReal -
              (∫⁻ y, greenKernelExtended O x y ∂ν₂).toReal) := by
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
  constructor
  · intro O K S ν hO hOb hK hν hfinite hS
    let : IsFiniteMeasure ν := hfinite
    obtain ⟨s, hs⟩ := hS.subset_ball (0 : ℂ)
    exact Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
      (ae_greenPotential_of_local_upper_growth hup hO hOb hK hν s)
  · intro O K₁ K₂ S ν₁ ν₂ hO hOb hK₁ hK₂ hν₁ hν₂ hf₁ hf₂ hS
    let : IsFiniteMeasure ν₁ := hf₁
    let : IsFiniteMeasure ν₂ := hf₂
    obtain ⟨s, hs⟩ := hS.subset_ball (0 : ℂ)
    exact Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
      (ae_greenPotential_sub_of_local_upper_growth hup hO hOb hK₁ hK₂ hν₁ hν₂ s)

#print axioms ae_lqg_greenPotential_exceptional_set

end HarmonicBalls
