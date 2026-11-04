import HarmonicBalls.Proofs.Sec6.DiscPotentialHolderTranslation
import HarmonicBalls.Proofs.Sec6.DiscRatioVolumeGrowth

/-! # Disc hitting estimates under volume growth -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess ProbabilityTheory
open scoped NNReal ENNReal

universe u

/-- On one event of full probability, every disc potential ratio bounds the
probability of hitting a compact exhaustion of full local LQG mass before
leaving that disc. -/
theorem ae_fineSupportDisc_circle_hitting_union_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r ε : ℝ, 0 < r → r ≤ ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      μ sample (ball c ε \ ⋃ n, K n) = 0 → ∀ x ∈ sphere c (r / 4),
      ENNReal.ofReal (greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ sample)) ≤
        planarBrownianMotion x {path | ContinuousPath.exitTime (⋃ n, K n)ᶜ path ≤
          ContinuousPath.exitTime (ball c r) path} := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_fineSupportDisc_ratio_pos_of_volumeGrowth hgrowth
    hγ hγ2 hα hGFF hμ] with sample hV hpos
  let : IsLocallyFiniteMeasure (μ sample) := hV.1
  intro c r ε hr hrε K hK hKmono hfull
  obtain ⟨_, _, _, _, R, hR, hsub⟩ := fineSupportDisc_geometry c hr
  apply fineSupportDisc_circle_hitting_union hr hrε hK hKmono hfull ?_ (hpos c r hr)
  intro f hf
  rw [closure_ball c hr.ne'] at hf ⊢
  exact greenPotential_disc_holderOnWith_of_volumeGrowth hr (hV.2 R hR) hsub hf

/-- The corresponding lower bound holds for Brownian motion started at the
centre of the disc. -/
theorem ae_fineSupportDisc_centre_hitting_union_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r ε : ℝ, 0 < r → r ≤ ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      μ sample (ball c ε \ ⋃ n, K n) = 0 →
      ENNReal.ofReal (greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ sample)) ≤
        planarBrownianMotion c {path | ContinuousPath.exitTime (⋃ n, K n)ᶜ path ≤
          ContinuousPath.exitTime (ball c r) path} := by
  filter_upwards [ae_fineSupportDisc_circle_hitting_union_of_volumeGrowth hgrowth
    hγ hγ2 hα hGFF hμ] with sample hhit
  intro c r ε hr hrε K hK hKmono hfull
  apply planarBrownian_hitting_probability_ge_of_circle (by positivity : 0 < r / 4)
    (by linarith : r / 4 < r) K hK
  exact hhit c r ε hr hrε K hK hKmono hfull

end HarmonicBalls.Section6
