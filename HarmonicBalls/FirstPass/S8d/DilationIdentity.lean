import HarmonicBalls.FirstPass.S8d.ProfileDilation
import HarmonicBalls.FirstPass.S8d.LQGLimitUnique
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.Proofs.Sec5.ScalingMeasure
import HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion

/-! # FIRST-PASS helper (fp-S8d, owner n4): the dilation identity of the profile LQG measure, almost surely

Let `F` be the measurable continuous circle-average profile of a whole-plane GFF (`ProfileVersion.lean`), let `ν` be the
γ-LQG measure of parameter `γ` (`α₀ = γ`), and let `Dec` be the measurable LQG-measure-of-profile map of the frozen input
`LQGMeasureOfProfileMeasurableFrozen` (E1). Then, for every `n`, almost surely

  `Dec (R^[n+1] (F ω)) = normalizedPullbackMeasure γ γ ((1/2)^{n+1}) (hcirc ω) (Dec (F ω))`,

where `R = continuousCircleDilation` (Proofs/GFF/ContinuousCircleDilationMixing.lean:19). The proof: the normalized pullback
field of the GFF has the LQG measure `normalizedPullbackMeasure` (`isLQGMeasureOfField_normalizedPullback`,
Proofs/Sec5/ScalingMeasure.lean:25, from the Proposed coordinate change); its circle profile is the dilated profile of
`F ω` (`s8d_circleProfile_dilation_iterate`); and the vague limit is unique (`s8d_isLQGLimit_unique`, with the frozen
Radon-uniqueness input). The Dec-limit property of `R^[n+1] (F ω)` comes from the measure preservation of `R` on the
profile law (`measurePreserving_continuousCircleDilation`, ContinuousCircleDilationMixing.lean:63) and E1.
No new mathematics. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- At positive radii, the circle profile of an almost-surely identified profile is the field's circle average. -/
theorem s8d_circleProfile_eq_of_ae (F : C(CircleParameter, ℝ)) (hcirc : ℝ → ℂ → ℝ)
    (hF : ∀ p : CircleParameter, F p = hcirc p.1 p.2) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    circleProfile F r z = hcirc r z := by
  unfold circleProfile
  simp only [hr, ↓reduceDIte]
  exact hF (⟨r, hr⟩, z)

/-- The dilation identity of the profile LQG measure, almost surely, for each iterate. -/
theorem s8d_dilation_identity_ae {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : γ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν : Ω → Measure ℂ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hCC : LQGMeasureCoordChange P γ γ hC hcirc)
    (hU : RadonIntegralUniqueFrozen)
    (F : Ω → C(CircleParameter, ℝ)) (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (Dec : C(CircleParameter, ℝ) → Measure ℂ)
    (hDecν : ∀ᵐ ω ∂P, ν ω = Dec (F ω))
    (hDecLim : ∀ᵐ y ∂(P.map F), IsLQGLimit γ (fieldCircleAverage γ (circleProfile y)) (Dec y))
    (n : ℕ) :
    ∀ᵐ ω ∂P, Dec (continuousCircleDilation^[n + 1] (F ω)) =
      normalizedPullbackMeasure γ γ ((1 / 2 : ℝ) ^ (n + 1)) (hcirc ω) (Dec (F ω)) := by
  have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  -- the LQG measure of the normalized pullback field (Proofs/Sec5/ScalingMeasure.lean:25)
  have h2 : ∀ᵐ ω ∂P, IsLQGLimit γ
      (fieldCircleAverage γ (fun r z => hcirc ω ((1 / 2 : ℝ) ^ (n + 1) * r) (((1 / 2 : ℝ) ^ (n + 1) : ℝ) • z) -
        hcirc ω ((1 / 2 : ℝ) ^ (n + 1)) 0))
      (normalizedPullbackMeasure γ γ ((1 / 2 : ℝ) ^ (n + 1)) (hcirc ω) (ν ω)) :=
    isLQGMeasureOfField_normalizedPullback hCC hGFF hγ0 hγ2 hα hν hk
  -- the Dec-limit property of the dilated profile, from measure preservation and E1
  have hmp := hGFF.measurePreserving_continuousCircleDilation hF hversion
  have hit := hmp.iterate (n + 1)
  have hq := hit.quasiMeasurePreserving.ae hDecLim
  have h4 : ∀ᵐ ω ∂P, IsLQGLimit γ
      (fieldCircleAverage γ (circleProfile (continuousCircleDilation^[n + 1] (F ω))))
      (Dec (continuousCircleDilation^[n + 1] (F ω))) :=
    ae_of_ae_map hF.aemeasurable hq
  have hae := IsWholePlaneGFF.ae_circle_map_eq_raw hGFF hversion
  filter_upwards [h2, h4, hae, hDecν] with ω hω2 hω4 hωae hων
  -- the profile of the dilated iterate is the normalized pullback of the circle averages
  have hcongr : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      fieldCircleAverage γ (circleProfile (continuousCircleDilation^[n + 1] (F ω))) ε z =
        fieldCircleAverage γ (fun r z => hcirc ω ((1 / 2 : ℝ) ^ (n + 1) * r)
          (((1 / 2 : ℝ) ^ (n + 1) : ℝ) • z) - hcirc ω ((1 / 2 : ℝ) ^ (n + 1)) 0) ε z := by
    intro ε hε z
    have hfin := s8d_circleProfile_dilation_iterate (F ω) n hε z
    have hpt : ∀ r : ℝ, 0 < r → ∀ w : ℂ, circleProfile (F ω) r w = hcirc ω r w :=
      fun r hr w => s8d_circleProfile_eq_of_ae (F ω) (hcirc ω) hωae hr w
    unfold fieldCircleAverage
    rw [hfin]
    have hk1 : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) * ε := mul_pos hk hε
    rw [hpt _ hk1, hpt _ hk]
    simp only [Complex.real_smul]
  have h5 : IsLQGLimit γ (fieldCircleAverage γ (circleProfile (continuousCircleDilation^[n + 1] (F ω))))
      (normalizedPullbackMeasure γ γ ((1 / 2 : ℝ) ^ (n + 1)) (hcirc ω) (ν ω)) :=
    (s8d_isLQGLimit_congr_pos γ (fun ε hε z => (hcongr ε hε z).symm) _).1 hω2
  have heq := s8d_isLQGLimit_unique hU hω4 h5
  rw [heq, hων]

#print axioms s8d_dilation_identity_ae

end HarmonicBalls
