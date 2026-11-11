import HarmonicBalls.FirstPass.S11h.CoordDistDiam11_17
import HarmonicBalls.FirstPass.S11h.SphereSup11_17
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11g

/-!
# Lemma 11.17, coordinate 0 of `pinchScalars`: the closed-corridor internal supremum

The coordinate `⨆ y ∈ ∂B₅(0), internalMetric D (B_{2δ}(Q ∪ W))ᶜ 0 y` of `pinchScalars` (`CertScalars11_17.lean`) is a
measurable field functional of the shifted field. The corridor is closed (the paper defines `internalMetric` for open
sets only, printed inconsistency Q2, so the closed-set formula is the frozen input
`InternalMetricClosedEqIInfThickeningFrozen`). The decoder uses the open-set decoders
`LQGInternalMetricWeylAeMeasurableFrozen` on countably many open sets `thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))`
and countably many points `y` of the sphere, and the sphere supremum is reduced to a countable dense set by continuity of
the internal metric on an open set `O` with `∂B₅(0) ⊆ O ⊆ C`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- On a Euclidean length metric, the supremum over the sphere `∂B_r(0)` of `y ↦ internalMetric D C x y` equals the
supremum over any countable subset `S` of the sphere that is dense in it, because the internal metric is continuous on an
open set `O ⊆ C` containing the sphere (`IsEuclideanLengthMetric.continuousOn_internalMetric_of_subset`). -/
theorem iSup_sphere_eq_of_dense {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {C O : Set ℂ} (hO : IsOpen O) (hOC : O ⊆ C) {r : ℝ} (hsph : sphere (0 : ℂ) r ⊆ O) (x : ℂ)
    {S : Set ℂ} (hSK : S ⊆ sphere (0 : ℂ) r) (hKS : sphere (0 : ℂ) r ⊆ closure S) :
    (⨆ y ∈ sphere (0 : ℂ) r, internalMetric D C x y) = ⨆ y ∈ S, internalMetric D C x y :=
  iSup_eq_iSup_of_dense_of_continuousOn hO hsph hSK hKS (hD.continuousOn_internalMetric_of_subset hO hOC x)

/-- Coordinate 0 of `pinchScalars` as a field functional (NEW step N1 of the plan, now proved). For a closed set
`C ∋ 0` and an open set `O` with `∂B₅(0) ⊆ O ⊆ C`, there is a measurable functional `Φ` of the field whose value at the
shifted field `addFunPairing (hC ω) g` is, almost surely, the supremum over `∂B₅(0)` of the internal metric of `C` of the
shifted metric, for every continuous `g` whose shifted metric is almost surely Euclidean. -/
theorem corridorInternalSup_decoder (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ ξ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (C O : Set ℂ) (hCc : IsClosed C) (h0C : (0 : ℂ) ∈ C)
    (hO : IsOpen O) (hOC : O ⊆ C) (hsph : sphere (0 : ℂ) 5 ⊆ O) :
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
        ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) =
          ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) C 0 y := by
  obtain ⟨S, hSsph, hSc, hSd⟩ := exists_countable_subset_sphere_dense (5 : ℝ)
  have : Countable S := hSc.to_subtype
  have hSC : ∀ y ∈ S, y ∈ C := fun y hy => hOC (hsph (hSsph hy))
  choose Φ hΦm hΦeq using fun p : ℕ × ℕ × S =>
    hdec γ ξ α₀ Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hα h𝔇
      (Metric.thickening (((p.2.1 : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((p.1 : ℝ) + 1)))
      isOpen_thickening 0 (p.2.2 : ℂ)
  refine ⟨fun T => ⨆ y : S, ⨅ n : ℕ, ⨆ k : ℕ, Φ (n, k, y) T, ?_, ?_⟩
  · exact Measurable.iSup fun y => Measurable.iInf fun n => Measurable.iSup fun k => hΦm (n, k, y)
  intro g hg hE
  have hall : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ × S, Φ p (addFunPairing (hC ω) g) =
      internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))
        (Metric.thickening (((p.2.1 : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((p.1 : ℝ) + 1))) 0 (p.2.2 : ℂ) :=
    ae_all_iff.2 fun p => hΦeq p g hg
  filter_upwards [hall, hE] with ω hω hEω
  have hK : ∀ y : S, internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) C 0 (y : ℂ) =
      ⨅ n : ℕ, ⨆ k : ℕ, Φ (n, k, y) (addFunPairing (hC ω) g) := by
    intro y
    rw [hK1 _ C hCc hEω h0C (hSC y y.2)]
    simp only [hω]
  rw [show (⨆ y : S, ⨅ n : ℕ, ⨆ k : ℕ, Φ (n, k, y) (addFunPairing (hC ω) g)) =
      ⨆ y : S, internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) C 0 (y : ℂ) from
      iSup_congr fun y => (hK y).symm]
  exact (iSup_subtype'' S _).trans (iSup_sphere_eq_of_dense hEω hO hOC hsph 0 hSsph hSd).symm

end HarmonicBalls
