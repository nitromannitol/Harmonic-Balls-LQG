import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly
import HarmonicBalls.Proofs.Sec5.FamilyUniqueness

/-! # Conditional Section 5 composition checks

These examples expand each top-level logical premise and the conclusions. The
imported Section 8 proofs use Leonardo Bonanno's `LatticeProb.Prob.Birkhoff`
formalization. They establish conditional composition, not source closure.
-/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter
universe u

example
    (hI2 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
    βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧ μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    (h32 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    IsOpen (cluster (μ ω) r z t) ∧ IsConnected (cluster (μ ω) r z t) ∧
    ∃ ν : Measure ℂ, IsLocallyFiniteMeasure ν ∧
      ν.restrict (ball 0 r) ≪ (μ ω).restrict (ball 0 r) ∧
      ν.restrict (ball 0 r) ≤ (μ ω).restrict (ball 0 r) ∧
      HasLaplacian (leastSupersolution (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t))) 0
        (ball 0 r) ∧
      HasLaplacian (odometer (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 r))
    (h33 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t₁ t₂ r : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    cluster (μ ω) r z t₁ ⊆ cluster (μ ω) r z t₂)
    (h35 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ R : ℝ, 0 < R →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ R → ∀ z ∈ ball (0 : ℂ) s₁,
    ∀ s₂ ∈ Set.Icc s₁ R, closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
      ∀ s ∈ Set.Icc s₁ R, cluster (μ ω) s z t = cluster (μ ω) s₂ z t)
    (h43 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ r t : ℝ, 0 < r → 0 < t → ∀ z ∈ ball (0 : ℂ) r,
    closure (cluster (μ ω) r z t) ⊆ ball 0 r → μ ω (frontier (cluster (μ ω) r z t)) = 0 →
      IsSubharmonicBall (μ ω) (cluster (μ ω) r z t) z)
    (h53 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    μ ω (frontier (cluster (μ ω) 1 z t)) = 0)
    (h54 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∃ T : ℝ, 0 < T ∧
    (∀ t ∈ Ioo 0 T, closure (regularizedCluster (μ ω) 1 z t) ⊆ ball 0 1) ∧
    SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z T ∧
    (closure (regularizedCluster (μ ω) 1 z T) ∩ sphere (0 : ℂ) 1).Nonempty)
    (h71 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ r ∈ Ioo (0 : ℝ) 1,
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)}))
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsWholePlaneGFF P
        (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b))
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsLQGLimit γ (fun ε z => fieldCircleAverage α₀ (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
        ((μ ω).map fun x => (x - b) / a))
    :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ Λ : ℝ → Set ℂ, (SatisfiesHarmonicBallConditions (μ ω) Λ z ∧
      (∀ t : ℝ, 0 < t → IsSubharmonicBall (μ ω) (Λ t) z) ∧
      ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r →
        Λ t = interior (closure (cluster (μ ω) r z t))) := by
  exact existenceHarmonicBalls_of_volumeGrowth hI2 h32 h33 h35 h43 h53 h54 h71 hAff hCC

example
    (hentry :   ∀ (μ : Measure ℂ), μ.IsOpenPosMeasure → ∀ (Λ A : ℝ → Set ℂ) (z : ℂ),
    IsRegularizedClusterFamily μ Λ z → IsHarmonicBallFamily μ A z →
    (∀ s : ℝ, 0 < s → frontier (A s) ⊆ closure (Λ s)) →
    ∀ t : ℝ, 0 < t → ∀ x : ℂ, ∀ r : ℝ, 0 < r →
      ball x r ⊆ (closure (Λ t))ᶜ → Disjoint (ball x r) (A t))
    (h93 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, (SatisfiesHarmonicBallConditions (μ ω) (Λhat ω z) z ∧ (∀ t : ℝ, 0 < t → IsSubharmonicBall (μ ω) (Λhat ω z t) z) ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λhat ω z t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r → Λhat ω z t = interior (closure (cluster (μ ω) r z t)))) →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (R t : ℝ), z ∈ ball (0 : ℂ) R → closure A ⊆ ball (0 : ℂ) R →
    IsHarmonicBallGen (μ ω) A z → 0 < t → μ ω A = ENNReal.ofReal t →
    frontier A ⊆ closure (Λhat ω z t))
    (h94 :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ X Y : Set ℂ, IsOpen X → IsOpen Y → IsRegularOpen X → IsRegularOpen Y →
    μ ω (X \ Y) = 0 → μ ω (Y \ X) = 0 → X = Y)
    (hfull :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    :   ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, (SatisfiesHarmonicBallConditions (μ ω) (Λhat ω z) z ∧ (∀ t : ℝ, 0 < t → IsSubharmonicBall (μ ω) (Λhat ω z t) z) ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λhat ω z t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r → Λhat ω z t = interior (closure (cluster (μ ω) r z t)))) →
  ∀ᵐ ω ∂P, ∀ (z : ℂ) (A : ℝ → Set ℂ), ((∀ t : ℝ, 0 < t → IsHarmonicBallGen (μ ω) (A t) z) ∧ SatisfiesHarmonicBallConditions (μ ω) A z) → EqOn A (Λhat ω z) (Ioi 0) := by
  exact uniquenessHarmonicBalls_of_steps hentry h93 h94 hfull

/- Direct composition tests: the no-entry producer is supplied, and 9.3,
9.4 and full support are each supplied from I2 without assuming 5.5 or 5.6. -/
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u})
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2 h53 h71 h72
    (fun P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC

example : HarmonicBallNoEntryStep := harmonicBallNoEntry

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_steps harmonicBallNoEntry
    (harmonicBallBoundarySubset_of_volumeGrowth hI2)
    (regularOpenEqOfAEEq_of_volumeGrowth hI2)
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2)

example {μ : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {z : ℂ}
    (h₁ : IsRegularizedClusterFamily μ Λ₁ z) (h₂ : IsRegularizedClusterFamily μ Λ₂ z) :
    EqOn Λ₁ Λ₂ (Ioi 0) := h₁.eqOn h₂

#print axioms existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates
#print axioms wholePlaneGFFAffineInvariance_proved
#print axioms existenceHarmonicBalls_of_volumeGrowth
#print axioms cofinalRegularizedClusterIntervals_of_volumeGrowth
#print axioms harmonicBallNoEntry
#print axioms uniquenessHarmonicBalls_of_steps
#print axioms harmonicBallBoundarySubset_of_volumeGrowth
#print axioms regularOpenEqOfAEEq_of_volumeGrowth
#print axioms IsRegularizedClusterFamily.eqOn

end HarmonicBalls
