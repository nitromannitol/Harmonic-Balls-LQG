import HarmonicBalls.Proofs.Sec8.GoodRadiusVersions
import HarmonicBalls.Proofs.Sec8.CountableCompactObstacles
import HarmonicBalls.Proofs.Sec8.PointPolarityApproximation
import HarmonicBalls.Proofs.Sec8.BallMassCountable
import Mathlib.MeasureTheory.Measure.Count

/-! # Borel versions on classes of measures

A counting measure on the class transfers almost-everywhere versions to a
single Borel set agreeing with the event on every measure in the class.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

open MarkovProcess in
/-- A single Borel set represents the very-good-annulus event at the origin
on any class of atomless measures whose relevant annuli have finite mass and
positive mass threshold. Point avoidance is an explicit hypothesis. -/
theorem exists_measurable_isVeryGoodAnnulus_on_class
    (S : Set (Measure ℂ)) (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hreg : ∀ ν ∈ S, (∀ x : ℂ, ν {x} = 0) ∧
      ∀ (n : ℕ) (j k : ℤ) (l : ℕ),
        let r := ρ * (7 : ℝ)⁻¹ ^ l
        let z := (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
        ν (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
          0 < ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ ν ∈ S,
      (ν ∈ G ↔ IsVeryGoodAnnulus ν βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃) := by
  let Ω := {ν : Measure ℂ // ν ∈ S}
  let μ : Ω → Measure ℂ := Subtype.val
  have hμ : Measurable μ := measurable_subtype_coe
  let P : Measure Ω := Measure.count
  have hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b) := by
    intro n j k l
    let r := ρ * (7 : ℝ)⁻¹ ^ l
    let z := (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
    have hr : 0 < r := mul_pos hρ (pow_pos (by norm_num) l)
    obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_on_atomless r hr z a b
      (annulus_smallBallHitting_of_ae_point_avoidance r hr z
        (by intro u _ x _ hxu; exact hpolar u x hxu))
    refine ⟨μ ⁻¹' G, hG.preimage hμ, Filter.Eventually.of_forall ?_⟩
    intro ω
    have hω := hreg ω.1 ω.2
    exact hrep (μ ω) ⟨hω.1⟩ (hω.2 n j k l).1 (hω.2 n j k l).2
  obtain ⟨A, hA, hrep⟩ := exists_measurable_isVeryGoodAnnulus_version P μ βminus ρ hρ 0 N₀
    a b C₁m C₁p C₂m C₂p C₃
    ((measurable_annulusBallMassSize_ratio βminus ρ 0 hρ).comp hμ).aemeasurable
    ((measurable_annulusGreenPotentialRatio_zero ρ).comp hμ).aemeasurable hgood
  obtain ⟨G, hG, hGA⟩ := MeasurableSpace.measurableSet_comap.mp hA
  refine ⟨G, hG, ?_⟩
  intro ν hν
  have h := Measure.ae_count_iff.mp hrep ⟨ν, hν⟩
  simpa only [← hGA, mem_preimage, μ] using h

open MarkovProcess in
/-- The Borel representative applies simultaneously to every locally finite,
atomless, full-support measure when the mass parameter is positive. -/
theorem exists_measurable_isVeryGoodAnnulus_on_fullSupport
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ (ν : Measure ℂ),
      (∀ x : ℂ, ν {x} = 0) → IsLocallyFiniteMeasure ν →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U) →
      (ν ∈ G ↔ IsVeryGoodAnnulus ν βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃) := by
  let S : Set (Measure ℂ) := {ν | (∀ x : ℂ, ν {x} = 0) ∧ IsLocallyFiniteMeasure ν ∧
    ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U}
  have hreg : ∀ ν ∈ S, (∀ x : ℂ, ν {x} = 0) ∧
      ∀ (n : ℕ) (j k : ℤ) (l : ℕ),
        let r := ρ * (7 : ℝ)⁻¹ ^ l
        let z := (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
        ν (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
          0 < ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r)) := by
    intro ν hν
    refine ⟨hν.1, ?_⟩
    let : IsLocallyFiniteMeasure ν := hν.2.1
    intro n j k l
    let r := ρ * (7 : ℝ)⁻¹ ^ l
    let z := (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
    have hr : 0 < r := mul_pos hρ (pow_pos (by norm_num) l)
    have hnonempty : (annulus z (3 * r) (5 * r)).Nonempty := by
      refine ⟨z + (((4 * r : ℝ) : ℂ)), ?_⟩
      have hd : dist (z + (((4 * r : ℝ) : ℂ))) z = 4 * r := by
        simp [dist_eq_norm, hr.le]
      change dist (z + (((4 * r : ℝ) : ℂ))) z < 5 * r ∧
        ¬ dist (z + (((4 * r : ℝ) : ℂ))) z ≤ 3 * r
      rw [hd]
      constructor <;> linarith
    have hpos := hν.2.2 _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty
    exact ⟨ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset),
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' hpos.ne'⟩
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isVeryGoodAnnulus_on_class S βminus ρ hρ N₀
    a b C₁m C₁p C₂m C₂p C₃ hreg hpolar
  exact ⟨G, hG, fun ν hν hloc hfull => hrep ν ⟨hν, hloc, hfull⟩⟩

end HarmonicBalls
