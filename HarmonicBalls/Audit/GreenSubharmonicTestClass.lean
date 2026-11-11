import HarmonicBalls.Draft.Section4

/-! # Bounded-domain reduction for the subharmonic test class

This audit works with the frozen real-valued definitions. It separates a proved reduction
from the remaining potential-theoretic assertion that bounded-domain representatives exist.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

/-- The frozen test class with a bounded witness domain. -/
def boundedSubharmonicBallTestClass (Λ : Set ℂ) (z : ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (O K : Set ℂ) (ν₁ ν₂ : Measure ℂ) (q : ℂ → ℝ),
    IsOpen O ∧ Bornology.IsBounded O ∧ closure Λ ⊆ O ∧ IsCompact K ∧ K ⊆ O ∧
    IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ Kᶜ = 0 ∧ ν₂ Kᶜ = 0 ∧ ν₁ Λ = 0 ∧
    HarmonicOnNhd q O ∧ ν₂ {z} = 0 ∧ Integrable (greenFunction O z) ν₂ ∧
    f = q + greenPotential O ν₁ - greenPotential O ν₂}

/-- A bounded-domain witness is a witness for the frozen class. -/
theorem boundedSubharmonicBallTestClass_subset (Λ : Set ℂ) (z : ℂ) :
    boundedSubharmonicBallTestClass Λ z ⊆ subharmonicBallTestClass Λ z := by
  rintro f ⟨O, K, ν₁, ν₂, q, hO, _, hΛ, hK, hKO, hν₁, hν₂, h₁, h₂, hΛ₁, hq, hz, hi, hf⟩
  exact ⟨O, K, ν₁, ν₂, q, hO, hΛ, hK, hKO, hν₁, hν₂, h₁, h₂, hΛ₁, hq, hz, hi, hf⟩

/-- A harmonic test on an arbitrary open neighbourhood has a bounded witness if the
cluster is bounded. No change of its values is required. -/
theorem harmonic_mem_boundedSubharmonicBallTestClass {Λ O : Set ℂ} {z : ℂ} {q : ℂ → ℝ}
    (hΛ : Bornology.IsBounded Λ) (hO : IsOpen O) (hΛO : closure Λ ⊆ O)
    (hq : HarmonicOnNhd q O) : q ∈ boundedSubharmonicBallTestClass Λ z := by
  obtain ⟨R, hR⟩ := hΛ.closure.subset_ball (0 : ℂ)
  refine ⟨O ∩ ball 0 R, ∅, 0, 0, q, hO.inter isOpen_ball,
    isBounded_ball.subset inter_subset_right, subset_inter hΛO hR, isCompact_empty,
    empty_subset _, inferInstance, inferInstance, by simp, by simp, by simp,
    hq.mono inter_subset_left, by simp, by simp, ?_⟩
  simp

/-- Equality at the pole and almost everywhere for the restricted measure preserves both
integrability and the sub-mean inequality. -/
theorem hasSubMeanValueProperty_congr {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f g : ℂ → ℝ}
    (hz : f z = g z) (hae : f =ᵐ[μ.restrict Λ] g) :
    HasSubMeanValueProperty μ Λ z f ↔ HasSubMeanValueProperty μ Λ z g := by
  unfold HasSubMeanValueProperty IntegrableOn
  rw [integrable_congr hae, hz, integral_congr_ae hae]

/-- The exact remaining replacement obligation for one measure and one cluster. -/
def HasBoundedSubharmonicRepresentatives (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  ∀ f ∈ subharmonicBallTestClass Λ z, ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
    f z = g z ∧ f =ᵐ[μ.restrict Λ] g

/-- Under the explicitly stated representative obligation, checking bounded witnesses is
exactly as strong as checking every test in the frozen class. -/
theorem subMeanValue_all_iff_bounded_of_representatives {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (hrep : HasBoundedSubharmonicRepresentatives μ Λ z) :
    (∀ f ∈ subharmonicBallTestClass Λ z, HasSubMeanValueProperty μ Λ z f) ↔
      (∀ f ∈ boundedSubharmonicBallTestClass Λ z, HasSubMeanValueProperty μ Λ z f) := by
  constructor
  · intro h f hf
    exact h f (boundedSubharmonicBallTestClass_subset Λ z hf)
  · intro h f hf
    obtain ⟨g, hg, hz, hae⟩ := hrep f hf
    exact (hasSubMeanValueProperty_congr hz hae).2 (h g hg)

/-- At a centre in the cluster, the positive measure does not charge the centre. -/
theorem positiveMeasure_pole_null {Λ : Set ℂ} {z : ℂ} {ν₁ : Measure ℂ}
    (hz : z ∈ Λ) (hν : ν₁ Λ = 0) : ν₁ {z} = 0 :=
  measure_mono_null (singleton_subset_iff.2 hz) hν

/-- Bochner nonintegrability forces the frozen potential to its junk value. -/
theorem greenPotential_eq_zero_of_not_integrable (O : Set ℂ) (ν : Measure ℂ) (x : ℂ)
    (h : ¬ Integrable (greenFunction O x) ν) : greenPotential O ν x = 0 :=
  integral_undef h

/-- Real-valued kernel integrability alone does not rule out an atom at the pole. -/
theorem integrable_greenFunction_dirac_self (O : Set ℂ) (x : ℂ) :
    Integrable (greenFunction O x) (Measure.dirac x) :=
  integrable_dirac enorm_lt_top

/-- A point mass sees the real-valued diagonal convention, even on a bounded domain. -/
theorem greenPotential_dirac_self (O : Set ℂ) (x : ℂ) :
    greenPotential O (Measure.dirac x) x = 0 := by
  simp [greenPotential, integral_dirac, greenFunction_self]

end HarmonicBalls
