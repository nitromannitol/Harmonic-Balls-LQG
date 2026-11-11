import HarmonicBalls.Defs.StrongMetricSpaces

/-!
# Testwise versions need not be distribution-valued

An uncountable family of null exceptional sets can destroy samplewise linearity.
This isolates a regularity issue in the pairing-only GFF interface.
-/

namespace HarmonicBalls

open MeasureTheory TopologicalSpace
open scoped Distributions

/-- A spike indexed by a real parameter and a fixed nonzero test function. -/
noncomputable def pairingVersionSpike
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (t : ℝ) (φ : ℂ → ℝ) : ℝ := by
  classical
  exact if φ = (t • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) then 1 else 0

/-- A fixed nonzero test function gives distinct scalar multiples as functions. -/
theorem testFunction_smul_injective
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (h₀ : test₀ ≠ 0) :
    Function.Injective (fun t : ℝ => ((t • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ)) := by
  intro a b hab
  apply smul_left_injective ℝ h₀
  ext z
  exact congrFun hab z

/-- For each fixed test, the spike vanishes almost everywhere in its parameter. -/
theorem pairingVersionSpike_ae_zero
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (h₀ : test₀ ≠ 0) (φ : ℂ → ℝ) :
    ∀ᵐ t ∂volume, pairingVersionSpike test₀ t φ = 0 := by
  classical
  by_cases h : ∃ t : ℝ, φ = ((t • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ)
  · obtain ⟨t, ht⟩ := h
    filter_upwards [Measure.ae_ne volume t] with s hs
    simp only [pairingVersionSpike]
    have hn : φ ≠ ((s • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ) := by
      intro heq
      apply hs
      exact (testFunction_smul_injective test₀ h₀) (heq.symm.trans ht)
    simp only [hn, ↓reduceIte]
  · filter_upwards with t
    simp only [pairingVersionSpike]
    have hn : φ ≠ ((t • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ) :=
      fun heq => h ⟨t, heq⟩
    simp only [hn, ↓reduceIte]

/-- No sample of the spike is the pairing of a distribution. -/
theorem pairingVersionSpike_not_represents
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (h₀ : test₀ ≠ 0) (t : ℝ) :
    ¬ ∃ distribution : PlaneDistribution,
      RepresentsPlaneDistribution (pairingVersionSpike test₀ t) distribution := by
  classical
  rintro ⟨distribution, hrep⟩
  by_cases ht : t = 0
  · subst t
    have hz := hrep 0
    simp [pairingVersionSpike] at hz
  · have h₁ := hrep (t • test₀)
    have h₂ := hrep ((2 * t) • test₀)
    have hne : (((2 * t) • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ) ≠
        ((t • test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : ℂ → ℝ) := by
      intro heq
      have := (testFunction_smul_injective test₀ h₀) heq
      apply ht
      linarith
    have hlin : distribution ((2 * t) • test₀) = 2 * distribution (t • test₀) := by
      simp [mul_smul]
    simp only [pairingVersionSpike, ↓reduceIte] at h₁
    simp only [pairingVersionSpike] at h₂
    simp only [hne, ↓reduceIte] at h₂
    linarith

/-- Testwise the spiked version agrees almost surely with the original field. -/
theorem pairingVersionSpike_add_ae_eq
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (h₀ : test₀ ≠ 0)
    (field : ℝ → PlaneDistribution) (φ : ℂ → ℝ) :
    ∀ᵐ t ∂volume, planeDistributionPairing (field t) φ + pairingVersionSpike test₀ t φ =
      planeDistributionPairing (field t) φ := by
  filter_upwards [pairingVersionSpike_ae_zero test₀ h₀ φ] with t ht
  simp only [ht, add_zero]

/-- Adding the spike destroys samplewise distribution representation. -/
theorem pairingVersionSpike_add_not_represents
    (test₀ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (h₀ : test₀ ≠ 0)
    (field : ℝ → PlaneDistribution) (t : ℝ) :
    ¬ ∃ distribution : PlaneDistribution, RepresentsPlaneDistribution
      (fun φ => planeDistributionPairing (field t) φ + pairingVersionSpike test₀ t φ) distribution := by
  rintro ⟨distribution, hrep⟩
  apply pairingVersionSpike_not_represents test₀ h₀ t
  refine ⟨distribution - field t, ?_⟩
  intro test
  have h := hrep test
  simp only [planeDistributionPairing_apply] at h
  simp only [sub_apply]
  linarith

/-- A concrete nonzero test function exists on the plane. -/
theorem exists_nonzero_plane_testFunction :
    ∃ test : TestFunction (⊤ : Opens ℂ) ℝ ⊤, test ≠ 0 := by
  let bump : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  let test : TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
    ⟨bump, bump.contDiff, bump.hasCompactSupport, Set.subset_univ _⟩
  refine ⟨test, ?_⟩
  intro h
  have hz := congrArg (fun ψ : TestFunction (⊤ : Opens ℂ) ℝ ⊤ => ψ 0) h
  have hb : bump (0 : ℂ) = 1 := bump.one_of_mem_closedBall (by simp [bump])
  change bump 0 = 0 at hz
  linarith


end HarmonicBalls
