import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileApprox
import HarmonicBalls.Proofs.Sec11.ClosureScales.CompactTestDensity
import HarmonicBalls.Proofs.Sec11.ClosureScales.CountableTestCauchy

/-!
# Lemma l:r6-transfer, step 3d (part 1): the good set of canonical profiles

Source: `notes/sec11-proof/sec11-proof-r7.tex`, Lemma `l:r6-transfer`, measure part (lines 560-600). The LQG measure is
the vague limit of the approximations along the dyadic scales, and vague convergence is read off the countable family
`testFamily` (`CompactTestDensity.lean`). The good set `goodProfiles γ α₀` consists of the canonical profiles along which
the approximations have masses bounded on each closed ball and converge against the countable family. This file proves:
the good set is measurable (countably many measurable conditions), and on the good set the approximations converge
against every compactly supported continuous test (`CountableTestCauchy.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric

/-- The countable determining family of `exists_countable_compactSupport_approx`, fixed by choice. -/
noncomputable def testFamily : Set (ℂ → ℝ) :=
  Classical.choose exists_countable_compactSupport_approx

theorem testFamily_countable : testFamily.Countable :=
  (Classical.choose_spec exists_countable_compactSupport_approx).1

theorem testFamily_spec : ∀ g ∈ testFamily, Continuous g ∧ HasCompactSupport g :=
  (Classical.choose_spec exists_countable_compactSupport_approx).2.1

theorem testFamily_approx : ∀ (ψ : ℂ → ℝ), Continuous ψ → ∀ R : ℕ,
    (∀ z : ℂ, (R : ℝ) < ‖z‖ → ψ z = 0) → ∀ ε : ℝ, 0 < ε → ∃ g ∈ testFamily,
      (∀ z : ℂ, (R : ℝ) + 1 < ‖z‖ → g z = 0) ∧ ∀ z : ℂ, ‖z‖ ≤ (R : ℝ) + 1 → |g z - ψ z| < ε :=
  (Classical.choose_spec exists_countable_compactSupport_approx).2.2

/-- **The good set** (Lemma l:r6-transfer, measure part). A canonical profile `f` is good when the LQG approximations
`profileApprox γ α₀ n f` have masses bounded on each closed ball `closedBall 0 (R + 1)` along the dyadic scales, and their
integrals against the countable family `testFamily` are Cauchy. -/
def goodProfiles (γ α₀ : ℝ) : Set CanonicalProfile :=
  {f | (∀ R : ℕ, ⨆ n : ℕ, profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1)) < ⊤) ∧
    ∀ g ∈ testFamily, CauchySeq (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f))}

/-- The mass condition on a closed ball is a measurable condition on the profile. -/
theorem measurableSet_profileMass (γ α₀ : ℝ) {B : Set ℂ} (hB : MeasurableSet B) :
    MeasurableSet {f : CanonicalProfile | ⨆ n : ℕ, profileApprox γ α₀ n f B < ⊤} := by
  refine measurableSet_lt (Measurable.iSup fun n : ℕ => ?_) measurable_const
  exact (Measure.measurable_coe hB).comp (measurable_profileApprox γ α₀ n)

/-- The Cauchy condition on the integrals against a fixed test of the family is a measurable condition. -/
theorem measurableSet_profileCauchy (γ α₀ : ℝ) {g : ℂ → ℝ} (hg : g ∈ testFamily) :
    MeasurableSet {f : CanonicalProfile | CauchySeq (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f))} := by
  obtain ⟨hgc, hgs⟩ := testFamily_spec g hg
  have hset : {f : CanonicalProfile | CauchySeq (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f))} =
      {f : CanonicalProfile | ∃ c, Tendsto (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f)) atTop (𝓝 c)} := by
    ext f
    constructor
    · intro h
      exact cauchySeq_tendsto_of_complete h
    · rintro ⟨c, hc⟩
      exact hc.cauchySeq
  rw [hset]
  exact measurableSet_exists_tendsto (l := atTop)
    (f := fun (n : ℕ) (f : CanonicalProfile) => ∫ z, g z ∂(profileApprox γ α₀ n f))
    fun n => measurable_integral_profileApprox γ α₀ n hgc hgs

/-- **The good set is measurable.** It is a countable intersection of measurable conditions. -/
theorem measurableSet_goodProfiles (γ α₀ : ℝ) : MeasurableSet (goodProfiles γ α₀) := by
  have h1 : MeasurableSet (⋂ R : ℕ, {f : CanonicalProfile | ⨆ n : ℕ,
      profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1)) < ⊤}) :=
    MeasurableSet.iInter fun R : ℕ => measurableSet_profileMass γ α₀ measurableSet_closedBall
  have h2 : MeasurableSet (⋂ g ∈ testFamily, {f : CanonicalProfile |
      CauchySeq (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f))}) :=
    MeasurableSet.biInter testFamily_countable fun g hg => measurableSet_profileCauchy γ α₀ hg
  have hset : goodProfiles γ α₀ = (⋂ R : ℕ, {f : CanonicalProfile | ⨆ n : ℕ,
      profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1)) < ⊤}) ∩
      (⋂ g ∈ testFamily, {f : CanonicalProfile |
        CauchySeq (fun n : ℕ => ∫ z, g z ∂(profileApprox γ α₀ n f))}) := by
    ext f
    simp only [goodProfiles, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [hset]
  exact h1.inter h2

/-- **Vague convergence on the good set.** On the good set, the LQG approximations of the profile integrate every
compactly supported continuous test to a limit. This is the convergence used to define the limit functional of step 3d
(part 2), and it follows from `exists_tendsto_integral_of_countable_approx`. -/
theorem exists_tendsto_profile_integral_of_good {γ α₀ : ℝ} {f : CanonicalProfile}
    (hf : f ∈ goodProfiles γ α₀) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => ∫ z, ψ z ∂(profileApprox γ α₀ n f)) atTop (𝓝 L) := by
  simp only [goodProfiles, Set.mem_ofPred_eq] at hf
  obtain ⟨hmass, hcauchy⟩ := hf
  refine exists_tendsto_integral_of_countable_approx
    (fun n => isLocallyFiniteMeasure_profileApprox γ α₀ n f) testFamily_spec testFamily_approx ?_ ?_ ψ hψ hcs
  · intro R
    refine ⟨(⨆ n : ℕ, profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1))).toReal, fun n => ?_⟩
    exact ENNReal.toReal_mono (ne_of_lt (hmass R))
      (le_iSup (fun m : ℕ => profileApprox γ α₀ m f (closedBall (0 : ℂ) ((R : ℝ) + 1))) n)
  · intro g hg
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hcauchy g hg)
    exact ⟨L, hL⟩

end HarmonicBalls
