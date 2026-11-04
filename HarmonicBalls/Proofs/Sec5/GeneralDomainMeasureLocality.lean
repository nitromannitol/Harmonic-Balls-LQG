import HarmonicBalls.Steps.Sec1.Locality
import HarmonicBalls.Proofs.Sec2.LQGLimitLocality

/-! # Dependence of the general-domain obstacle on the restricted measure -/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- A distributional Laplacian inequality on a measurable domain depends only
on the restriction of its measure to that domain. -/
theorem laplacianLE_iff_of_restrict_eq {U : Set ℂ} (hU : MeasurableSet U)
    {μ ν : Measure ℂ} (hμν : μ.restrict U = ν.restrict U) (w : ℂ → ℝ) :
    LaplacianLE w μ U ↔ LaplacianLE w ν U := by
  have htest : ∀ φ : ℂ → ℝ, IsTestFunction U φ →
      (Integrable φ μ ↔ Integrable φ ν) ∧ (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν := by
    intro φ hφ
    have hs : Function.support φ ⊆ U := (subset_tsupport φ).trans hφ.2.2
    have hi : Integrable φ μ ↔ Integrable φ ν := by
      rw [← integrableOn_iff_integrable_of_support_subset hs,
        ← integrableOn_iff_integrable_of_support_subset hs]
      change Integrable φ (μ.restrict U) ↔ Integrable φ (ν.restrict U)
      rw [hμν]
    have hind : U.indicator φ = φ := by
      funext x
      by_cases hx : x ∈ U
      · simp [hx]
      · have hzero : φ x = 0 := by
          by_contra hne
          exact hx (hs (Function.mem_support.mpr hne))
        simp [hx, hzero]
    have heq : (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν := by
      calc
        (∫ x, φ x ∂μ) = ∫ x in U, φ x ∂μ := by rw [← integral_indicator hU, hind]
        _ = ∫ x in U, φ x ∂ν := by rw [hμν]
        _ = ∫ x, φ x ∂ν := by rw [← integral_indicator hU, hind]
    exact ⟨hi, heq⟩
  constructor <;> rintro ⟨hloc, hineq⟩ <;> refine ⟨hloc, ?_⟩
  · intro φ hφ hnn hint
    have h := hineq φ hφ hnn ((htest φ hφ).1.mpr hint)
    rwa [(htest φ hφ).2] at h
  · intro φ hφ hnn hint
    have h := hineq φ hφ hnn ((htest φ hφ).1.mp hint)
    rwa [← (htest φ hφ).2] at h

/-- General-domain supersolutions depend only on the measure inside the domain. -/
theorem supersolutionsOn_eq_of_restrict_eq {U : Set ℂ} (hU : MeasurableSet U)
    {μ ν : Measure ℂ} (hμν : μ.restrict U = ν.restrict U) (z : ℂ) (t : ℝ) :
    supersolutionsOn μ U z t = supersolutionsOn ν U z t := by
  ext w
  simp only [supersolutionsOn, mem_ofPred_eq, laplacianLE_iff_of_restrict_eq hU hμν w]

/-- The general-domain obstacle cluster is unchanged when the measure is
changed outside the domain. -/
theorem clusterOn_eq_of_restrict_eq {U : Set ℂ} (hU : MeasurableSet U)
    {μ ν : Measure ℂ} (hμν : μ.restrict U = ν.restrict U) (z : ℂ) (t : ℝ) :
    clusterOn μ U z t = clusterOn ν U z t := by
  have heq := supersolutionsOn_eq_of_restrict_eq hU hμν z t
  simp only [clusterOn, leastSupersolutionOn, heq]

/-- In particular, the obstacle cluster agrees with that constructed from the
restricted measure itself. -/
theorem clusterOn_restrict (μ : Measure ℂ) {U : Set ℂ} (hU : MeasurableSet U)
    (z : ℂ) (t : ℝ) : clusterOn (μ.restrict U) U z t = clusterOn μ U z t := by
  apply clusterOn_eq_of_restrict_eq hU
  rw [Measure.restrict_restrict hU, inter_self]

/-- Two LQG limits whose circle averages agree locally at sufficiently small
scales produce identical obstacle clusters on the domain. -/
theorem IsLQGLimit.clusterOn_eq {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hν : IsLQGLimit γ hε' ν)
    {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    (z : ℂ) (t : ℝ) : clusterOn μ U z t = clusterOn ν U z t :=
  clusterOn_eq_of_restrict_eq hU.measurableSet (hμ.restrict_eq hν hU hloc) z t

end HarmonicBalls
