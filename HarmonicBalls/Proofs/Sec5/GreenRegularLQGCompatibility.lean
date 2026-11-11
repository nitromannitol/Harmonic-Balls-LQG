import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility
import HarmonicBalls.Proofs.Sec5.GeneralDomainClusterOpen
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-! # LQG compatibility on Green-regular pole components

This conditional result uses I2 and the proved Lemma 3.2, as well as the
potential-theoretic infrastructure of Leonardo Bonanno. It does not establish
Lemma 5.8 for arbitrary irregular domains. The Green boundary condition is
required for every pole component; admissibility is derived, not assumed.
The componentwise comparison after an empty deletion needs disc-cluster
openness only for discs containing the pole, as supplied by Lemma 3.2.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

universe u

/-- Strong compatibility on a deterministic bounded open domain whose pole
components have vanishing Green boundary limits. The event is simultaneous in
all positive times and all poles in the domain. -/
theorem ae_strongCompatibility_of_greenRegular_components
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ Λhat : Ω → ℂ → ℝ → Set ℂ,
      (∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) →
    ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
      (∀ z ∈ U, ∀ y ∈ closure (connectedComponentIn U z),
        y ∉ connectedComponentIn U z →
        Tendsto (greenFunction (connectedComponentIn U z) z)
          (𝓝[connectedComponentIn U z] y) (𝓝 0)) →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ U,
      (closure (Λhat ω z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U) →
        closure (Λhat ω z t) = closure (clusterOn (μ ω) U z t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λhat hΛ U hU hUb hboundary
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, hΛ, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω hω hfamily hopen
  intro t ht z hz hcl
  obtain ⟨R, hUR⟩ := hUb.subset_ball (0 : ℂ)
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (mem_ball.mp (hUR hz))
  have hv := leastSupersolutionOn_mem_of_greenRegular hω.1 hR (hω.2 R hR)
    hU.connectedComponentIn ((connectedComponentIn_subset U z).trans hUR)
    (mem_connectedComponentIn hz) ht (hboundary z hz)
  have hopenU := isOpen_clusterOn_of_leastSupersolutionOn_mem hU.connectedComponentIn
    (hUb.subset (connectedComponentIn_subset U z)) (mem_connectedComponentIn hz) ht hv
  have hresult := regularizedFamily_strongCompatibility_of_countable_on_component
    (K := ∅) hω.1 hω.2 hU (by simpa using hU) hUb ht
    (by simpa using hz) (by simp) hv hopenU (hboundary z hz) (hfamily z)
    (fun r hr hzr => (hopen t r ht hr z hzr).1) (by simpa using hcl)
  simpa using hresult

end HarmonicBalls
