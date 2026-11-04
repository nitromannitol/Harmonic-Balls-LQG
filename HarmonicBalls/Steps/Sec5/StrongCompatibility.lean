import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section3

/-!
# Lemma 5.8 from compatibility with general open sets

The comparison with a bounded open set `U` is isolated as the extension of
Lemma 3.5 to `U`. The paper asserts this extension at lines 1014–1025; its
proof for irregular domains is the unresolved issue GRAPH G9.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- General-domain extension of the cluster compatibility argument in Lemma
3.5, with a simultaneous event for all centres, times, and enclosing balls.
The open set `U` is fixed before the event, as in Lemma 5.8. -/
def ClusterGeneralDomainCompatibilityStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → U ⊆ ball (0 : ℂ) r → ∀ z ∈ U, ∀ t : ℝ, 0 < t →
      (closure (cluster (μ ω) r z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U) →
      cluster (μ ω) r z t = clusterOn (μ ω) U z t

/-- The closure of an open set equals the closure of its regularization. -/
theorem closure_regularizedCluster_eq_of_isOpen {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) :
    closure (regularizedCluster μ r z t) = closure (cluster μ r z t) := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact hopen.subset_interior_iff.2 subset_closure

/-- Lemma 5.8 from Lemma 3.2 and the general-domain compatibility step. -/
theorem clusterStrongCompatibility_of_steps (h32 : ClusterOpenLaplacianStmt.{u})
    (hcompat : ClusterGeneralDomainCompatibilityStep.{u}) : ClusterStrongCompatibilityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λhat hΛhat U hU hUbound
  filter_upwards [hΛhat, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hcompat γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ U hU hUbound] with ω hΛ hopen hcompare
  intro t ht z hz hcase
  obtain ⟨r₁, hr₁⟩ := (hUbound.subset_ball (0 : ℂ))
  obtain ⟨r₂, hr₂⟩ := (((hΛ z).1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]
    linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λhat ω z t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hzball : z ∈ ball (0 : ℂ) r := hUr hz
  have heq := (hΛ z).2.2 t ht r hr hΛr r le_rfl
  have hcl : closure (Λhat ω z t) = closure (cluster (μ ω) r z t) := by
    rw [heq]
    exact closure_regularizedCluster_eq_of_isOpen (hopen t r ht hr z hzball).1
  have hcase' : closure (cluster (μ ω) r z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U := by
    simpa only [← hcl] using hcase
  rw [hcl, hcompare r hr hUr z hz t ht hcase']

end HarmonicBalls
