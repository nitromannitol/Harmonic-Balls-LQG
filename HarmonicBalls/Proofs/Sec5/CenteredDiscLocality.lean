import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Locality of harmonic balls in centred discs

Disc compatibility and local measurability of the disc obstacle give the
local containment event in centred discs. This does not assert the
corresponding arbitrary-open-domain result.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Compatibility of a regularized cluster family with centred disc clusters,
including both possible compact-containment hypotheses. -/
theorem ae_regularizedClusterFamily_centeredDisc_compatibility
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Λhat : Ω → ℂ → ℝ → Set ℂ)
    (hΛhat : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) r, ∀ t : ℝ, 0 < t →
      (closure (Λhat ω z t) ⊆ ball 0 r ∨
        closure (cluster (μ ω) r z t) ⊆ ball 0 r) →
      closure (Λhat ω z t) = closure (cluster (μ ω) r z t) := by
  have hcomp : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      ∀ s₁ : ℝ, s₁ ≤ (n : ℝ) + 1 → ∀ z ∈ ball (0 : ℂ) s₁,
      ∀ s₂ ∈ Icc s₁ ((n : ℝ) + 1), closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
        ∀ s ∈ Icc s₁ ((n : ℝ) + 1), cluster (μ ω) s z t = cluster (μ ω) s₂ z t := by
    intro n
    exact clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
      ((n : ℝ) + 1) (by positivity)
  filter_upwards [hΛhat, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ, ae_all_iff.mpr hcomp] with ω hΛ hopen hcompat
  intro r hr z hz t ht hcase
  obtain ⟨R, hR⟩ := (((hΛ z).1.isBounded t ht).closure).subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt (max R r)
  have hRn : R ≤ (n : ℝ) + 1 := by have := le_max_left R r; linarith
  have hrn : r ≤ (n : ℝ) + 1 := by have := le_max_right R r; linarith
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hΛn : closure (Λhat ω z t) ⊆ ball 0 ((n : ℝ) + 1) :=
    hR.trans (ball_subset_ball hRn)
  have hreg := (hΛ z).2.2 t ht ((n : ℝ) + 1) hnpos hΛn ((n : ℝ) + 1) le_rfl
  have hcl : closure (Λhat ω z t) = closure (cluster (μ ω) ((n : ℝ) + 1) z t) := by
    rw [hreg]
    exact closure_regularizedCluster_eq_of_isOpen
      (hopen t ((n : ℝ) + 1) ht hnpos z (ball_subset_ball hrn hz)).1
  rcases hcase with hlarge | hsmall
  · have heq := hcompat n t ht r hrn z hz ((n : ℝ) + 1) ⟨hrn, le_rfl⟩
      (hcl ▸ hlarge) r ⟨le_rfl, hrn⟩
    rw [hcl, heq]
  · have heq := hcompat n t ht r hrn z hz r ⟨le_rfl, hrn⟩ hsmall
      ((n : ℝ) + 1) ⟨hrn, le_rfl⟩
    rw [hcl, heq]

/-- The positive-time harmonic-ball containment event in a centred disc is
measurable from the field on that disc, up to a null set. -/
theorem exists_local_harmonicBall_centeredDisc_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (z : ℂ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) z)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 r)] E ∧
      {ω | closure (Λ ω t) ⊆ ball 0 r} =ᵐ[P] E := by
  classical
  by_cases hz : z ∈ ball (0 : ℂ) r
  · let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω x =>
      if h : ∃ A, IsRegularizedClusterFamily (μ ω) A x then Classical.choose h else fun _ => ∅
    have hhat : ∀ᵐ ω ∂P, ∀ x, IsRegularizedClusterFamily (μ ω) (Λhat ω x) x := by
      filter_upwards [h55 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
      intro x
      dsimp only [Λhat]
      simpa only [dite_eq_left (hω x)] using Classical.choose_spec (hω x)
    obtain ⟨E, hE, heq⟩ := exists_local_lqg_cluster_ball_containment
      hI2 hγ hγ2 hα hGFF hμ hloc hr hz ht
    refine ⟨E, hE, ?_⟩
    filter_upwards [hΛ, h56 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat,
      ae_regularizedClusterFamily_centeredDisc_compatibility hI2 hγ hγ2 hα hGFF hμ Λhat hhat,
      heq] with ω hA hunique hcompat hEω
    have hsame : Λ ω t = Λhat ω z t := hunique z (Λ ω) hA ht
    apply propext
    rw [hsame]
    have hc := hcompat r hr z hz t ht
    have hEω : closure (cluster (μ ω) r z t) ⊆ ball 0 r ↔ ω ∈ E := propext_iff.mp hEω
    constructor
    · intro h
      exact hEω.mp ((hc (Or.inl h)) ▸ h)
    · intro h
      have h' := hEω.mpr h
      exact (hc (Or.inr h')) ▸ h'
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigmaAlgebra α₀ hC (ball 0 r)), ?_⟩
    filter_upwards [hΛ] with ω hω
    apply propext
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hz (h (subset_closure (hω.2.mem t ht)))

end HarmonicBalls
