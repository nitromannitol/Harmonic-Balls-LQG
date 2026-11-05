import HarmonicBalls.Proofs.Sec5.LargerDiscMassEquivalence
import HarmonicBalls.Proofs.Sec6.WholePlaneNonatomic

/-! # Larger-disc comparison for a logarithmically singular field -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- The deterministic unit circle is null for the LQG measure with a
logarithmic singularity at zero. Existence of the whole-plane measure is an
explicit input; Weyl scaling transfers nullity away from the singularity. -/
theorem ae_singular_lqg_unit_sphere_eq_zero
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hE : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, μ ω (sphere (0 : ℂ) 1) = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE hGFF hγ hγ2 hQ
  have hSW := singularWeightStep_of_weyl
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
  have hweight := hSW γ α₀ hγ hγ2 hα Ω P hC hcirc μ μ₀ hGFF hμ hμ₀
  filter_upwards [hweight, Section6.ae_lqg_sphere_eq_zero_of_translation hGFF hμ₀ hAff 0 1]
    with ω hweight hnull
  have heq := congrArg (fun ν : Measure ℂ => ν (sphere (0 : ℂ) 1)) hweight
  rw [Measure.restrict_apply isClosed_sphere.measurableSet,
    Measure.restrict_apply isClosed_sphere.measurableSet] at heq
  have hs : sphere (0 : ℂ) 1 ∩ ({0} : Set ℂ)ᶜ = sphere (0 : ℂ) 1 := by
    apply inter_eq_left.mpr
    intro x hx hx0
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    simp only [mem_singleton_iff] at hx0
    rw [hx0] at hxnorm
    norm_num at hxnorm
  rw [hs] at heq
  rw [heq]
  exact (withDensity_absolutelyContinuous (μ₀ ω) _) hnull

/-- Under the displayed inputs, larger-disc closure equality is equivalent to
full mass, simultaneously for all centres, positive times and larger radii. -/
theorem ae_singular_larger_disc_closure_eq_iff_mass_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hE : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ R : ℝ, 1 < R →
      (closure (cluster (μ ω) 1 z t) = closure (cluster (μ ω) R z t) ↔
        μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t) := by
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps (clusterOpenLaplacian_proved hI2)
      h611 h82 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_singular_lqg_unit_sphere_eq_zero hE hAff hγ hγ2 hα hGFF hμ]
      with ω hopen hmass hfull hinterior hsphere
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro z hz t ht R hR
  have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball hR.le hz
  have hopen1 := (hopen t 1 ht zero_lt_one z hz).1
  have hopenR := (hopen t R ht (lt_trans zero_lt_one hR) z hzR).1
  have hfront := measure_frontier_cluster_eq_zero_of_inter_ball_and_sphere
    (μ ω) z t (hinterior t ht z hz) hsphere
  constructor
  · intro heq
    apply cluster_mass_eq_of_larger_disc_closure_eq hR hz ht.le hopen1 hopenR hfront heq
    apply (hmass R t (lt_trans zero_lt_one hR) ht z hzR).2.2
    rw [← heq]
    exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
      isClosed_closedBall).trans (closedBall_subset_ball hR)
  · intro h
    exact cluster_closure_eq_larger_disc_of_mass_eq hR hz ht.le hopen1 hopenR h
      (hmass R t (lt_trans zero_lt_one hR) ht z hzR).1

end HarmonicBalls
