import HarmonicBalls.Proofs.Sec6.GreenMono
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import HarmonicBalls.Proofs.Sec6.PotentialRatioPositive

/-!
# Integrability of Green kernels on subdomains

Domain monotonicity and measurability transfer Green-kernel integrability from a bounded
ambient domain to an open subdomain, including points outside the subdomain and the
convention that the diagonal has value zero. This is useful for annuli inside balls.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

/-- Domain monotonicity for Green functions holds for all pairs, including the diagonal
and points outside the smaller domain. -/
theorem greenFunction_le_of_subset {O O' : Set ℂ} (hsub : O ⊆ O')
    (hbounded : Bornology.IsBounded O') (x y : ℂ) :
    greenFunction O x y ≤ greenFunction O' x y := by
  by_cases hx : x ∈ O
  · by_cases hy : y ∈ O
    · by_cases hxy : x = y
      · subst y
        simp only [greenFunction_self, le_refl]
      · exact greenFunction_mono hsub hbounded hx hy hxy
    · rw [greenFunction_of_notMem_right hy]
      exact greenFunction_nonneg hbounded x y
  · rw [greenFunction_of_notMem_left hx]
    exact greenFunction_nonneg hbounded x y

/-- Integrability of a Green kernel on a bounded ambient domain implies integrability
on each open subdomain. -/
theorem integrable_greenFunction_of_subset {O O' : Set ℂ} (hopen : IsOpen O)
    (hsub : O ⊆ O') (hbounded : Bornology.IsBounded O') (μ : Measure ℂ) (x : ℂ)
    (hint : Integrable (greenFunction O' x) μ) :
    Integrable (greenFunction O x) μ := by
  have hO : Bornology.IsBounded O := hbounded.subset hsub
  refine hint.mono_nonneg (measurable_greenFunction hopen x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => greenFunction_nonneg hO x y) ?_
  exact Filter.Eventually.of_forall (greenFunction_le_of_subset hsub hbounded x)

/-- Volume growth on a ball implies Green-kernel integrability on any open subdomain
of that ball. -/
theorem integrable_greenFunction_of_volumeGrowth {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {O : Set ℂ} {R βminus βplus : ℝ} (hR : 0 < R) (hopen : IsOpen O)
    (hsub : O ⊆ Metric.ball (0 : ℂ) R) (hV : VolumeGrowth μ R βminus βplus)
    {x : ℂ} (hx : x ∈ Metric.closedBall (0 : ℂ) R) :
    Integrable (greenFunction O x) μ := by
  obtain ⟨hI, -⟩ := greenPotential_ball_holderOnWith hR hV (memLp_top_const (1 : ℝ))
  have hIon : IntegrableOn (greenFunction (Metric.ball (0 : ℂ) R) x)
      (Metric.ball (0 : ℂ) R) μ := by
    simpa only [mul_one] using hI x hx
  have hsupp : Function.support (greenFunction (Metric.ball (0 : ℂ) R) x) ⊆
      Metric.ball (0 : ℂ) R := by
    intro y hy
    by_contra hy'
    exact hy (greenFunction_of_notMem_right hy' x)
  exact integrable_greenFunction_of_subset hopen hsub Metric.isBounded_ball μ x
    ((integrableOn_iff_integrable_of_support_subset hsupp).mp hIon)

/-- Positive ball mass, absence of an atom at the pole, and volume growth yield a
strictly positive Green potential on an open subdomain of a ball. -/
theorem greenPotential_pos_of_volumeGrowth {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {O : Set ℂ} {R βminus βplus : ℝ} (hR : 0 < R) (hopen : IsOpen O)
    (hsub : O ⊆ Metric.ball (0 : ℂ) R) (hV : VolumeGrowth μ R βminus βplus)
    {x : ℂ} (hx : x ∈ O) (hμx : μ {x} = 0)
    (hμball : ∀ r > 0, 0 < μ (Metric.ball x r)) :
    0 < greenPotential O μ x := by
  have hbounded : Bornology.IsBounded O := Metric.isBounded_ball.subset hsub
  exact greenPotential_pos_of_ball_mass hbounded hopen μ x hx hμx hμball
    (integrable_greenFunction_of_volumeGrowth hR hopen hsub hV
      (Metric.ball_subset_closedBall (hsub hx)))

end HarmonicBalls.Section6
