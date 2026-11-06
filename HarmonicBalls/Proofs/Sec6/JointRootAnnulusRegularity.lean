import HarmonicBalls.Proofs.Sec6.SingularRootAnnulusRegularity
import HarmonicBalls.Proofs.Sec6.RandomCentreAnnulusTransfer

/-! # Annular regularity under rooted laws

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- The regularity event at a fixed radius is jointly measurable for a
measurable, locally finite family of planar measures. -/
theorem measurableSet_joint_annulus_regular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Ω → Measure ℂ}
    (hμ : Measurable μ) (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω)) (r : ℝ) :
    MeasurableSet {p : Ω × ℂ | μ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ p.1 (annulus p.2 (3*r) (5*r))} := by
  let ν : Ω × ℂ → Measure ℂ := fun p => (μ p.1).map (fun x => x - p.2)
  have hν : Measurable ν := measurable_map_of_locallyFinite (hμ.comp measurable_fst)
    (fun p => hloc p.1) (f := fun p : (Ω × ℂ) × ℂ => p.2 - p.1.2) (by fun_prop)
  have hs (p : Ω × ℂ) (t : ℝ) : ν p (sphere 0 t) = μ p.1 (sphere p.2 t) := by
    rw [Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
    congr 1
    ext x
    simp only [mem_preimage, mem_sphere, dist_eq_norm, sub_zero]
  have ha (p : Ω × ℂ) : ν p (annulus 0 (3*r) (5*r)) =
      μ p.1 (annulus p.2 (3*r) (5*r)) := by
    change ((μ p.1).map (fun x => x - p.2)) (annulus 0 (3*r) (5*r)) = _
    have hm : MeasurableSet (annulus (0 : ℂ) (3*r) (5*r)) :=
      isOpen_ball.measurableSet.diff measurableSet_closedBall
    rw [Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  have h3 := (Measure.measurable_coe (isClosed_sphere.measurableSet :
    MeasurableSet (sphere (0 : ℂ) (3*r)))).comp hν
  have h5 := (Measure.measurable_coe (isClosed_sphere.measurableSet :
    MeasurableSet (sphere (0 : ℂ) (5*r)))).comp hν
  have hA := (Measure.measurable_coe (isOpen_ball.measurableSet.diff
    measurableSet_closedBall : MeasurableSet (annulus (0 : ℂ) (3*r) (5*r)))).comp hν
  have h3' : Measurable (fun p : Ω × ℂ => μ p.1 (sphere p.2 (3*r))) := by
    change Measurable (fun p => ν p (sphere 0 (3*r))) at h3
    simpa only [hs] using h3
  have h5' : Measurable (fun p : Ω × ℂ => μ p.1 (sphere p.2 (5*r))) := by
    change Measurable (fun p => ν p (sphere 0 (5*r))) at h5
    simpa only [hs] using h5
  have hA' : Measurable (fun p : Ω × ℂ => μ p.1 (annulus p.2 (3*r) (5*r))) := by
    change Measurable (fun p => ν p (annulus 0 (3*r) (5*r))) at hA
    simpa only [ha] using hA
  exact (measurableSet_eq_fun h3' measurable_const).inter
    ((measurableSet_eq_fun h5' measurable_const).inter (measurableSet_lt measurable_const hA'))

/-- A fixed-radius regularity property holding for almost every root in almost
every fibre also holds under the composition-product rooted law. -/
theorem ae_compProd_annulus_regular
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : Kernel Ω ℂ)
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) (r : ℝ)
    (hreg : ∀ᵐ ω ∂P, ∀ᵐ z ∂κ ω, μ ω (sphere z (3*r)) = 0 ∧
      μ ω (sphere z (5*r)) = 0 ∧ 0 < μ ω (annulus z (3*r) (5*r))) :
    ∀ᵐ p ∂(P ⊗ₘ κ), μ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ p.1 (annulus p.2 (3*r) (5*r)) := by
  obtain ⟨ν, hν, hνloc, heq⟩ := exists_measurable_locallyFinite_rep hμ hloc
  have hrep := Measure.ae_compProd_of_ae_ae (measurableSet_joint_annulus_regular hν hνloc r) (by
    filter_upwards [heq, hreg] with ω heq hω
    simpa only [← heq] using hω)
  have heq' := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp heq
  filter_upwards [hrep, heq'] with p hp he
  change μ p.1 = ν p.1 at he
  simpa only [he] using hp

/-- Under a rooted law whose kernel is absolutely continuous with respect to
singular LQG mass, zero-singularity annuli are regular at any fixed positive
radius. The two measures are built from the same field. -/
theorem ae_compProd_zero_annulus_regular_at_singular_roots
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ p ∂(P ⊗ₘ κ), μ₀ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ₀ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ₀ p.1 (annulus p.2 (3*r) (5*r)) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  apply ae_compProd_annulus_regular P κ (h.aemeasurable_lqgMeasure hμ₀)
    (hV.mono fun _ hv => hv.1) r
  filter_upwards [hac, ae_zero_annulus_regular_at_singular_roots hgrowth hγ hγ2 hα h hμ hμ₀] with ω ha hreg
  filter_upwards [hreg (κ ω) ha] with z hz
  exact hz r hr

end HarmonicBalls.Section6
