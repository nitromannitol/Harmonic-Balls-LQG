import HarmonicBalls.Proofs.Sec5.LocalRestrictedShiftedCluster
import HarmonicBalls.Proofs.Sec5.GeneralDomainMeasureLocality

/-! # Shifted obstacle compatibility for dominated measures

The shifted and unshifted non-coincidence sets agree whenever the Green
potential is continuous and has the expected Laplacian. Domination by a
volume-growth measure supplies these properties without lower mass bounds.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian

/-- Supersolutions correspond after adding a continuous Green potential with
the expected Laplacian. -/
theorem supersolutions_iff_shifted_of_greenPotential
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R t : ℝ} {z : ℂ}
    (hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    (hΔq : HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R))
    (w : ℂ → ℝ) : w ∈ supersolutions μ R z t ↔
      (fun x => w x + greenPotentialBall μ R x) ∈ shiftedSupersolutions μ R z t := by
  have := hμ
  set q := greenPotentialBall μ R with hqdef
  have hqloc : LocallyIntegrableOn q (ball 0 R) := hΔq.1
  have hφμ : ∀ φ : ℂ → ℝ, IsTestFunction (ball 0 R) φ → Integrable φ μ := fun φ hφ =>
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hqΔ : ∀ φ : ℂ → ℝ, IsTestFunction (ball 0 R) φ →
      ∫ x, q x * Δ φ x = -∫ x, φ x ∂μ := fun φ hφ => by
    have h := (hΔq.2 φ hφ).2.2
    rw [integral_zero_measure, zero_sub] at h
    exact h
  constructor
  · rintro ⟨hwc, hwL, hwo⟩
    refine ⟨hwc.add hqc, ⟨hwL.1.add hqloc, fun φ hφ hφ0 _ => ?_⟩, fun x hx hxz => ?_⟩
    · have h1 := hwL.2 φ hφ hφ0 (hφμ φ hφ)
      rw [integral_zero_measure]
      have e : (fun x => (w x + q x) * Δ φ x) = fun x => w x * Δ φ x + q x * Δ φ x := by
        funext x; ring
      rw [e, integral_add (integrable_mul_laplacian_of_test hwL.1 hφ)
        (integrable_mul_laplacian_of_test hqloc hφ), hqΔ φ hφ]
      linarith
    · have := hwo x hx hxz
      simp only [obstacle, ← hqdef]
      linarith
  · rintro ⟨hwc, hwL, hwo⟩
    have hwc' : ContinuousOn w (closedBall 0 R) :=
      (hwc.sub hqc).congr fun x _ => by simp
    have e : (fun x => (w x + q x) - q x) = w := funext fun x => add_sub_cancel_right _ _
    have hwloc : LocallyIntegrableOn w (ball 0 R) := e ▸ hwL.1.sub hqloc
    refine ⟨hwc', ⟨hwloc, fun φ hφ hφ0 _ => ?_⟩, fun x hx hxz => ?_⟩
    · have h1 := hwL.2 φ hφ hφ0 integrable_zero_measure
      rw [integral_zero_measure] at h1
      have e' : (fun x => (w x + q x) * Δ φ x) = fun x => w x * Δ φ x + q x * Δ φ x := by
        funext x; ring
      rw [e', integral_add (integrable_mul_laplacian_of_test hwloc hφ)
        (integrable_mul_laplacian_of_test hqloc hφ), hqΔ φ hφ] at h1
      linarith
    · have := hwo x hx hxz
      simp only [obstacle, ← hqdef] at this
      linarith

/-- Off the pole, the shifted least supersolution is obtained by adding the
Green potential to the unshifted least supersolution. -/
theorem leastSupersolution_eq_shifted_of_greenPotential
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R t : ℝ} {z x : ℂ}
    (ht : 0 ≤ t) (hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    (hΔq : HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R))
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x =
      shiftedLeastSupersolution μ R z t x - greenPotentialBall μ R x := by
  set q := greenPotentialBall μ R with hqdef
  have hmem := supersolutions_iff_shifted_of_greenPotential (t := t) (z := z) hμ hqc hΔq
  have hqS : q ∈ shiftedSupersolutions μ R z t :=
    greenPotentialBall_mem_shiftedSupersolutions ht hqc hΔq.laplacianLE
  have himg : (fun w : ℂ → ℝ => w x) '' supersolutions μ R z t =
      (fun a => a - q x) '' ((fun u : ℂ → ℝ => u x) '' shiftedSupersolutions μ R z t) := by
    ext a
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w x + q x, ⟨fun y => w y + q y, (hmem w).1 hw, rfl⟩, by ring⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨fun y => u y - q y, (hmem _).2 ?_, rfl⟩
      convert hu using 1
      funext y
      ring
  rw [leastSupersolution, himg, shiftedLeastSupersolution]
  exact (Monotone.map_csInf_of_continuousAt (continuousAt_id.sub continuousAt_const)
    (fun a b h => sub_le_sub_right h _)
    (⟨q x, q, hqS, rfl⟩ : ((fun u : ℂ → ℝ => u x) '' shiftedSupersolutions μ R z t).Nonempty)
    (bddBelow_shiftedSupersolutions hx hxz)).symm

/-- Shifted and unshifted clusters agree under the Green-potential hypotheses. -/
theorem cluster_eq_nonCoincidenceSet_of_greenPotential
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R t : ℝ} {z : ℂ}
    (ht : 0 ≤ t) (hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    (hΔq : HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R)) :
    cluster μ R z t = nonCoincidenceSet μ R z t := by
  ext x
  by_cases hxz : x = z
  · simp only [cluster, nonCoincidenceSet, mem_ofPred_eq, hxz, true_or]
  · have hls := leastSupersolution_eq_shifted_of_greenPotential (z := z) (x := x) hμ ht hqc hΔq
    simp only [cluster, nonCoincidenceSet, mem_ofPred_eq, hxz, false_or, obstacle]
    constructor <;> rintro ⟨hx, hp⟩ <;> refine ⟨hx, ?_⟩
    · rw [hls (ball_subset_closedBall hx) hxz] at hp
      linarith
    · rw [hls (ball_subset_closedBall hx) hxz]
      linarith

/-- The disc cluster depends only on the restriction of the measure to the disc. -/
theorem cluster_eq_restrict_ball (μ : Measure ℂ) (R t : ℝ) (z : ℂ) :
    cluster μ R z t = cluster (μ.restrict (ball 0 R)) R z t := by
  have hrestrict : μ.restrict (ball 0 R) =
      (μ.restrict (ball 0 R)).restrict (ball 0 R) := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_self]
  have heq : supersolutions μ R z t = supersolutions (μ.restrict (ball 0 R)) R z t := by
    ext w
    simp only [supersolutions, mem_ofPred_eq,
      laplacianLE_iff_of_restrict_eq measurableSet_ball hrestrict w]
  simp only [cluster, leastSupersolution, heq]

/-- The shifted non-coincidence set depends only on the disc restriction. -/
theorem nonCoincidenceSet_eq_restrict_ball (μ : Measure ℂ) (R t : ℝ) (z : ℂ) :
    nonCoincidenceSet μ R z t = nonCoincidenceSet (μ.restrict (ball 0 R)) R z t := by
  have hq : greenPotentialBall μ R = greenPotentialBall (μ.restrict (ball 0 R)) R := by
    funext x
    simp only [greenPotentialBall, Measure.restrict_restrict measurableSet_ball, inter_self]
  simp only [nonCoincidenceSet, shiftedLeastSupersolution, shiftedSupersolutions, obstacle, hq]

/-- Domination by a volume-growth measure implies shifted compatibility,
without any lower volume-growth hypothesis for the dominated measure. -/
theorem cluster_eq_nonCoincidenceSet_of_dominated
    {μ σ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hσ : σ ≤ μ)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) : cluster σ R z t = nonCoincidenceSet σ R z t := by
  have hσ' : IsLocallyFiniteMeasure (σ.restrict (ball 0 R)) :=
    Measure.isLocallyFiniteMeasure_of_le (Measure.restrict_le_self.trans hσ)
  obtain ⟨hc, hΔ⟩ := dominated_greenPotentialBall hμ hR hV hσ
  rw [cluster_eq_restrict_ball, nonCoincidenceSet_eq_restrict_ball]
  exact cluster_eq_nonCoincidenceSet_of_greenPotential hσ' ht hc hΔ

end HarmonicBalls
