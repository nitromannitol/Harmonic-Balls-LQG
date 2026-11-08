import HarmonicBalls.Proofs.Metric.InternalDistanceCompactBounds
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity
import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Proofs.Sec6.HarnackIteration
import HarmonicBalls.Proposed.PfefferMetricScaling

/-!
# Distances across annuli

Disjoint compact sets in a connected open set have a positive uniform lower
bound and a finite uniform upper bound for their internal distances. We apply
this to the boundary circles of a round annulus. The ambient across distance
is Pfeffer's actual infimum over those circles.

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Disjoint nonempty compact sets inside a connected open set have uniformly
positive and uniformly finite internal distances. -/
theorem IsEuclideanLengthMetric.internalDistance_compact_separated_bounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U K L : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKL : Disjoint K L) (hKU : K ⊆ U) (hLU : L ⊆ U) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ b < ∞ ∧
      ∀ x ∈ K, ∀ y ∈ L, a ≤ internalMetric D U x y ∧ internalMetric D U x y ≤ b := by
  have hpos : 0 < setDist D K L :=
    hD.setDist_pos_of_compact_subset_open hK hKne hL.isClosed.isOpen_compl
      (by intro x hx hxL; exact Set.disjoint_left.mp hKL hx hxL) hLne (by intro x hx; simpa using hx)
  let b := ⨆ x ∈ K ∪ L, ⨆ y ∈ K ∪ L, internalMetric D U x y
  have hb : b < ∞ := hD.internalDistance_compact_uniform_lt_top hU hconn
    (hK.union hL) (union_subset hKU hLU)
  refine ⟨ENNReal.ofReal (setDist D K L), b, ENNReal.ofReal_pos.mpr hpos, hb, ?_⟩
  intro x hx y hy
  constructor
  · calc
      ENNReal.ofReal (setDist D K L) = ⨅ x ∈ K, ⨅ y ∈ L, ENNReal.ofReal (D x y) :=
        ofReal_setDist_eq_iInf hKne hLne
      _ ≤ ENNReal.ofReal (D x y) :=
        iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y (iInf_le _ hy)))
      _ = internalMetric D univ x y := hD.ofReal_eq_internalMetric x y
      _ ≤ internalMetric D U x y := internalMetric_anti D (subset_univ U) x y
  · exact le_iSup_of_le x (le_iSup_of_le (Or.inl hx)
      (le_iSup_of_le y (le_iSup_of_le (show y ∈ K ∪ L from Or.inr hy) le_rfl)))

/-- The across distance is the extended nonnegative value of the ordinary
set distance between the boundary circles. -/
theorem pfefferAcross_eq_ofReal_setDist (D : ℂ → ℂ → ℝ) (z : ℂ)
    {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    pfefferAcross D z r R = ENNReal.ofReal (setDist D (sphere z r) (sphere z R)) := by
  exact (ofReal_setDist_eq_iInf (NormedSpace.sphere_nonempty.mpr hr)
    (NormedSpace.sphere_nonempty.mpr hR)).symm

/-- The actual ambient across distance is strictly positive and finite. -/
theorem IsEuclideanLengthMetric.pfefferAcross_pos_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < pfefferAcross D z r R ∧ pfefferAcross D z r R < ∞ := by
  rw [pfefferAcross_eq_ofReal_setDist D z hr.le (hr.le.trans hrR.le)]
  exact ⟨ENNReal.ofReal_pos.mpr (hD.setDist_spheres_pos z hr hrR), ENNReal.ofReal_lt_top⟩

/-- In any open annulus whose radii strictly bracket `r` and `R`, the
internal distances between the boundary circles are uniformly bounded above
and below by finite and positive constants. -/
theorem IsEuclideanLengthMetric.internalDistance_spheres_uniform_bounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (z : ℂ) {s r R T : ℝ} (hs : 0 ≤ s) (hsr : s < r) (hrR : r < R) (hRT : R < T) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ b < ∞ ∧
      ∀ x ∈ sphere z r, ∀ y ∈ sphere z R,
        a ≤ internalMetric D (annulus z s T) x y ∧
        internalMetric D (annulus z s T) x y ≤ b := by
  have hr : 0 ≤ r := hs.trans hsr.le
  have hR : 0 ≤ R := hr.trans hrR.le
  have hK : sphere z r ⊆ annulus z s T := by
    intro x hx
    have hd : dist x z = r := mem_sphere.mp hx
    exact ⟨by rw [mem_ball, hd]; linarith,
      by rw [mem_closedBall, hd]; linarith⟩
  have hL : sphere z R ⊆ annulus z s T := by
    intro x hx
    have hd : dist x z = R := mem_sphere.mp hx
    exact ⟨by rw [mem_ball, hd]; linarith,
      by rw [mem_closedBall, hd]; linarith⟩
  have hconn : IsConnected (annulus z s T) :=
    ⟨(NormedSpace.sphere_nonempty.mpr hr).mono hK, Section6.isPreconnected_annulus z hs T⟩
  apply hD.internalDistance_compact_separated_bounds
    (isOpen_ball.sdiff isClosed_closedBall) hconn (isCompact_sphere z r) (isCompact_sphere z R)
    (NormedSpace.sphere_nonempty.mpr hr) (NormedSpace.sphere_nonempty.mpr hR) ?_ hK hL
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [mem_sphere] at hx hy
  linarith

/-- The infimum of internal distances across the two boundary circles is
strictly positive and finite in a surrounding open annulus. -/
theorem IsEuclideanLengthMetric.internalAcross_spheres_pos_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (z : ℂ) {s r R T : ℝ} (hs : 0 ≤ s) (hsr : s < r) (hrR : r < R) (hRT : R < T) :
    0 < (⨅ x ∈ sphere z r, ⨅ y ∈ sphere z R, internalMetric D (annulus z s T) x y) ∧
      (⨅ x ∈ sphere z r, ⨅ y ∈ sphere z R, internalMetric D (annulus z s T) x y) < ∞ := by
  obtain ⟨a, b, ha, hb, hbounds⟩ :=
    hD.internalDistance_spheres_uniform_bounds z hs hsr hrR hRT
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := z)).mpr (hs.trans hsr.le)
  obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := z)).mpr ((hs.trans hsr.le).trans hrR.le)
  constructor
  · exact ha.trans_le (le_iInf fun x => le_iInf fun hx => le_iInf fun y =>
      le_iInf fun hy => (hbounds x hx y hy).1)
  · exact (iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y
      (iInf_le_of_le hy (hbounds x hx y hy).2)))).trans_lt hb

#print axioms IsEuclideanLengthMetric.internalDistance_compact_separated_bounds
#print axioms pfefferAcross_eq_ofReal_setDist
#print axioms IsEuclideanLengthMetric.pfefferAcross_pos_lt_top
#print axioms IsEuclideanLengthMetric.internalDistance_spheres_uniform_bounds
#print axioms IsEuclideanLengthMetric.internalAcross_spheres_pos_lt_top

end HarmonicBalls
