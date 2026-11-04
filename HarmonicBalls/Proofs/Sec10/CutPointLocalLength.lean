import HarmonicBalls.Proofs.Sec10.ConnectedCutPointPieces
import HarmonicBalls.Proofs.Sec10.LocalFrontierLength

/-! # Local length at a cut point

A cut point of a compact continuum forces two disjoint branches to cross
all sufficiently small annuli. Each branch contributes its radius to the
one-dimensional Hausdorff measure.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Topology Filter
open scoped ENNReal MeasureTheory

/-- At a cut point of a compact continuum, each sufficiently small ball
contains continuum length at least twice its radius. -/
theorem IsConnected.local_length_ge_two_mul_of_cut_point
    {S : Set ℂ} (hS : IsConnected S) (hSc : IsCompact S) {a : ℂ} (ha : a ∈ S)
    (hcut : ¬ IsPreconnected (S \ {a})) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      2 * ENNReal.ofReal r ≤ μH[1] (S ∩ ball a r) := by
  obtain ⟨A, B, hAc, hBc, hA, hB, hAB, hABa, hAp, hBp⟩ :=
    IsConnected.exists_compact_decomposition_of_cut_point hS hSc ha hcut
  have haAB : a ∈ A ∩ B := hABa.symm ▸ mem_singleton a
  obtain ⟨x, hxS, hxA⟩ := hAp
  obtain ⟨y, hyS, hyB⟩ := hBp
  have hxB : x ∈ B := (show x ∈ A ∪ B from hAB.symm ▸ hxS).resolve_left hxA
  have hyA : y ∈ A := (show y ∈ A ∪ B from hAB.symm ▸ hyS).resolve_right hyB
  have hxa : x ≠ a := by rintro rfl; exact hxA haAB.1
  have hya : y ≠ a := by rintro rfl; exact hyB haAB.2
  let R := min (dist x a) (dist y a)
  have hR : 0 < R := lt_min (dist_pos.mpr hxa) (dist_pos.mpr hya)
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  let D : Set ℂ := {q | 0 < dist q a ∧ dist q a < r}
  have hmeasB : MeasurableSet (B ∩ D) := by
    apply hBc.isClosed.measurableSet.inter
    exact ((isOpen_Ioi.preimage (continuous_id.dist continuous_const)).inter
      (isOpen_Iio.preimage (continuous_id.dist continuous_const))).measurableSet
  have hdis : Disjoint (A ∩ D) (B ∩ D) := by
    apply disjoint_left.mpr
    intro q hqA hqB
    have hqa : q = a := mem_singleton_iff.mp (hABa ▸ ⟨hqA.1, hqB.1⟩)
    subst q
    simpa [D] using hqA.2.1
  have hAmeet : ∀ s ∈ Ioo (0 : ℝ) r, (sphere a s ∩ A).Nonempty := by
    intro s hs
    have hsfar : s < dist y a := (hs.2.trans_le hrR).trans_le (min_le_right _ _)
    obtain ⟨q, hq, hqs⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hA.isPreconnected
      (subset_closure haAB.1) hyA hs.1 hsfar
    exact ⟨q, hqs, hq⟩
  have hBmeet : ∀ s ∈ Ioo (0 : ℝ) r, (sphere a s ∩ B).Nonempty := by
    intro s hs
    have hsfar : s < dist x a := (hs.2.trans_le hrR).trans_le (min_le_left _ _)
    obtain ⟨q, hq, hqs⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hB.isPreconnected
      (subset_closure haAB.2) hxB hs.1 hsfar
    exact ⟨q, hqs, hq⟩
  have hAlen : ENNReal.ofReal r ≤ μH[1] (A ∩ D) := by
    simpa [D] using hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres hAmeet
  have hBlen : ENNReal.ofReal r ≤ μH[1] (B ∩ D) := by
    simpa [D] using hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres hBmeet
  have hsub : (A ∩ D) ∪ (B ∩ D) ⊆ S ∩ ball a r := by
    rintro q (hq | hq)
    · exact ⟨hAB ▸ Or.inl hq.1, mem_ball.mpr hq.2.2⟩
    · exact ⟨hAB ▸ Or.inr hq.1, mem_ball.mpr hq.2.2⟩
  calc
    2 * ENNReal.ofReal r = ENNReal.ofReal r + ENNReal.ofReal r := by simp [two_mul]
    _ ≤ μH[1] (A ∩ D) + μH[1] (B ∩ D) := add_le_add hAlen hBlen
    _ = μH[1] ((A ∩ D) ∪ (B ∩ D)) := (measure_union hdis hmeasB).symm
    _ ≤ μH[1] (S ∩ ball a r) := measure_mono hsub

/-- Arbitrarily small balls with length strictly below twice their radius
exclude a cut point of a compact continuum. -/
theorem IsConnected.not_isCutPoint_of_small_local_length
    {S : Set ℂ} (hS : IsConnected S) (hSc : IsCompact S) {a : ℂ}
    (hshort : ∀ R : ℝ, 0 < R → ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      μH[1] (S ∩ ball a r) < 2 * ENNReal.ofReal r) :
    ¬ IsCutPoint S a := by
  intro hcut
  obtain ⟨R, hR, hlength⟩ :=
    IsConnected.local_length_ge_two_mul_of_cut_point hS hSc hcut.1 hcut.2
  obtain ⟨r, hr, hrR, hlt⟩ := hshort R hR
  exact (not_le_of_gt hlt) (hlength r hr hrR)

universe u

/-- On the volume-growth event, a cut point of a connected complementary
cluster frontier has at least twice the radius in local Hausdorff length.
The frontier's connectedness remains an explicit hypothesis. -/
theorem ae_cluster_complement_cut_point_local_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      IsPreconnected (frontier U) → ∀ a : ℂ, IsCutPoint (frontier U) a →
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        2 * ENNReal.ofReal r ≤ μH[1] (frontier U ∩ ball a r) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
    hC hcirc μ hGFF hμ hI2] with ω hgeom
  intro t ht z hz hcl U hU hfront a hcut
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hcompact : IsCompact (frontier U) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_frontier
      (fun q hq => ball_subset_closedBall (hg.2.2.2.2 (subset_closure hq)))
  exact IsConnected.local_length_ge_two_mul_of_cut_point
    ⟨⟨a, hcut.1⟩, hfront⟩ hcompact hcut.1 hcut.2

end HarmonicBalls
