import HarmonicBalls.Steps.Sec11.PathClearancePartition
import HarmonicBalls.Steps.Sec11.BoundaryClearanceChains
import HarmonicBalls.Steps.Sec11.PinchConstrainedPaths

/-! # Finiteness of constrained internal distances

An open connected corridor gives finite internal distances uniformly on compact
sets. This supplies the finiteness part of the constrained-path construction;
it does not assert that such a corridor exists for the pinch configuration or
that the required strict comparison has positive probability.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Points joined by a path in an open set have finite internal distance for
any length metric inducing the Euclidean topology. -/
theorem IsEuclideanLengthMetric.internalMetric_lt_top_of_joinedIn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x y : ℂ} (hxy : JoinedIn U x y) : internalMetric D U x y < ∞ := by
  obtain ⟨p, hp⟩ := hxy
  obtain ⟨n, v, _, hv0, hvn, hchain, _⟩ := hD.exists_clearance_chain_of_path hU p hp
  have hv : v 0 ∈ U := by rw [hv0]; simpa using hp 0
  have hbound := hD.internalMetric_le_sum_of_boundary_clearance hnonneg hU v hv n hchain
  rw [hv0, hvn] at hbound
  exact hbound.trans_lt (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top)

/-- A path inside an open set can be replaced by one of finite length in any
Euclidean length metric. -/
theorem IsEuclideanLengthMetric.exists_finiteLength_path_of_joinedIn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x y : ℂ} (hxy : JoinedIn U x y) :
    ∃ p : Path x y, (∀ t, p t ∈ U) ∧ pathLength D p < ∞ := by
  have hfin := hD.internalMetric_lt_top_of_joinedIn hnonneg hU hxy
  change (⨅ p : Path x y, ⨅ (_ : ∀ t, p t ∈ U), pathLength D p) < ∞ at hfin
  obtain ⟨p, hp⟩ := iInf_lt_iff.mp hfin
  obtain ⟨hU, hp⟩ := iInf_lt_iff.mp hp
  exact ⟨p, hU, hp⟩

/-- Internal distances from a point are uniformly finite on a compact subset
of an open connected domain. -/
theorem IsEuclideanLengthMetric.iSup_internalMetric_lt_top_of_isCompact
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U K : Set ℂ} (hU : IsOpen U)
    (hconn : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : ℂ} (hx : x ∈ U) : (⨆ y ∈ K, internalMetric D U x y) < ∞ := by
  by_cases hne : K.Nonempty
  · have hcts := (hD.continuousOn_internalMetric hnonneg hU x).mono hKU
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hcts
    have hfin : internalMetric D U x y < ∞ :=
      hD.internalMetric_lt_top_of_joinedIn hnonneg hU
        ((hU.isConnected_iff_isPathConnected.mp hconn).joinedIn x hx y (hKU hy))
    apply lt_of_le_of_lt _ hfin
    exact iSup_le fun z => iSup_le fun hz => hmax hz
  · have hempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, notMem_empty, iSup_of_empty, iSup_const, bot_lt_top]

/-- A connected open corridor inside the obstacle complement and the radius-six
ball makes the constrained distances to the radius-five sphere uniformly
finite. The construction of the corridor and any comparison with the boundary
distance remain separate hypotheses. -/
theorem IsEuclideanLengthMetric.pinch_constrained_iSup_lt_top_of_corridor
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {Q W U : Set ℂ} {δ : ℝ}
    (hU : IsOpen U) (hconn : IsConnected U) (hzero : (0 : ℂ) ∈ U)
    (hsphere : sphere (0 : ℂ) 5 ⊆ U)
    (hsub : U ⊆ (thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) < ∞ := by
  apply lt_of_le_of_lt _
    (hD.iSup_internalMetric_lt_top_of_isCompact hnonneg hU hconn
      (isCompact_sphere (0 : ℂ) 5) hsphere hzero)
  exact iSup_le fun y => iSup_le fun hy =>
    le_iSup_of_le y (le_iSup_of_le hy (internalMetric_anti D hsub 0 y))

end HarmonicBalls
