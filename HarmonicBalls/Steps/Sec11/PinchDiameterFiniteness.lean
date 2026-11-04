import HarmonicBalls.Steps.Sec11.PinchConstrainedFiniteness

/-! # Finiteness of auxiliary internal diameters

Compactness and connected open neighborhoods give uniform internal-distance
bounds for the auxiliary pinch pieces.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The internal distances between points of a compact subset of an open
connected set are uniformly finite. -/
theorem IsEuclideanLengthMetric.iSup_pair_internalMetric_lt_top_of_isCompact
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U K : Set ℂ} (hU : IsOpen U)
    (hconn : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D U x y) < ∞ := by
  obtain ⟨z, hz⟩ := hconn.nonempty
  let L := ⨆ x ∈ K, internalMetric D U z x
  have hL : L < ∞ := hD.iSup_internalMetric_lt_top_of_isCompact hnonneg hU hconn hK hKU hz
  apply lt_of_le_of_lt _ (ENNReal.add_lt_top.mpr ⟨hL, hL⟩)
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  calc
    internalMetric D U x y ≤ internalMetric D U x z + internalMetric D U z y :=
      hD.internalMetric_triangle U x z y
    _ ≤ L + L := add_le_add
      (by rw [hD.internalMetric_symm U x z]; exact le_iSup_of_le x (le_iSup_of_le hx le_rfl))
      (le_iSup_of_le y (le_iSup_of_le hy le_rfl))

/-- A bounded set has finite internal diameter if its closure lies in a
connected open subset of its thickening. -/
theorem IsEuclideanLengthMetric.internalDiam_lt_top_of_connected_neighborhood
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {A U : Set ℂ} {δ : ℝ}
    (hA : Bornology.IsBounded A) (hU : IsOpen U) (hconn : IsConnected U)
    (hAU : closure A ⊆ U) (hUδ : U ⊆ thickening δ A) :
    internalDiam D δ A < ∞ := by
  have hcompact : IsCompact (closure A) :=
    isCompact_of_isClosed_isBounded isClosed_closure hA.closure
  have hfin := hD.iSup_pair_internalMetric_lt_top_of_isCompact hnonneg hU hconn hcompact hAU
  apply lt_of_le_of_lt _ hfin
  unfold internalDiam
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact (internalMetric_anti D hUδ x y).trans (le_iSup_of_le x
    (le_iSup_of_le (subset_closure hx) (le_iSup_of_le y
      (le_iSup_of_le (subset_closure hy) le_rfl))))

/-- A bounded set has finite internal diameter whenever its thickening is
connected. -/
theorem IsEuclideanLengthMetric.internalDiam_lt_top_of_connected_thickening
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {A : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hA : Bornology.IsBounded A) (hconn : IsConnected (thickening δ A)) :
    internalDiam D δ A < ∞ := by
  have hcompact : IsCompact (closure A) :=
    isCompact_of_isClosed_isBounded isClosed_closure hA.closure
  have hfin := hD.iSup_pair_internalMetric_lt_top_of_isCompact hnonneg
    isOpen_thickening hconn hcompact (closure_subset_thickening hδ A)
  apply lt_of_le_of_lt _ hfin
  unfold internalDiam
  exact iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    le_iSup_of_le x (le_iSup_of_le (subset_closure hx)
      (le_iSup_of_le y (le_iSup_of_le (subset_closure hy) le_rfl)))

/-- The concentric inner ball in a pinch proof configuration has finite
internal diameter. -/
theorem IsPinchPointProofConfiguration.internalDiam_inner_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) : internalDiam D δ V < ∞ := by
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := hconfig.concentric
  have hVne : V.Nonempty := hconfig.isConnected_U.nonempty.mono
    (subset_closure.trans hconfig.closure_U_subset_V)
  have hρV : 0 < ρV := by rw [hV, nonempty_ball] at hVne; exact hVne
  have hbV : Bornology.IsBounded V := by rw [hV]; exact isBounded_ball
  have hc : IsConnected (thickening δ V) := by
    rw [hV, thickening_ball hconfig.δ₀_mem.1 hρV]
    exact isConnected_ball (by linarith [hconfig.δ₀_mem.1])
  exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hconfig.δ₀_mem.1 hbV hc

end HarmonicBalls
