import HarmonicBalls.Proofs.Sec10.ClosedContinuumBoundaryBumping
import HarmonicBalls.Proofs.Sec10.CompactBoundaryCrossings

/-!
# Local connectivity away from the origin

The localized crossing estimate applies to nonzero boundary points. Thus it
implies local connectivity when the complementary boundary avoids the origin,
conditional on the annular crossing inputs.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Finite crossing counts make the center component a neighborhood in a
closed connected planar set which meets the exterior of the ball. -/
theorem IsConnected.ball_component_mem_nhdsWithin_of_finite_crossings_of_isClosed
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F)
    {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hout : (F \ ball x R).Nonempty)
    (hfinite : (crossingComponents (F ∩ ball x R) x r R).Finite) :
    connectedComponentIn (F ∩ ball x R) x ∈ 𝓝[F] x := by
  apply connectedComponentIn_mem_nhdsWithin_of_finite_cover hFc hr hrR hfinite
  · exact fun C hC => hC.1
  · intro y hy
    have hyR : y ∈ F ∩ ball x R := ⟨hy.1, ball_subset_ball hrR.le hy.2⟩
    let C := connectedComponentIn (F ∩ ball x R) y
    have hyC : y ∈ C := mem_connectedComponentIn hyR
    have hC : C ∈ connectedComponentsIn (F ∩ ball x R) := ⟨y, hyR, rfl⟩
    have hcross : CrossesAnnulus C x r R :=
      IsConnected.ball_component_crosses_of_meets_inner_ball_of_isClosed hF hFc hrR hout hC
        ⟨y, hyC, hy.2⟩
    exact mem_sUnion.mpr ⟨C, ⟨hC, hcross⟩, hyC⟩

/-- Finiteness of crossings at arbitrarily small scales gives a connected
relative neighborhood at the center. -/
theorem IsConnected.exists_connected_relative_neighborhood_of_small_finite_crossings
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F) {x : ℂ} (hx : x ∈ F)
    {N : Set ℂ} (hN : N ∈ 𝓝[F] x)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ r R : ℝ,
      0 < r ∧ r < R ∧ R < δ ∧
        (crossingComponents (F ∩ ball x R) x r R).Finite) :
    ∃ V ∈ 𝓝[F] x, V ⊆ N ∩ F ∧ IsConnected V := by
  classical
  by_cases hother : ∃ y ∈ F, y ≠ x
  · obtain ⟨y, hyF, hyx⟩ := hother
    obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhdsWithin_iff.mp hN
    have hd : 0 < dist y x := dist_pos.mpr hyx
    obtain ⟨r, R, hr, hrR, hR, hfinite⟩ := hsmall (min δ (dist y x)) (lt_min hδ hd)
    have hout : (F \ ball x R).Nonempty := by
      refine ⟨y, hyF, ?_⟩
      intro hyball
      have hylt := mem_ball.mp hyball
      have hRd := hR.trans_le (min_le_right _ _)
      exact (not_lt_of_ge hRd.le) hylt
    let C := connectedComponentIn (F ∩ ball x R) x
    have hxR : x ∈ F ∩ ball x R := ⟨hx, mem_ball_self (hr.trans hrR)⟩
    refine ⟨C, IsConnected.ball_component_mem_nhdsWithin_of_finite_crossings_of_isClosed
      hF hFc hr hrR hout hfinite, ?_, isConnected_connectedComponentIn_iff.mpr hxR⟩
    intro z hz
    have hz' := connectedComponentIn_subset (F ∩ ball x R) x hz
    exact ⟨hδN ⟨ball_subset_ball (hR.trans_le (min_le_left _ _)).le hz'.2, hz'.1⟩, hz'.1⟩
  · have hsub : F ⊆ {x} := by
      intro y hy
      have hyx : y = x := by
        by_contra hne
        exact hother ⟨y, hy, hne⟩
      exact mem_singleton_iff.mpr hyx
    refine ⟨{x}, mem_of_superset self_mem_nhdsWithin hsub, ?_, isConnected_singleton⟩
    rintro y (rfl : y = x)
    exact ⟨mem_of_mem_nhdsWithin hx hN, hx⟩

/-- A complementary component whose boundary avoids the origin has locally
connected complement, conditional on the annular crossing inputs. -/
theorem ae_complement_locallyConnected_of_origin_not_mem_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        (0 : ℂ) ∉ frontier U → IsLocallyConnectedSet Uᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨α, _, hbound⟩ :=
    ae_boundary_complement_localized_crossings_of_compact_continuum
      hI2 h6 h5 hcompactBump γ hγ hγ2
  filter_upwards [hbound α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hcount hgeom
  intro t ht z hz hcl U hU horigin
  have hgeo := hgeom t 1 ht zero_lt_one z hz hcl U hU
  apply IsConnected.isLocallyConnectedSet_of_small_finite_crossings hgeo.2.2.1 hgeo.1.isClosed_compl
  intro x hx δ hδ
  have hxfront : x ∈ frontier U := by simpa only [frontier_compl] using hx.2
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    exact horigin hxfront
  have hevent := hcount t ht z hz hcl U hU x hxfront hx0
  have hevent' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ ρ ∈ Icc ε (Real.sqrt ε),
        (crossingComponents (Uᶜ ∩ ball x (2 * ρ)) x (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊) ∧
      ε < (δ / 2) ^ 2 ∧ 0 < ε := by
    filter_upwards [hevent,
      (eventually_lt_nhds (sq_pos_of_pos (half_pos hδ))).filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hsmall hpos
    exact ⟨hε, hsmall, hpos⟩
  obtain ⟨ε, ⟨ρ, hρ, hρcount⟩, hεsmall, hεpos⟩ := hevent'.exists
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hsqrt : Real.sqrt ε < δ / 2 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hεsmall
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (half_pos hδ)] using hs
  refine ⟨ρ / 3, 2 * ρ, by linarith, by linarith, by linarith [hρ.2], ?_⟩
  apply Set.encard_lt_top_iff.mp
  exact hρcount.trans_lt (by simp)

/-- At each nonzero point of any complementary boundary, the complement has
connected relative neighborhoods, conditional on the annular crossing inputs. -/
theorem ae_complement_localConnectivity_at_nonzero_boundary
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ x ∈ frontier U, x ≠ 0 → ∀ N ∈ 𝓝[Uᶜ] x,
        ∃ V ∈ 𝓝[Uᶜ] x, V ⊆ N ∩ Uᶜ ∧ IsConnected V := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨α, _, hbound⟩ :=
    ae_boundary_complement_localized_crossings_of_compact_continuum
      hI2 h6 h5 hcompactBump γ hγ hγ2
  filter_upwards [hbound α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hcount hgeom
  intro t ht z hz hcl U hU x hxfront hx0 N hN
  have hgeo := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hxF : x ∈ Uᶜ := by
    rw [hgeo.1.frontier_eq] at hxfront
    exact hxfront.2
  apply IsConnected.exists_connected_relative_neighborhood_of_small_finite_crossings
    hgeo.2.2.1 hgeo.1.isClosed_compl hxF hN
  intro δ hδ
  have hevent := hcount t ht z hz hcl U hU x (by
    simpa only [hgeo.1.frontier_eq] using hxfront) hx0
  have hevent' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ ρ ∈ Icc ε (Real.sqrt ε),
        (crossingComponents (Uᶜ ∩ ball x (2 * ρ)) x (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊) ∧
      ε < (δ / 2) ^ 2 ∧ 0 < ε := by
    filter_upwards [hevent,
      (eventually_lt_nhds (sq_pos_of_pos (half_pos hδ))).filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hsmall hpos
    exact ⟨hε, hsmall, hpos⟩
  obtain ⟨ε, ⟨ρ, hρ, hρcount⟩, hεsmall, hεpos⟩ := hevent'.exists
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hsqrt : Real.sqrt ε < δ / 2 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hεsmall
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (half_pos hδ)] using hs
  refine ⟨ρ / 3, 2 * ρ, by linarith, by linarith, by linarith [hρ.2], ?_⟩
  exact Set.encard_lt_top_iff.mp (hρcount.trans_lt (by simp))

/-- Local connectivity at all nonzero frontier points implies local
connectivity after removing the origin. -/
theorem isLocallyConnectedSet_sdiff_zero_of_frontier
    (F : Set ℂ)
    (hfront : ∀ x ∈ F ∩ frontier F, x ≠ 0 → ∀ N ∈ 𝓝[F] x,
      ∃ V ∈ 𝓝[F] x, V ⊆ N ∩ F ∧ IsConnected V) :
    IsLocallyConnectedSet (F \ {0}) := by
  intro x hx N hN
  have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hN' : N ∈ 𝓝[F] x := by
    simpa only [hx0.nhdsWithin_sdiff_singleton F] using hN
  have hN'' : N \ {0} ∈ 𝓝[F] x := by
    have hne : {0}ᶜ ∈ 𝓝[F] x :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hx0)
    exact inter_mem hN' hne
  have hlocal : ∃ V ∈ 𝓝[F] x, V ⊆ (N \ {0}) ∩ F ∧ IsConnected V := by
    by_cases hxint : x ∈ interior F
    · exact exists_connected_relative_neighborhood_of_mem_interior hxint hN''
    · exact hfront x ⟨hx.1, (mem_frontier_iff_notMem_interior hx.1).mpr hxint⟩ hx0 _ hN''
  obtain ⟨V, hV, hVsub, hconn⟩ := hlocal
  refine ⟨V, ?_, ?_, hconn⟩
  · simpa only [hx0.nhdsWithin_sdiff_singleton F] using hV
  · intro y hy
    have hy' := hVsub hy
    exact ⟨hy'.1.1, hy'.2, hy'.1.2⟩

/-- Every complementary cluster component has a locally connected complement
outside the origin, conditional on the annular crossing inputs. -/
theorem ae_complement_sdiff_zero_locallyConnected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet (Uᶜ \ {0}) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_localConnectivity_at_nonzero_boundary hI2 h6 h5 hcompactBump
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro t ht z hz hcl U hU
  apply isLocallyConnectedSet_sdiff_zero_of_frontier
  intro x hx hx0 N hN
  apply hω t ht z hz hcl U hU x
  · simpa only [frontier_compl] using hx.2
  · exact hx0
  · exact hN

end HarmonicBalls
