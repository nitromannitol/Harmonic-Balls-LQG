import HarmonicBalls.Proofs.Sec10.LocalConnectivityFromCrossings

/-!
# Local connectivity at an isolated exceptional point

For a closed connected planar set, local connectivity away from one point
extends to that point. A compact circle can be covered by finitely many
connected relative neighborhoods, so only finitely many components of a
larger ball can meet a smaller concentric ball.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Local connectivity off one point extends across it for a closed connected
planar set. -/
theorem IsConnected.isLocallyConnectedSet_of_sdiff_singleton
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F) {x : ℂ}
    (hlocal : IsLocallyConnectedSet (F \ {x})) : IsLocallyConnectedSet F := by
  classical
  intro p hp N hN
  by_cases hpx : p = x
  · subst p
    by_cases hother : ∃ y ∈ F, y ≠ x
    · obtain ⟨y, hyF, hyx⟩ := hother
      have hdist : 0 < dist y x := dist_pos.mpr hyx
      obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhdsWithin_iff.mp hN
      let R : ℝ := min δ (dist y x) / 2
      have hR : 0 < R := by dsimp [R]; positivity
      have hRδ : R < δ := by dsimp [R]; have := min_le_left δ (dist y x); linarith
      have hRd : R < dist y x := by dsimp [R]; have := min_le_right δ (dist y x); linarith
      have hout : (F \ ball x R).Nonempty := ⟨y, hyF, fun h => (not_lt_of_ge hRd.le) (mem_ball.mp h)⟩
      let K : Set ℂ := F ∩ sphere x (R / 2)
      have hKc : IsCompact K := (isCompact_sphere x (R / 2)).of_isClosed_subset
        (hFc.inter isClosed_sphere) inter_subset_right
      have hKlocal : ∀ q : K, ∃ V : Set ℂ, V ∈ 𝓝[F] (q : ℂ) ∧
          V ⊆ F ∩ ball x R ∧ IsConnected V := by
        intro q
        have hqF : (q : ℂ) ∈ F := q.property.1
        have hqx : (q : ℂ) ≠ x := by
          intro heq
          have hs := mem_sphere.mp q.property.2
          rw [heq, dist_self] at hs
          linarith
        have hqball : (q : ℂ) ∈ ball x R := by
          apply mem_ball.mpr
          rw [mem_sphere.mp q.property.2]
          linarith
        have hqmem : (q : ℂ) ∈ F \ {x} := ⟨hqF, by simpa only [mem_singleton_iff] using hqx⟩
        have hNq : ball x R ∈ 𝓝[F \ {x}] (q : ℂ) :=
          nhdsWithin_le_nhds (isOpen_ball.mem_nhds hqball)
        obtain ⟨V, hV, hVsub, hVc⟩ := hlocal q hqmem _ hNq
        have hV' : V ∈ 𝓝[F] (q : ℂ) := by
          simpa only [hqx.nhdsWithin_sdiff_singleton F] using hV
        refine ⟨V, hV', ?_, hVc⟩
        intro z hz
        exact ⟨(hVsub hz).2.1, (hVsub hz).1⟩
      choose V hV hVsub hVconn using hKlocal
      have hKballs : ∀ q : K, ∃ d : ℝ, 0 < d ∧ ball (q : ℂ) d ∩ F ⊆ V q := by
        intro q
        exact Metric.mem_nhdsWithin_iff.mp (hV q)
      choose d hd hdb using hKballs
      have hcover : K ⊆ ⋃ q : K, ball (q : ℂ) (d q) := by
        intro q hq
        exact mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (hd ⟨q, hq⟩)⟩
      obtain ⟨s, hs⟩ := hKc.elim_finite_subcover (fun q : K => ball (q : ℂ) (d q))
        (fun _ => isOpen_ball) hcover
      let S : Set (Set ℂ) := (fun q : K => connectedComponentIn (F ∩ ball x R) q) '' (↑s : Set K)
      have hS : S.Finite := s.finite_toSet.image _
      have hScomp : S ⊆ connectedComponentsIn (F ∩ ball x R) := by
        rintro C ⟨q, hq, rfl⟩
        refine ⟨q, ⟨q.property.1, ?_⟩, rfl⟩
        apply mem_ball.mpr
        rw [mem_sphere.mp q.property.2]
        linarith
      have hsmall : F ∩ ball x (R / 4) ⊆ ⋃₀ S := by
        intro v hv
        have hvR : v ∈ F ∩ ball x R := ⟨hv.1, ball_subset_ball (by linarith) hv.2⟩
        let C := connectedComponentIn (F ∩ ball x R) v
        have hvC : v ∈ C := mem_connectedComponentIn hvR
        have hC : C ∈ connectedComponentsIn (F ∩ ball x R) := ⟨v, hvR, rfl⟩
        have hcross := IsConnected.ball_component_crosses_of_meets_inner_ball_of_isClosed hF hFc
          (show R / 2 < R by linarith) hout hC
          ⟨v, hvC, ball_subset_ball (by linarith) hv.2⟩
        obtain ⟨q, hqcl, hqs⟩ := hcross.1
        have hqF : q ∈ F := closure_minimal (connectedComponentIn_subset _ v |>.trans inter_subset_left)
          hFc hqcl
        have hqK : q ∈ K := ⟨hqF, hqs⟩
        obtain ⟨a, ha, hqa⟩ := mem_iUnion₂.mp (hs hqK)
        have hqaV : q ∈ V a := hdb a ⟨hqa, hqF⟩
        have haV : (a : ℂ) ∈ V a := mem_of_mem_nhdsWithin a.property.1 (hV a)
        have hVcomp : V a ⊆ connectedComponentIn (F ∩ ball x R) a :=
          (hVconn a).isPreconnected.subset_connectedComponentIn haV (hVsub a)
        have hqcomp : q ∈ connectedComponentIn (F ∩ ball x R) a := hVcomp hqaV
        have hqC : q ∈ C := by
          change q ∈ connectedComponentIn (F ∩ ball x R) v
          rw [connectedComponentIn_eq_closure_inter_of_isClosed hFc hvR]
          exact ⟨hqcl, mem_ball.mpr (by rw [mem_sphere.mp hqs]; linarith)⟩
        have heq : C = connectedComponentIn (F ∩ ball x R) a :=
          (connectedComponentIn_eq hqC).trans (connectedComponentIn_eq hqcomp).symm
        have hvcomp : v ∈ connectedComponentIn (F ∩ ball x R) a := by
          rw [← heq]
          exact hvC
        exact mem_sUnion.mpr ⟨_, ⟨a, ha, rfl⟩, hvcomp⟩
      have hCn := connectedComponentIn_mem_nhdsWithin_of_finite_cover hFc
        (show 0 < R / 4 by positivity) (show R / 4 < R by linarith) hS hScomp hsmall
      refine ⟨connectedComponentIn (F ∩ ball x R) x, hCn, ?_, ?_⟩
      · intro z hz
        have hz' := connectedComponentIn_subset (F ∩ ball x R) x hz
        exact ⟨hδN ⟨ball_subset_ball hRδ.le hz'.2, hz'.1⟩, hz'.1⟩
      · exact isConnected_connectedComponentIn_iff.mpr ⟨hp, mem_ball_self hR⟩
    · have hsub : F ⊆ {x} := by
        intro y hy
        simp only [mem_singleton_iff]
        by_contra hne
        exact hother ⟨y, hy, hne⟩
      refine ⟨{x}, mem_of_superset self_mem_nhdsWithin hsub, ?_, isConnected_singleton⟩
      rintro y (rfl : y = x)
      exact ⟨mem_of_mem_nhdsWithin hp hN, hp⟩
  · have hps : p ∈ F \ {x} := ⟨hp, by simpa only [mem_singleton_iff] using hpx⟩
    have hN' : N ∈ 𝓝[F \ {x}] p := nhdsWithin_mono _ sdiff_subset hN
    obtain ⟨V, hV, hVsub, hVc⟩ := hlocal p hps N hN'
    refine ⟨V, ?_, ?_, hVc⟩
    · simpa only [(show p ≠ x from hpx).nhdsWithin_sdiff_singleton F] using hV
    · exact hVsub.trans (inter_subset_inter_right N sdiff_subset)

/-- Under volume growth and Lemmas 6.2 and 10.5, every complementary
cluster component has locally connected complement, including at the origin. -/
theorem ae_complement_locallyConnected_of_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet Uᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_sdiff_zero_locallyConnected_of_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hlocal hgeom
  intro t ht z hz hcl U hU
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  exact IsConnected.isLocallyConnectedSet_of_sdiff_singleton hg.2.2.1
    hg.1.isClosed_compl (hlocal t ht z hz hcl U hU)

end HarmonicBalls
