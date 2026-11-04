import HarmonicBalls.Proofs.Sec10.HoleCompactPersistence

/-! # Compact connected enclosures inside planar domains

Compact subsets of an open connected planar set lie in compact connected
subsets of the same set. This allows persistence estimates for continua to
be applied to compact subsets of complementary components.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A compact subset of an open connected planar set is contained in a compact
connected subset of that set. -/
theorem exists_compact_connected_enclosure {U C : Set ℂ}
    (hUopen : IsOpen U) (hUconn : IsConnected U) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧ C ⊆ K ∧ K ⊆ U := by
  classical
  obtain ⟨p, hp⟩ := hUconn.nonempty
  have hpath : IsPathConnected U := hUopen.isConnected_iff_isPathConnected.mp hUconn
  have hlocal : ∀ x : C, ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧
      p ∈ K ∧ x.1 ∈ interior K ∧ K ⊆ U := by
    intro x
    have hx : x.1 ∈ U := hCU x.2
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen x.1 hx
    obtain ⟨γ, hγ⟩ := hpath.joinedIn p hp x.1 hx
    let K := range γ ∪ closedBall x.1 (ε / 2)
    have hγU : range γ ⊆ U := range_subset_iff.mpr hγ
    have hballU : closedBall x.1 (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    refine ⟨K, (isCompact_range γ.continuous).union (isCompact_closedBall _ _), ?_, ?_, ?_, ?_⟩
    · exact (isConnected_range γ.continuous).union
        ⟨x.1, γ.target_mem_range, mem_closedBall_self (half_pos hε).le⟩
        (isConnected_closedBall (half_pos hε).le)
    · exact mem_union_left _ γ.source_mem_range
    · apply mem_interior_iff_mem_nhds.mpr
      apply mem_of_superset (ball_mem_nhds x.1 (half_pos hε))
      exact fun y hy => mem_union_right _ (ball_subset_closedBall hy)
    · exact union_subset hγU hballU
  choose K hKcompact hKconn hpK hxK hKU using hlocal
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover (fun x : C => interior (K x))
    (fun _ => isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxK ⟨x, hx⟩⟩)
  have hfinite : ∀ F : Finset C, ∃ L : Set ℂ, IsCompact L ∧ IsConnected L ∧
      p ∈ L ∧ (⋃ x ∈ F, K x) ⊆ L ∧ L ⊆ U := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        exact ⟨{p}, isCompact_singleton, isConnected_singleton, by simp, by simp, by simpa⟩
    | @insert x F hx ih =>
        obtain ⟨L, hLc, hLconn, hpL, hFL, hLU⟩ := ih
        refine ⟨K x ∪ L, (hKcompact x).union hLc,
          (hKconn x).union ⟨p, hpK x, hpL⟩ hLconn, mem_union_left _ (hpK x), ?_,
          union_subset (hKU x) hLU⟩
        intro y hy
        obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact mem_union_left _ hyz
        · exact mem_union_right _ (hFL (mem_iUnion₂.mpr ⟨z, hz, hyz⟩))
  obtain ⟨L, hLc, hLconn, _, hFL, hLU⟩ := hfinite F
  refine ⟨L, hLc, hLconn, ?_, hLU⟩
  intro x hx
  obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.mp (hF hx)
  exact hFL (mem_iUnion₂.mpr ⟨y, hyF, interior_subset hxy⟩)

universe u

/-- Every compact subset of a bounded hole remains in one descendant for a
right interval, with no connectedness hypothesis on the subset. -/
theorem ae_cluster_hole_compact_subset_persists
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ C : Set ℂ, IsCompact C → C ⊆ U →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ C ⊆ V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_compact_connected_subset_persists hI2 hvolume h61 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro t ht z hz U hU hb C hC hCU
  have hUopen : IsOpen U := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  have hUconn : IsConnected U := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact isConnected_connectedComponentIn_iff.mpr hx
  obtain ⟨K, hK, hKconn, hCK, hKU⟩ := exists_compact_connected_enclosure hUopen hUconn hC hCU
  obtain ⟨δ, hδ, hdesc⟩ := hpersist t ht z hz U hU hb K hK hKconn hKU
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hV, hVb, hKV, hVU⟩ := hdesc s hs
  exact ⟨V, hV, hVb, hCK.trans hKV, hVU⟩

/-- A bounded hole with mass greater than `a` has descendants of mass
larger than `a` throughout a right interval. -/
theorem ae_cluster_hole_mass_persists
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ a : ℝ≥0∞, a < μ ω U →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U ∧ a < μ ω V := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_cluster_hole_compact_subset_persists hI2 hvolume h61 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hV hpersist
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  intro t ht z hz U hU hb a ha
  have hUopen : IsOpen U := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  obtain ⟨C, hCU, hCcompact, haC⟩ := hUopen.exists_lt_isCompact ha
  obtain ⟨δ, hδ, hdesc⟩ := hpersist t ht z hz U hU hb C hCcompact hCU
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hV, hVb, hCV, hVU⟩ := hdesc s hs
  exact ⟨V, hV, hVb, hVU, haC.trans_le (measure_mono hCV)⟩

end HarmonicBalls
