import HarmonicBalls.Proofs.Sec10.FiniteCrossingsLocalConnectivity

/-!
# Boundary bumping for closed connected sets

Compactness is only needed near the chosen component. This yields boundary
contact in a ball even when the closed connected set is unbounded.
-/

namespace HarmonicBalls

open Metric Set Filter Topology

/-- Boundary bumping in a connected normal space for an open set with compact
closure. -/
theorem closure_connectedComponentIn_inter_compl_nonempty_of_compact_closure
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X] [ConnectedSpace X]
    {O : Set X} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hproper : O ≠ univ) {x : X} (hx : x ∈ O) :
    (closure (connectedComponentIn O x) ∩ Oᶜ).Nonempty := by
  classical
  let C := connectedComponentIn O x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCO : C ⊆ O := connectedComponentIn_subset O x
  by_contra h
  have hclO : closure C ⊆ O := by
    intro y hy
    by_contra hyO
    exact h ⟨y, hy, hyO⟩
  have hclC : closure C ⊆ C := by
    intro y hy
    have hconn : IsPreconnected (C ∪ {y}) :=
      isPreconnected_connectedComponentIn.subset_closure subset_union_left
        (union_subset subset_closure (singleton_subset_iff.mpr hy))
    have hsub : C ∪ {y} ⊆ O := union_subset hCO (singleton_subset_iff.mpr (hclO hy))
    exact hconn.subset_connectedComponentIn (mem_union_left _ hxC) hsub (mem_union_right _ rfl)
  have hCc : IsClosed C := closure_subset_iff_isClosed.mp hclC
  obtain ⟨U, V, hU, hV, hCU, hOV, hUV⟩ :=
    normal_separation hCc hO.isClosed_compl (disjoint_compl_right.mono_left hCO)
  have hclUO : closure U ⊆ O := by
    have hclUV : closure U ⊆ Vᶜ :=
      closure_minimal (fun z hz hzV => Set.disjoint_left.mp hUV hz hzV) hV.isClosed_compl
    intro z hz
    by_contra hzO
    exact hclUV hz (hOV hzO)
  let K := closure U
  have hKcompact : IsCompact K := hOc.of_isClosed_subset isClosed_closure
    (hclUO.trans subset_closure)
  have hCK : C ⊆ K := hCU.trans subset_closure
  have hxK : x ∈ K := hCK hxC
  have hcomponent : connectedComponentIn K x = C := by
    apply Subset.antisymm
    · exact connectedComponentIn_mono x hclUO
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxC hCK
  have hcomponentU : connectedComponentIn K x ⊆ U := by rw [hcomponent]; exact hCU
  obtain ⟨W, hWopen, hCW, hWU, hWclosed⟩ :=
    exists_open_inter_compact_component_subset hKcompact hxK hU hcomponentU
  have heq : K ∩ W = U ∩ W := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨hWU hz, hz.2⟩
    · exact inter_subset_inter_left W subset_closure
  have hopen : IsOpen (K ∩ W) := by rw [heq]; exact hU.inter hWopen
  have hclopen : IsClopen (K ∩ W) := ⟨hWclosed, hopen⟩
  have huniv : K ∩ W = univ := hclopen.eq_univ ⟨x, hCW (by rw [hcomponent]; exact hxC)⟩
  have hOuniv : O = univ := univ_subset_iff.mp (by
    rw [← huniv]
    exact hWU.trans (subset_closure.trans hclUO))
  exact hproper hOuniv

/-- A component of a closed connected planar set inside a ball has closure
meeting the exterior of that ball whenever the set meets the exterior. -/
theorem IsConnected.closure_ball_component_meets_compl
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F)
    {w y : ℂ} {R : ℝ} (hout : (F \ ball w R).Nonempty)
    (hy : y ∈ F ∩ ball w R) :
    (closure (connectedComponentIn (F ∩ ball w R) y) ∩ (F \ ball w R)).Nonempty := by
  let : ConnectedSpace F := isConnected_iff_connectedSpace.mp hF
  let y' : F := ⟨y, hy.1⟩
  let O : Set F := Subtype.val ⁻¹' ball w R
  have hO : IsOpen O := isOpen_ball.preimage continuous_subtype_val
  have hcompact : IsCompact (closure O) := by
    have hk : IsCompact ((Subtype.val : F → ℂ) ⁻¹' closedBall w R) :=
      hFc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall w R)
    apply hk.of_isClosed_subset isClosed_closure
    exact closure_minimal (fun z hz => ball_subset_closedBall hz)
      (isClosed_closedBall.preimage continuous_subtype_val)
  have hproper : O ≠ univ := by
    obtain ⟨z, hzF, hzout⟩ := hout
    intro heq
    have hz : (⟨z, hzF⟩ : F) ∈ O := by rw [heq]; trivial
    exact hzout hz
  obtain ⟨z, hzcl, hzout⟩ :=
    closure_connectedComponentIn_inter_compl_nonempty_of_compact_closure
      hO hcompact hproper (show y' ∈ O from hy.2)
  have himage : Subtype.val '' connectedComponentIn O y' ⊆ connectedComponentIn (F ∩ ball w R) y := by
    have hconnected : IsPreconnected (Subtype.val '' connectedComponentIn O y') :=
      isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn
    have hyimage : y ∈ Subtype.val '' connectedComponentIn O y' :=
      ⟨y', mem_connectedComponentIn hy.2, rfl⟩
    have hsub : Subtype.val '' connectedComponentIn O y' ⊆ F ∩ ball w R := by
      rintro v ⟨a, ha, rfl⟩
      exact ⟨a.property, connectedComponentIn_subset O y' ha⟩
    exact hconnected.subset_connectedComponentIn hyimage hsub
  have hzcl' : (z : ℂ) ∈ closure (connectedComponentIn (F ∩ ball w R) y) :=
    closure_mono himage (image_closure_subset_closure_image continuous_subtype_val ⟨z, hzcl, rfl⟩)
  exact ⟨z, hzcl', z.property, hzout⟩

/-- Every ball component of a closed continuum that meets a smaller ball
crosses its two boundary circles, if the continuum also meets the exterior. -/
theorem IsConnected.ball_component_crosses_of_meets_inner_ball_of_isClosed
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F)
    {x : ℂ} {r R : ℝ} (hrR : r < R)
    (hout : (F \ ball x R).Nonempty)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn (F ∩ ball x R))
    (hinner : (C ∩ ball x r).Nonempty) : CrossesAnnulus C x r R := by
  obtain ⟨y, hy, hyC⟩ := hC
  obtain ⟨z, hzC, hzr⟩ := hinner
  have hconn : IsConnected C := by rw [← hyC]; exact isConnected_connectedComponentIn_iff.mpr hy
  obtain ⟨q, hqcl, _, hqout⟩ :=
    IsConnected.closure_ball_component_meets_compl hF hFc hout hy
  have hqcl' : q ∈ closure C := by simpa only [hyC] using hqcl
  have hsub : closure C ⊆ closedBall x R := by
    apply closure_minimal _ isClosed_closedBall
    intro v hv
    rw [← hyC] at hv
    exact ball_subset_closedBall (connectedComponentIn_subset _ y hv).2
  have hqR : dist q x = R := le_antisymm (mem_closedBall.mp (hsub hqcl'))
    (le_of_not_gt (fun hlt => hqout (mem_ball.mpr hlt)))
  obtain ⟨p, hpC, hpr⟩ := hconn.closure.isPreconnected.intermediate_value
    (subset_closure hzC) hqcl' (continuous_id.dist continuous_const).continuousOn
    ⟨(mem_ball.mp hzr).le, by simpa only [id_eq, hqR] using hrR.le⟩
  exact ⟨⟨p, hpC, mem_sphere.mpr hpr⟩, ⟨q, hqcl', mem_sphere.mpr hqR⟩⟩

/-- A closed connected planar set is locally connected if its crossing
families are finite at arbitrarily small scales around each frontier point,
provided it meets the exterior of the corresponding balls. -/
theorem IsConnected.isLocallyConnectedSet_of_finite_crossings_of_isClosed
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F)
    (hsmall : ∀ x ∈ F ∩ frontier F, ∀ δ : ℝ, 0 < δ → ∃ r R : ℝ,
      0 < r ∧ r < R ∧ R < δ ∧ (F \ ball x R).Nonempty ∧
        (crossingComponents (F ∩ ball x R) x r R).Finite) :
    IsLocallyConnectedSet F := by
  apply isLocallyConnectedSet_of_finite_crossings_and_escape hFc
  intro x hx δ hδ
  obtain ⟨r, R, hr, hrR, hRδ, hout, hfinite⟩ := hsmall x hx δ hδ
  refine ⟨r, R, hr, hrR, hRδ, hfinite, ?_⟩
  intro C hC hinner
  exact IsConnected.ball_component_crosses_of_meets_inner_ball_of_isClosed
    hF hFc hrR hout hC hinner

/-- A closed connected planar set is locally connected when its ball-crossing
families are finite at arbitrarily small scales around every frontier point. -/
theorem IsConnected.isLocallyConnectedSet_of_small_finite_crossings
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsClosed F)
    (hsmall : ∀ x ∈ F ∩ frontier F, ∀ δ : ℝ, 0 < δ → ∃ r R : ℝ,
      0 < r ∧ r < R ∧ R < δ ∧
        (crossingComponents (F ∩ ball x R) x r R).Finite) :
    IsLocallyConnectedSet F := by
  classical
  by_cases hnon : F.Nontrivial
  · apply IsConnected.isLocallyConnectedSet_of_finite_crossings_of_isClosed hF hFc
    intro x hx δ hδ
    obtain ⟨y, hyF, hyx⟩ := hnon.exists_ne x
    have hd : 0 < dist y x := dist_pos.mpr hyx
    obtain ⟨r, R, hr, hrR, hR, hfinite⟩ :=
      hsmall x hx (min δ (dist y x)) (lt_min hδ hd)
    refine ⟨r, R, hr, hrR, hR.trans_le (min_le_left _ _), ?_, hfinite⟩
    refine ⟨y, hyF, ?_⟩
    intro hyball
    have hylt := mem_ball.mp hyball
    have hRd := hR.trans_le (min_le_right _ _)
    exact (not_lt_of_ge hRd.le) hylt
  · intro x hx N hN
    have hsub : F ⊆ {x} := by
      intro y hy
      exact mem_singleton_iff.mpr ((Set.not_nontrivial_iff.mp hnon) hy hx)
    refine ⟨{x}, mem_of_superset self_mem_nhdsWithin hsub, ?_, isConnected_singleton⟩
    rintro y (rfl : y = x)
    exact ⟨mem_of_mem_nhdsWithin hx hN, hx⟩

end HarmonicBalls
