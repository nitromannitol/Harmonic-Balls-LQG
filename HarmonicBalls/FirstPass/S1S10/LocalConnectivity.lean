import HarmonicBalls.Defs.Geometry

/-! # Pointwise local connectedness of `closure G` from crossing components

Used for the local-connectedness clause of the corrected Lemma 10.5 ([C48]). The crossing hypothesis is on the
components of `G ∩ B_{2r}(p)` (the open set `G`, as printed), not on those of `closure G`.
-/

namespace HarmonicBalls

open Set Metric Filter Topology

/-- A component of `G ∩ B_{2r}(p)` which meets `B_{r/3}(p)` crosses the annulus `𝔸_{r/3,2r}(p)`, when `G` is
open and connected and has a point `y` with `2r < dist y p`. The proof is a clopen argument in `G`. -/
theorem crossesAnnulus_of_meets_inner {G : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G) {p : ℂ} {r : ℝ}
    (hr : 0 < r) {y : ℂ} (hyG : y ∈ G) (hy : 2 * r < dist y p)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn (G ∩ ball p (2 * r)))
    (hmeet : (C ∩ ball p (r / 3)).Nonempty) : CrossesAnnulus C p (r / 3) (2 * r) := by
  obtain ⟨x, hxF, rfl⟩ := hC
  have hFo : IsOpen (G ∩ ball p (2 * r)) := hGo.inter isOpen_ball
  have hCsub : connectedComponentIn (G ∩ ball p (2 * r)) x ⊆ G ∩ ball p (2 * r) :=
    connectedComponentIn_subset _ _
  have hCopen : IsOpen (connectedComponentIn (G ∩ ball p (2 * r)) x) := hFo.connectedComponentIn
  have hCpre : IsPreconnected (connectedComponentIn (G ∩ ball p (2 * r)) x) :=
    isPreconnected_connectedComponentIn
  have hxC : x ∈ connectedComponentIn (G ∩ ball p (2 * r)) x := mem_connectedComponentIn hxF
  have hCball : connectedComponentIn (G ∩ ball p (2 * r)) x ⊆ ball p (2 * r) :=
    hCsub.trans inter_subset_right
  -- the closure of the component meets `F` only inside the component
  have hclF : closure (connectedComponentIn (G ∩ ball p (2 * r)) x) ∩ (G ∩ ball p (2 * r))
      ⊆ connectedComponentIn (G ∩ ball p (2 * r)) x := by
    have hs : IsPreconnected (closure (connectedComponentIn (G ∩ ball p (2 * r)) x) ∩ (G ∩ ball p (2 * r))) :=
      hCpre.subset_closure (subset_inter subset_closure hCsub) inter_subset_left
    exact hs.subset_connectedComponentIn ⟨subset_closure hxC, hxF⟩ inter_subset_right
  -- Step 1: the closure of the component meets the sphere of radius `2r`
  have hsph : (closure (connectedComponentIn (G ∩ ball p (2 * r)) x) ∩ sphere p (2 * r)).Nonempty := by
    by_contra hno
    have hlt : closure (connectedComponentIn (G ∩ ball p (2 * r)) x) ⊆ ball p (2 * r) := by
      intro z hz
      have hzcb : z ∈ closedBall p (2 * r) :=
        (closure_minimal ball_subset_closedBall isClosed_closedBall)
          (closure_mono hCball hz)
      rw [mem_closedBall] at hzcb
      rcases lt_or_eq_of_le hzcb with h | h
      · exact mem_ball.mpr h
      · exact (hno ⟨z, hz, mem_sphere.mpr h⟩).elim
    have hyout : y ∉ closure (connectedComponentIn (G ∩ ball p (2 * r)) x) := fun hy' => by
      have := mem_ball.mp (hlt hy')
      linarith
    have hGsub : G ⊆ connectedComponentIn (G ∩ ball p (2 * r)) x ∪
        (closure (connectedComponentIn (G ∩ ball p (2 * r)) x))ᶜ := by
      intro z hzG
      by_cases hz : z ∈ closure (connectedComponentIn (G ∩ ball p (2 * r)) x)
      · exact Or.inl (hclF ⟨hz, hzG, hlt hz⟩)
      · exact Or.inr hz
    obtain ⟨z, _, hzC, hzn⟩ :=
      hGc.isPreconnected _ _ hCopen isClosed_closure.isOpen_compl hGsub ⟨x, hxF.1, hxC⟩ ⟨y, hyG, hyout⟩
    exact hzn (subset_closure hzC)
  -- Step 2: the closure of the component meets the sphere of radius `r/3` (intermediate value)
  obtain ⟨w, hwcl, hwsph⟩ := hsph
  obtain ⟨u, huC, hub⟩ := hmeet
  have hpre : IsPreconnected (closure (connectedComponentIn (G ∩ ball p (2 * r)) x)) := hCpre.closure
  have hcont : ContinuousOn (fun z : ℂ => dist z p) (closure (connectedComponentIn (G ∩ ball p (2 * r)) x)) :=
    (continuous_id.dist continuous_const).continuousOn
  have hIVT := hpre.intermediate_value (subset_closure huC) hwcl hcont
  have hmem : r / 3 ∈ Icc (dist u p) (dist (w) p) := by
    have hu' : dist u p < r / 3 := mem_ball.mp hub
    have hw' : dist w p = 2 * r := mem_sphere.mp hwsph
    exact ⟨hu'.le, by rw [hw']; linarith⟩
  obtain ⟨z, hzcl, hz⟩ := hIVT hmem
  exact ⟨⟨z, hzcl, mem_sphere.mpr hz⟩, ⟨w, hwcl, hwsph⟩⟩

/-- Pointwise local connectedness of `closure G` at a point `p ∈ closure G \ G`, from finitely many crossing
components of `G ∩ B_{2r}(p)` at arbitrarily small scales `r`: the connected set `H` is the union of the closures
of the crossing components whose closure contains `p`. -/
theorem isLC_at_of_finite_crossings {G : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    {p : ℂ} (hpG : p ∈ closure G) (hpnG : p ∉ G)
    (hcross : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (crossingComponents (G ∩ ball p (2 * r)) p (r / 3) (2 * r)).Finite)
    {N : Set ℂ} (hN : N ∈ 𝓝[closure G] p) :
    ∃ V ∈ 𝓝[closure G] p, V ⊆ N ∩ closure G ∧ IsConnected V := by
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.mp hN
  obtain ⟨y, hyG⟩ := hGc.nonempty
  have hdy : 0 < dist y p := dist_pos.mpr (fun h => hpnG (h ▸ hyG))
  obtain ⟨r, hr, hrδ, hfin⟩ := hcross (min (ε / 3) (dist y p / 2)) (lt_min (by linarith) (by linarith))
  obtain ⟨hr1, hr2⟩ := lt_min_iff.mp hrδ
  have hrε : 2 * r < ε := by linarith
  have hry : 2 * r < dist y p := by linarith
  set CC := crossingComponents (G ∩ ball p (2 * r)) p (r / 3) (2 * r) with hCCdef
  have hsubF : ∀ C ∈ CC, C ⊆ G ∩ ball p (2 * r) := by
    rintro C ⟨⟨x, -, rfl⟩, -⟩
    exact connectedComponentIn_subset _ _
  have hpreC : ∀ C ∈ CC, IsPreconnected C := by
    rintro C ⟨⟨x, -, rfl⟩, -⟩
    exact isPreconnected_connectedComponentIn
  have hsubG : ∀ C ∈ CC, closure C ⊆ closure G := fun C hC =>
    closure_mono ((hsubF C hC).trans inter_subset_left)
  have hsubB : ∀ C ∈ CC, closure C ⊆ closedBall p (2 * r) := fun C hC =>
    (closure_mono ((hsubF C hC).trans inter_subset_right)).trans
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  -- the crossing components whose closure misses `p`, and their union `Z` (closed, not containing `p`)
  set CC' := {C ∈ CC | p ∉ closure C} with hCC'def
  have hCC'fin : CC'.Finite := hfin.subset (fun C hC => hC.1)
  set Z := ⋃₀ (closure '' CC') with hZdef
  have hZc : IsClosed Z :=
    Set.Finite.isClosed_sUnion (hCC'fin.image closure) (by rintro _ ⟨C, -, rfl⟩; exact isClosed_closure)
  have hpZ : p ∉ Z := by
    rintro ⟨t, ⟨C, ⟨-, hpC⟩, rfl⟩, hpt⟩
    exact hpC hpt
  obtain ⟨s₀, hs₀, hball0⟩ := Metric.isOpen_iff.mp hZc.isOpen_compl p hpZ
  set s := min s₀ (r / 3) with hsdef
  have hs_pos : 0 < s := lt_min hs₀ (by linarith)
  have hs_le : s ≤ r / 3 := min_le_right _ _
  have hs_le₀ : s ≤ s₀ := min_le_left _ _
  -- covering: points of `closure G` near `p` lie in closures of crossing components
  have hRHSc : IsClosed (⋃₀ (closure '' CC)) :=
    Set.Finite.isClosed_sUnion (hfin.image closure) (by rintro _ ⟨C, -, rfl⟩; exact isClosed_closure)
  have hcover : ∀ x ∈ closure G, dist x p < s → x ∈ ⋃₀ (closure '' CC) := by
    intro x hxK hxs
    have hxball : x ∈ ball p (r / 3) := mem_ball.mpr (lt_of_lt_of_le hxs hs_le)
    have h1 : x ∈ closure (G ∩ ball p (r / 3)) := by
      have h := (isOpen_ball (x := p) (ε := r / 3)).inter_closure (⟨hxball, hxK⟩ : x ∈ ball p (r / 3) ∩ closure G)
      rw [inter_comm] at h
      exact h
    have h2 : G ∩ ball p (r / 3) ⊆ ⋃₀ CC := by
      rintro y' ⟨hy'G, hy'b⟩
      have hy'F : y' ∈ G ∩ ball p (2 * r) :=
        ⟨hy'G, mem_ball.mpr (lt_trans (mem_ball.mp hy'b) (by linarith))⟩
      have hmemCC : connectedComponentIn (G ∩ ball p (2 * r)) y' ∈ CC :=
        ⟨⟨y', hy'F, rfl⟩, crossesAnnulus_of_meets_inner hGo hGc hr hyG hry ⟨y', hy'F, rfl⟩
          ⟨y', mem_connectedComponentIn hy'F, hy'b⟩⟩
      exact ⟨_, hmemCC, mem_connectedComponentIn hy'F⟩
    have h3 : closure (G ∩ ball p (r / 3)) ⊆ ⋃₀ (closure '' CC) := by
      refine closure_minimal ?_ hRHSc
      intro y' hy'
      obtain ⟨C, hC, hy'C⟩ := h2 hy'
      exact ⟨closure C, ⟨C, hC, rfl⟩, subset_closure hy'C⟩
    exact h3 h1
  -- the connected set `H`
  set CCp := {C ∈ CC | p ∈ closure C} with hCCpdef
  set H := ⋃₀ (closure '' CCp) with hHdef
  have hpH : p ∈ H := by
    obtain ⟨t, ⟨C, hC, rfl⟩, hpt⟩ := hcover p hpG (by rw [dist_self]; exact hs_pos)
    exact ⟨closure C, ⟨C, ⟨hC, hpt⟩, rfl⟩, hpt⟩
  have hHpre : IsPreconnected H := by
    apply isPreconnected_sUnion p (closure '' CCp)
    · rintro _ ⟨C, ⟨-, hpC⟩, rfl⟩
      exact hpC
    · rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
      exact (hpreC C hC).closure
  have hHsubG : H ⊆ closure G := by
    apply sUnion_subset
    rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
    exact hsubG C hC
  have hHball : H ⊆ closedBall p (2 * r) := by
    apply sUnion_subset
    rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
    exact hsubB C hC
  have hHnbhd : H ∈ 𝓝[closure G] p := by
    refine Metric.mem_nhdsWithin_iff.mpr ⟨s, hs_pos, ?_⟩
    rintro x ⟨hxs, hxK⟩
    have hxs' : dist x p < s := mem_ball.mp hxs
    obtain ⟨t, ⟨C, hC, rfl⟩, hxt⟩ := hcover x hxK hxs'
    by_cases hpC : p ∈ closure C
    · exact ⟨closure C, ⟨C, ⟨hC, hpC⟩, rfl⟩, hxt⟩
    · exfalso
      have hxZ : x ∈ Z := ⟨closure C, ⟨C, ⟨hC, hpC⟩, rfl⟩, hxt⟩
      have hxball0 : x ∈ ball p s₀ := mem_ball.mpr (lt_of_lt_of_le hxs' hs_le₀)
      exact hball0 hxball0 hxZ
  have hVN : H ⊆ N ∩ closure G := fun z hz =>
    ⟨hεN ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp (hHball hz)) hrε), hHsubG hz⟩, hHsubG hz⟩
  exact ⟨H, hHnbhd, hVN, ⟨p, hpH⟩, hHpre⟩

end HarmonicBalls
