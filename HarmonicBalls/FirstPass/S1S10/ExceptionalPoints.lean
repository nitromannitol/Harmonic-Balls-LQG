import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Proofs.Sec10.ContinuumBoundaryBumping

/-! # Removing finitely many exceptional points from local connectedness

A compact connected `K ⊂ ℂ` which is locally connected (relative to `K`) at every point outside a finite set `E` is
locally connected at every point. This is the step of the corrected Lemma 10.5 ([C48]) which removes the finite
exceptional set `E`. Proof: at a point `p` where the local condition fails, the components of `K ∩ B_a(p)` cannot be
finitely many meeting `B_{s₁}(p)`; boundary bumping and the intermediate value theorem give points on a sphere
`∂B_{s₀}(p)` (with `s₀` avoiding the distances of `E` from `p`) in infinitely many distinct components; a subsequence
converges to a non-exceptional point, where local connectedness forces all but one of these components to coincide.
-/

namespace HarmonicBalls

open Set Metric Filter Topology

/-- The closure of a connected component of `F` is relatively closed in `F`. -/
theorem closure_connectedComponentIn_inter_subset {F : Set ℂ} {x : ℂ} (hx : x ∈ F) :
    closure (connectedComponentIn F x) ∩ F ⊆ connectedComponentIn F x := by
  have hCpre : IsPreconnected (connectedComponentIn F x) := isPreconnected_connectedComponentIn
  have hCsub : connectedComponentIn F x ⊆ F := connectedComponentIn_subset _ _
  have hs : IsPreconnected (closure (connectedComponentIn F x) ∩ F) :=
    hCpre.subset_closure (subset_inter subset_closure hCsub) inter_subset_left
  exact hs.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx), hx⟩ inter_subset_right

/-- A component `C` of `F` is the component of each of its points. -/
theorem connectedComponentIn_eq_of_mem {F C : Set ℂ} (hC : C ∈ connectedComponentsIn F) {x : ℂ}
    (hx : x ∈ C) : connectedComponentIn F x = C := by
  obtain ⟨u, -, rfl⟩ := hC
  exact (connectedComponentIn_eq hx).symm

/-- Boundary bumping with intermediate values: a component `C` of `K ∩ B_a(p)` containing a point of `B_{s₁}(p)`
has a closure point on each sphere `∂B_{s₀}(p)` with `s₁ < s₀ < a`. -/
theorem exists_point_on_sphere_of_component {K : Set ℂ} (hKc : IsCompact K) (hKconn : IsConnected K)
    {p z0 : ℂ} {a s0 s1 : ℝ} (hs1s0 : s1 < s0) (hs0a : s0 < a) (hz0K : z0 ∈ K) (hz0 : a ≤ dist z0 p)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn (K ∩ ball p a)) {y : ℂ} (hyC : y ∈ C)
    (hy : y ∈ ball p s1) : ∃ w ∈ closure C, dist w p = s0 := by
  obtain ⟨u, -, rfl⟩ := hC
  have hyX : y ∈ K ∩ ball p a := connectedComponentIn_subset _ _ hyC
  rw [connectedComponentIn_eq hyC]
  have hz0out : z0 ∉ ball p a := fun h => absurd (mem_ball.mp h) (not_lt.mpr hz0)
  obtain ⟨z, hzcl, -, hzout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hKconn hKc isOpen_ball ⟨z0, hz0K, hz0out⟩ hyX
  have hza : a ≤ dist z p := not_lt.mp (fun h => hzout (mem_ball.mpr h))
  have hpre : IsPreconnected (closure (connectedComponentIn (K ∩ ball p a) y)) :=
    isPreconnected_connectedComponentIn.closure
  have hcont : ContinuousOn (fun w : ℂ => dist w p) (closure (connectedComponentIn (K ∩ ball p a) y)) :=
    (continuous_id.dist continuous_const).continuousOn
  have hyc : y ∈ closure (connectedComponentIn (K ∩ ball p a) y) :=
    subset_closure (mem_connectedComponentIn hyX)
  have hy' : dist y p < s1 := mem_ball.mp hy
  have hs0mem : s0 ∈ Icc (dist y p) (dist z p) :=
    ⟨(hy'.trans hs1s0).le, (hs0a.trans_le hza).le⟩
  obtain ⟨w, hwc, hw⟩ := hpre.intermediate_value hyc hzcl hcont hs0mem
  exact ⟨w, hwc, hw⟩

/-- If `p` has no connected neighbourhood in `K` inside `B_a(p) ∩ K`, then for each `0 < s₁ < a` infinitely many
components of `K ∩ B_a(p)` meet `B_{s₁}(p)`: otherwise the component of `p` is a connected neighbourhood of `p`. -/
theorem infinite_components_meet_ball {K : Set ℂ} {p : ℂ} {a s1 : ℝ} (hpK : p ∈ K) (ha : 0 < a)
    (hs1 : 0 < s1) (hs1a : s1 < a)
    (hnoC : ∀ V ∈ 𝓝[K] p, V ⊆ ball p a ∩ K → ¬ IsConnected V) :
    {C ∈ connectedComponentsIn (K ∩ ball p a) | (C ∩ ball p s1).Nonempty}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set X := K ∩ ball p a with hX
  set 𝒮 := {C ∈ connectedComponentsIn X | (C ∩ ball p s1).Nonempty} with h𝒮
  set 𝒮' := {C ∈ 𝒮 | p ∉ C} with h𝒮'
  have hpX : p ∈ X := ⟨hpK, mem_ball_self ha⟩
  have hZc : IsClosed (⋃₀ (closure '' 𝒮')) :=
    Set.Finite.isClosed_sUnion ((hfin.subset (fun C hC => hC.1)).image closure)
      (by rintro _ ⟨C, -, rfl⟩; exact isClosed_closure)
  have hpZ : p ∉ ⋃₀ (closure '' 𝒮') := by
    rintro ⟨t, ⟨C, ⟨hC, hpC⟩, rfl⟩, hpt⟩
    obtain ⟨x, hxX, rfl⟩ := hC.1
    exact hpC (closure_connectedComponentIn_inter_subset hxX ⟨hpt, hpX⟩)
  obtain ⟨ρ, hρ, hballρ⟩ := Metric.isOpen_iff.mp hZc.isOpen_compl p hpZ
  have hδpos : 0 < min s1 ρ := lt_min hs1 hρ
  have hC0 : K ∩ ball p (min s1 ρ) ⊆ connectedComponentIn X p := by
    rintro x ⟨hxK, hxδ⟩
    have hxs1 : x ∈ ball p s1 := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hxδ) (min_le_left _ _))
    have hxX : x ∈ X := ⟨hxK, mem_ball.mpr (lt_trans (mem_ball.mp hxs1) hs1a)⟩
    have hmem : connectedComponentIn X x ∈ 𝒮 :=
      ⟨mem_image_of_mem _ hxX, x, mem_connectedComponentIn hxX, hxs1⟩
    by_cases hpx : p ∈ connectedComponentIn X x
    · rw [← connectedComponentIn_eq hpx]
      exact mem_connectedComponentIn hxX
    · exfalso
      have hmem' : connectedComponentIn X x ∈ 𝒮' := ⟨hmem, hpx⟩
      have hxZ : x ∈ ⋃₀ (closure '' 𝒮') :=
        ⟨closure (connectedComponentIn X x), ⟨_, hmem', rfl⟩,
          subset_closure (mem_connectedComponentIn hxX)⟩
      have hxρ : x ∈ ball p ρ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hxδ) (min_le_right _ _))
      exact hballρ hxρ hxZ
  have hnhds : connectedComponentIn X p ∈ 𝓝[K] p :=
    Metric.mem_nhdsWithin_iff.mpr ⟨min s1 ρ, hδpos, fun x hx => hC0 ⟨hx.2, hx.1⟩⟩
  have hsub : connectedComponentIn X p ⊆ ball p a ∩ K := fun z hz =>
    ⟨(connectedComponentIn_subset _ _ hz).2, (connectedComponentIn_subset _ _ hz).1⟩
  exact hnoC _ hnhds hsub ⟨⟨p, mem_connectedComponentIn hpX⟩, isPreconnected_connectedComponentIn⟩

/-- E-removal: a compact connected `K ⊂ ℂ` which is locally connected relative to `K` at every point outside a
finite set `E` is locally connected relative to `K` at every point. -/
theorem isLocallyConnectedSet_of_finite_exceptions {K : Set ℂ} (hKc : IsCompact K) (hKconn : IsConnected K)
    {E : Set ℂ} (hE : E.Finite)
    (hoff : ∀ q ∈ K, q ∉ E → ∀ N ∈ 𝓝[K] q, ∃ V ∈ 𝓝[K] q, V ⊆ N ∩ K ∧ IsConnected V) :
    IsLocallyConnectedSet K := by
  intro p hpK N hN
  by_contra hnot
  have hpN : p ∈ N := mem_of_mem_nhdsWithin hpK hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.mp hN
  by_cases hz : ∃ z ∈ K, z ≠ p
  · obtain ⟨z0, hz0K, hz0p⟩ := hz
    have hd0 : 0 < dist z0 p := dist_pos.mpr hz0p
    set a := min (ε / 2) (dist z0 p) with ha_def
    have ha : 0 < a := lt_min (by linarith) hd0
    have haε : a < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have had : a ≤ dist z0 p := min_le_right _ _
    have hinf1 : (Ioo (a / 3) (2 * a / 3) \ (fun e => dist e p) '' E).Infinite :=
      (Set.Ioo_infinite (by linarith)).sdiff (hE.image _)
    obtain ⟨s0, hs0mem, hs0E⟩ := hinf1.nonempty
    obtain ⟨hs0lo, hs0hi⟩ := hs0mem
    have hs1s0 : a / 3 < s0 := hs0lo
    have hs0a : s0 < a := by linarith
    have hnoC : ∀ V ∈ 𝓝[K] p, V ⊆ ball p a ∩ K → ¬ IsConnected V := fun V hV hVsub hVc =>
      hnot ⟨V, hV, fun x hx => ⟨hεN ⟨mem_ball.mpr (lt_trans (mem_ball.mp (hVsub hx).1) haε), (hVsub hx).2⟩,
        (hVsub hx).2⟩, hVc⟩
    have hinf := infinite_components_meet_ball (s1 := a / 3) hpK ha (by linarith) (by linarith) hnoC
    set emb := Set.Infinite.natEmbedding _ hinf with hemb
    have hsubX : ∀ C ∈ connectedComponentsIn (K ∩ ball p a), C ⊆ K ∩ ball p a := by
      rintro C ⟨u, -, rfl⟩
      exact connectedComponentIn_subset _ _
    -- for each `n`: a sphere point of the closure of the `n`-th component, and a nearby point of that component
    have hpts : ∀ n : ℕ, ∃ w : ℂ, (w ∈ closure (emb n).1 ∧ dist w p = s0) ∧
        ∃ c ∈ (emb n).1, dist w c < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨hCn, y, hyC, hyb⟩ := (emb n).2
      obtain ⟨w, hwc, hw⟩ :=
        exists_point_on_sphere_of_component hKc hKconn hs1s0 hs0a hz0K had hCn hyC hyb
      obtain ⟨c, hcC, hcd⟩ := Metric.mem_closure_iff.mp hwc (1 / ((n : ℝ) + 1)) (by positivity)
      exact ⟨w, ⟨hwc, hw⟩, c, hcC, hcd⟩
    choose w hw c hc hcd using hpts
    -- a convergent subsequence of the sphere points
    obtain ⟨w₀, hw₀S, φ, hφ, hlim⟩ :=
      (isCompact_sphere p s0).tendsto_subseq (fun n => mem_sphere.mpr (hw n).2)
    have hCK : ∀ n, closure (emb n).1 ⊆ K := fun n =>
      closure_minimal ((hsubX _ (emb n).2.1).trans inter_subset_left) hKc.isClosed
    have hw₀K : w₀ ∈ K := hKc.isClosed.mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun n => hCK (φ n) (hw (φ n)).1)
    have hdist₀ : dist w₀ p = s0 := mem_sphere.mp hw₀S
    have hw₀E : w₀ ∉ E := fun h => hs0E ⟨w₀, h, hdist₀⟩
    -- local connectedness at the non-exceptional limit point `w₀`
    have hw₀ball : w₀ ∈ ball p a := mem_ball.mpr (by rw [hdist₀]; exact hs0a)
    obtain ⟨V, hV, hVsub, hVc⟩ := hoff w₀ hw₀K hw₀E (ball p a)
      (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hw₀ball))
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhdsWithin_iff.mp hV
    have hev1 : ∀ᶠ n in atTop, dist (w (φ n)) w₀ < r / 2 :=
      Metric.tendsto_nhds.mp hlim (r / 2) (by linarith)
    have hev2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < r / 2 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith))
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
    have hin : ∀ n ≥ N0, c (φ n) ∈ V := by
      intro n hn
      obtain ⟨h1, h2⟩ := hN0 n hn
      have hφn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
      have hbound : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 : dist (c (φ n)) (w (φ n)) < 1 / ((φ n : ℝ) + 1) := by
        rw [dist_comm]; exact hcd (φ n)
      have h4 : dist (c (φ n)) w₀ < r := by
        linarith [dist_triangle (c (φ n)) (w (φ n)) w₀]
      exact hrV ⟨mem_ball.mpr h4, (hsubX _ (emb (φ n)).2.1 (hc (φ n))).1⟩
    -- two indices give the same component, contradicting the injectivity of the enumeration
    have hVX : V ⊆ K ∩ ball p a := fun x hx => ⟨(hVsub hx).2, (hVsub hx).1⟩
    have hsubi : V ⊆ (emb (φ N0)).1 := by
      have h := (IsConnected.isPreconnected hVc).subset_connectedComponentIn (hin N0 le_rfl) hVX
      rwa [connectedComponentIn_eq_of_mem (emb (φ N0)).2.1 (hc (φ N0))] at h
    have hsubj : c (φ (N0 + 1)) ∈ (emb (φ N0)).1 := hsubi (hin (N0 + 1) (by omega))
    have heq : (emb (φ (N0 + 1))).1 = (emb (φ N0)).1 :=
      (connectedComponentIn_eq_of_mem (emb (φ (N0 + 1))).2.1 (hc (φ (N0 + 1)))).symm.trans
        (connectedComponentIn_eq_of_mem (emb (φ N0)).2.1 hsubj)
    have hij : φ (N0 + 1) = φ N0 := emb.injective (Subtype.ext heq)
    have := hφ.injective hij
    omega
  · -- `K = {p}`: the whole set is a connected neighbourhood of `p`
    apply hnot
    refine ⟨K, self_mem_nhdsWithin, fun x hx => ⟨?_, hx⟩, hKconn⟩
    by_cases hxp : x = p
    · rw [hxp]; exact hpN
    · exact (hz ⟨x, hx, hxp⟩).elim

end HarmonicBalls
