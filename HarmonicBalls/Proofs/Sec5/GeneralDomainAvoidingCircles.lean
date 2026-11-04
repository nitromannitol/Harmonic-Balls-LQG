import HarmonicBalls.Proofs.Sec5.GeneralDomainHarmonicComparison
import Mathlib.Topology.TietzeExtension

/-! # Circles avoiding locally finite-rank deletions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Arbitrarily small circles centred at any point avoid a countable set. -/
theorem exists_radius_sphere_disjoint_of_countable
    {K : Set ℂ} (hK : K.Countable) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) ε, Disjoint (sphere c r) K := by
  by_contra h
  push Not at h
  have hsub : Ioo (0 : ℝ) ε ⊆ (fun y : ℂ => dist y c) '' K := by
    intro r hr
    have hn : ¬ Disjoint (sphere c r) K := h r hr
    obtain ⟨y, hyr, hyK⟩ := Set.not_disjoint_iff.mp hn
    exact ⟨y, hyK, mem_sphere.mp hyr⟩
  have hc : (Ioo (0 : ℝ) ε).Countable := (hK.image _).mono hsub
  exact (not_le_of_gt hε) (Cardinal.Real.Ioo_countable_iff.mp hc)

/-- A locally finite-rank deletion can be avoided by arbitrarily small circles
whose closed interiors stay inside the ambient open set. -/
theorem exists_radius_sphere_disjoint_of_locallyFiniteRankOn
    {U K : Set ℂ} (hU : IsOpen U) (hK : LocallyFiniteRankOn U K)
    {c : ℂ} (hc : c ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) ε, closedBall c r ⊆ U ∧ Disjoint (sphere c r) K := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU c hc
  have hmin : 0 < min ε δ := lt_min hε hδ
  obtain ⟨r, hr, hdis⟩ := exists_radius_sphere_disjoint_of_countable
    (countable_inter_open_of_locallyFiniteRankOn hU hK) c hmin
  have hrδ : r < δ := hr.2.trans_le (min_le_right _ _)
  have hrε : r < ε := hr.2.trans_le (min_le_left _ _)
  have hcl : closedBall c r ⊆ U := (closedBall_subset_ball hrδ).trans hδU
  refine ⟨r, ⟨hr.1, hrε⟩, hcl, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hyK
  exact Set.disjoint_left.mp hdis hy ⟨hyK, hcl (sphere_subset_closedBall hy)⟩

/-- Harmonic comparison across a thin deletion with boundary-continuous data.
The harmonicity hypotheses are only needed in the open disc. -/
theorem harmonic_sub_le_of_locallyFiniteRankOn_ball_of_continuous_boundary
    {R r C M : ℝ} {c x : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hhc : ContinuousOn h (closedBall c r \ K))
    (hh : HarmonicOnNhd h (ball c r \ K))
    (hqc : ContinuousOn q (closedBall c r)) (hq : HarmonicOnNhd q (ball c r))
    (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball c r \ K) : h x - q x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
    exists_capped_barrier_of_locallyFiniteRankOn hKclosed hK
      (isCompact_closedBall _ _) hball hx.2 hM hε
  have hbc' : ContinuousOn b (closedBall c r) := hbc.mono (hball.trans ball_subset_closedBall)
  let D := ball c r \ K
  let f : ℂ → ℝ := fun y => (h y - q y) - b y
  have hdc : D ⊆ closedBall c r \ K :=
    fun _ hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
  have hDopen : IsOpen D := isOpen_ball.sdiff hKclosed
  have hDR : D ⊆ ball (0 : ℂ) R := hdc.trans (sdiff_subset.trans hball)
  have hbs : IsSuperharmonicOn D b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbc'.mono (hdc.trans sdiff_subset)) (hbΔ.mono_set hDR)
  have hfc : ContinuousOn f (closedBall c r \ K) :=
    (hhc.sub (hqc.mono sdiff_subset)).sub (hbc'.mono sdiff_subset)
  have hsub : IsSubharmonicOn D f := by
    have hhq := hh.sub (hq.mono sdiff_subset)
    have hhqb := HarmonicOnNhd.sub_superharmonic hhq (hbc'.mono (hdc.trans sdiff_subset)) hbs
    convert hhqb using 1
  have hne : ∀ a ∈ K, ∀ᶠ y in 𝓝[D] a, f y < C := by
    intro a ha
    by_cases haρ : a ∈ closedBall c r
    · have hba := hbar a ⟨ha, haρ⟩
      have hba' : ∀ᶠ y in 𝓝[closedBall c r] a, M < b y :=
        (hbc' a haρ).eventually (Ioi_mem_nhds hba)
      filter_upwards [hnear a ha, hba'.filter_mono
        (nhdsWithin_mono a (hdc.trans sdiff_subset))] with y hy hyb
      dsimp [f]
      linarith
    · have haway : ∀ᶠ y in 𝓝 a, y ∉ closedBall c r :=
        isClosed_closedBall.isOpen_compl.mem_nhds haρ
      filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyD
      exact (hy (ball_subset_closedBall hyD.1)).elim
  have hle := isSubharmonicOn_ball_sdiff_le_of_eventually_lt hKclosed hfc hsub hne
    (fun y hy hyK => by dsimp [f]; linarith [hbd y hy hyK, hbn y]) x hx
  dsimp [f] at hle
  linarith

/-- A bounded punctured harmonic function agrees with a boundary-continuous
harmonic replacement having the same undeleted boundary values. -/
theorem harmonic_eq_of_locallyFiniteRankOn_ball_of_continuous_boundary
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hhc : ContinuousOn h (closedBall c r \ K))
    (hh : HarmonicOnNhd h (ball c r \ K))
    (hqc : ContinuousOn q (closedBall c r)) (hq : HarmonicOnNhd q (ball c r))
    (hM : 0 ≤ M) (hbound : ∀ y ∈ ball c r \ K, |h y - q y| ≤ M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y = q y)
    {x : ℂ} (hx : x ∈ ball c r \ K) : h x = q x := by
  have hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ 0 + M := by
    intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using (le_abs_self (h y - q y)).trans (hbound y hy)
  have hnear' : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, (-h) y - (-q) y ≤ 0 + M := by
    intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hb := (neg_le_abs (h y - q y)).trans (hbound y hy)
    simp only [Pi.neg_apply]
    linarith
  have hle := harmonic_sub_le_of_locallyFiniteRankOn_ball_of_continuous_boundary
    hball hKclosed hK hhc hh hqc hq hM hnear
    (fun y hy hyK => by rw [hbd y hy hyK]; simp) hx
  have hge := harmonic_sub_le_of_locallyFiniteRankOn_ball_of_continuous_boundary
    hball hKclosed hK hhc.neg hh.neg hqc.neg hq.neg hM hnear'
    (fun y hy hyK => by simp [hbd y hy hyK]) hx
  simp only [Pi.neg_apply] at hge
  linarith

/-- A bounded harmonic function on a punctured disc has a harmonic replacement
when the boundary circle avoids the deletion. -/
theorem exists_harmonic_replacement_of_locallyFiniteRankOn_ball
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h : ℂ → ℝ}
    (hr : 0 < r) (hball : closedBall c r ⊆ ball (0 : ℂ) R)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hdis : Disjoint (sphere c r) K)
    (hh : HarmonicOnNhd h (closedBall c r \ K))
    (hbound : ∀ y ∈ ball c r \ K, |h y| ≤ M) :
    ∃ q : ℂ → ℝ, HarmonicOnNhd q (ball c r) ∧
      ContinuousOn q (closedBall c r) ∧ EqOn q h (ball c r \ K) := by
  have hsphere : sphere c r ⊆ closedBall c r \ K := by
    intro y hy
    exact ⟨sphere_subset_closedBall hy, fun hyK => Set.disjoint_left.mp hdis hy hyK⟩
  have hhc : ContinuousOn h (sphere c r) := hh.continuousOn.mono hsphere
  let f : C(sphere c r, ℝ) := ⟨fun y => h y, hhc.domRestrict⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_sphere f
  have hg' : ∀ y ∈ sphere c r, g y = h y := by
    intro y hy
    exact congrFun (congrArg DFunLike.coe hg) ⟨y, hy⟩
  let q : ℂ → ℝ := discSweep univ c r g
  have hD : IsSweepDisc (univ : Set ℂ) c r := ⟨hr, subset_univ _⟩
  have hqc : ContinuousOn q (closedBall c r) :=
    (continuousOn_discSweep isOpen_univ g.continuous.continuousOn).mono (subset_univ _)
  have hq : HarmonicOnNhd q (ball c r) := by
    intro y hy
    apply (harmonicAt_congr_nhds (f₁ := discPoissonIntegral g c r) (f₂ := q) ?_).mp
      (harmonicOnNhd_discPoissonIntegral (hD.circleIntegrable g.continuous.continuousOn) y hy)
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw
    exact (discSweep_of_mem hD hw).symm
  have hbd : ∀ y ∈ sphere c r, y ∉ K → h y = q y := by
    intro y hy _
    have hynot : y ∉ ball c r := by
      rw [mem_sphere] at hy
      exact fun hyb => (mem_ball.mp hyb).ne hy
    dsimp [q]
    rw [discSweep_of_not (fun h => hynot h.2), hg' y hy]
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hqc
  let A := max (M + B) 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound' : ∀ y ∈ ball c r \ K, |h y - q y| ≤ A := by
    intro y hy
    have hqbound : |q y| ≤ B := by simpa only [Real.norm_eq_abs] using hB y (ball_subset_closedBall hy.1)
    exact (abs_sub _ _).trans ((add_le_add (hbound y hy) hqbound).trans (le_max_left _ _))
  refine ⟨q, hq, hqc, ?_⟩
  intro x hx
  exact (harmonic_eq_of_locallyFiniteRankOn_ball_of_continuous_boundary
    hball hKclosed hK hh.continuousOn (hh.mono (fun _ hy => ⟨ball_subset_closedBall hy.1, hy.2⟩))
    hqc hq hA hbound' hbd hx).symm

/-- Locally bounded harmonic functions have local harmonic replacements across a
closed locally finite-rank deletion. -/
theorem exists_local_harmonic_replacement_of_locallyFiniteRankOn
    {U K : Set ℂ} {R ε M : ℝ} {a : ℂ} {h : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R) (ha : a ∈ U)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hh : HarmonicOnNhd h (U \ K)) (hε : 0 < ε)
    (hbound : ∀ y ∈ ball a ε \ K, |h y| ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∃ q : ℂ → ℝ,
      HarmonicOnNhd q (ball a r) ∧ EqOn q h (ball a r \ K) := by
  let V := U ∩ ball a ε
  have hV : IsOpen V := hU.inter isOpen_ball
  have hVR : V ⊆ ball (0 : ℂ) R := inter_subset_left.trans hUR
  have haV : a ∈ V := ⟨ha, mem_ball_self hε⟩
  obtain ⟨r, hr, hcl, hdis⟩ := exists_radius_sphere_disjoint_of_locallyFiniteRankOn
    hV (hK.mono_domain hVR) haV hε
  have hball : closedBall a r ⊆ ball (0 : ℂ) R := hcl.trans hVR
  have hh' : HarmonicOnNhd h (closedBall a r \ K) :=
    hh.mono (fun _ hy => ⟨(hcl hy.1).1, hy.2⟩)
  have hbound' : ∀ y ∈ ball a r \ K, |h y| ≤ M := by
    intro y hy
    exact hbound y ⟨(hcl (ball_subset_closedBall hy.1)).2, hy.2⟩
  obtain ⟨q, hq, _, heq⟩ := exists_harmonic_replacement_of_locallyFiniteRankOn_ball
    hr.1 hball hKclosed hK hdis hh' hbound'
  exact ⟨r, hr.1, q, hq, heq⟩

#print axioms exists_local_harmonic_replacement_of_locallyFiniteRankOn

#print axioms exists_harmonic_replacement_of_locallyFiniteRankOn_ball

#print axioms harmonic_eq_of_locallyFiniteRankOn_ball_of_continuous_boundary

#print axioms harmonic_sub_le_of_locallyFiniteRankOn_ball_of_continuous_boundary

#print axioms exists_radius_sphere_disjoint_of_countable
#print axioms exists_radius_sphere_disjoint_of_locallyFiniteRankOn

end HarmonicBalls
