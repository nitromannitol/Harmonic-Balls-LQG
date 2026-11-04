import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness
import Mathlib.Analysis.Normed.Module.Connected

/-! # Connected neighborhoods of concentric annuli -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- A positive thickening of a connected planar set is connected. -/
theorem IsConnected.thickening_complex {A : Set ℂ} (hA : IsConnected A)
    {δ : ℝ} (hδ : 0 < δ) : IsConnected (thickening δ A) := by
  obtain ⟨z, hz⟩ := hA.nonempty
  let F : A → Set ℂ := fun x => A ∪ ball x.1 δ
  have heq : thickening δ A = ⋃ x : A, F x := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hyx⟩ := mem_thickening_iff.mp hy
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Or.inr hyx⟩
    · intro hy
      obtain ⟨x, hy⟩ := mem_iUnion.mp hy
      rcases hy with hy | hy
      · exact self_subset_thickening hδ A hy
      · exact mem_thickening_iff.mpr ⟨x, x.property, hy⟩
  rw [heq]
  have hpre : IsPreconnected (⋃ x : A, F x) := by
    apply isPreconnected_iUnion
    · refine ⟨z, mem_iInter.mpr ?_⟩
      intro x
      exact Or.inl hz
    · intro x
      exact hA.isPreconnected.union' ⟨x, x.property, mem_ball_self hδ⟩
        (isPreconnected_ball : IsPreconnected (ball (x : ℂ) δ))
  exact ⟨⟨z, mem_iUnion.mpr ⟨⟨z, hz⟩, Or.inl hz⟩⟩, hpre⟩

/-- A concentric planar annulus with its inner circle included is connected. -/
theorem isConnected_ball_sdiff_ball_complex (c : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) : IsConnected (ball c R \ ball c r) := by
  let F : ℝ × ℂ → ℂ := fun p => c + (p.1 : ℂ) * p.2
  have hc : Continuous F := by fun_prop
  have hprod : IsConnected (Ico r R ×ˢ sphere (0 : ℂ) 1) :=
    (isConnected_Ico hrR).prod (isConnected_sphere (by simp) 0 (by norm_num))
  have himage : F '' (Ico r R ×ˢ sphere (0 : ℂ) 1) = ball c R \ ball c r := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
      have ht0 : 0 ≤ t := le_trans hr.le ht.1
      simp only [mem_sdiff, mem_ball, not_lt]
      have hn : ‖(t : ℂ) * u‖ = t := by
        simp [hu', Real.norm_eq_abs, abs_of_nonneg ht0]
      rw [dist_eq_norm, add_sub_cancel_left, hn]
      exact ⟨ht.2, ht.1⟩
    · intro hz
      have hzR : dist z c < R := hz.1
      have hzr : r ≤ dist z c := le_of_not_gt hz.2
      have hnpos : 0 < ‖z - c‖ := by simpa [dist_eq_norm] using hr.trans_le hzr
      let u : ℂ := (z - c) / (‖z - c‖ : ℂ)
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right]
        simp [u, ne_of_gt hnpos]
      refine ⟨(‖z - c‖, u), ⟨⟨?_, ?_⟩, hu⟩, ?_⟩
      · simpa [dist_eq_norm] using hzr
      · simpa [dist_eq_norm] using hzR
      · dsimp [F, u]
        have hne : (‖z - c‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
        field_simp
        abel
  rw [← himage]
  exact hprod.image F hc.continuousOn

/-- The annular auxiliary piece in the third pinch event has finite internal
diameter for every Euclidean length metric. -/
theorem IsPinchPointProofConfiguration.internalDiam_outerAnnulus_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    internalDiam D δ (thickening (3 * δ) W \ V) < ∞ := by
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := hconfig.concentric
  have hδ : 0 < δ := hconfig.δ₀_mem.1
  have hVne : V.Nonempty := hconfig.isConnected_U.nonempty.mono
    (subset_closure.trans hconfig.closure_U_subset_V)
  have hρV : 0 < ρV := by rw [hV, nonempty_ball] at hVne; exact hVne
  have hWne : W.Nonempty := hVne.mono (subset_closure.trans hconfig.closure_V_subset_W)
  have hρW : 0 < ρW := by rw [hW, nonempty_ball] at hWne; exact hWne
  have hρVW : ρV < ρW := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hρV.le
    have hxcl : x ∈ closure V := by
      rw [hV, closure_ball c hρV.ne']
      exact sphere_subset_closedBall hx
    have hxW : x ∈ ball c ρW := by simpa [hW] using hconfig.closure_V_subset_W hxcl
    rw [mem_ball] at hxW
    rw [mem_sphere] at hx
    linarith
  have hpiece : thickening (3 * δ) W \ V = ball c (ρW + 3 * δ) \ ball c ρV := by
    rw [hW, thickening_ball (by linarith : 0 < 3 * δ) hρW, hV, add_comm (3 * δ) ρW]
  have hconn : IsConnected (thickening (3 * δ) W \ V) := by
    rw [hpiece]
    exact isConnected_ball_sdiff_ball_complex c hρV (by linarith)
  have hbounded : Bornology.IsBounded (thickening (3 * δ) W \ V) := by
    rw [hpiece]
    exact isBounded_ball.subset sdiff_subset
  exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hδ hbounded
    (IsConnected.thickening_complex hconn hδ)

end HarmonicBalls
