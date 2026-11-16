import HarmonicBalls.FirstPass.S11y.ShiftLength

/-! # Local pinch events under a supported Weyl shift -/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- The buffered third-event neighborhood admits a cutoff supported in the
five-delta neighborhood of `W`. -/
theorem IsBufferedPinchGeometry.exists_third_cutoff
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closure (thickening δ (S11y.pinchK2 W V δ)), φ z = 1) ∧
      (∀ z ∈ closure U, φ z = 0) ∧ tsupport φ ⊆ thickening (5 * δ) W := by
  have hδ := hgeo.delta_pos
  have hWb : W ⊆ closedBall (0 : ℂ) 2 := fun z hz =>
    mem_closedBall.2 (le_of_lt (mem_ball.1 (hgeo.W_subset hz).1))
  have hUb : U ⊆ closedBall (0 : ℂ) 2 := fun z hz =>
    mem_closedBall.2 (le_of_lt (mem_ball.1 (hgeo.U_subset hz).1))
  have hK2 : S11y.pinchK2 W V δ ⊆ closedBall (0 : ℂ) (2 + 3 * δ) :=
    closure_minimal (fun z hz => S11y.thickening_subset_closedBall_of_subset hWb (by linarith) hz.1)
      isClosed_closedBall
  have hKc : IsCompact (closure (thickening δ (S11y.pinchK2 W V δ))) :=
    S11y.isCompact_closure_of_subset_closedBall
      (S11y.thickening_subset_closedBall_of_subset hK2 hδ.le)
  have hUcl : closure U ⊆ closedBall (0 : ℂ) 2 := closure_minimal hUb isClosed_closedBall
  have hUc : IsCompact (closure U) := S11y.isCompact_closure_of_subset_closedBall hUb
  have hKsub : closure (thickening δ (S11y.pinchK2 W V δ)) ⊆
      thickening (9 * δ / 2) W := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := mem_closure_iff.1 hy (δ / 8) (by positivity)
    obtain ⟨z, hzK, hwz⟩ := mem_thickening_iff.1 hw
    obtain ⟨b, hb, hzb⟩ := mem_closure_iff.1 hzK (δ / 8) (by positivity)
    obtain ⟨x, hx, hbx⟩ := mem_thickening_iff.1 hb.1
    refine mem_thickening_iff.2 ⟨x, hx, ?_⟩
    have h1 := dist_triangle y w z
    have h2 := dist_triangle z b x
    have h3 := dist_triangle y z x
    linarith
  obtain ⟨χ, hχs, hχc, hχ1, hχ0, hχ01⟩ :=
    exists_smooth_bump_on hKc isOpen_thickening hKsub
      (isBounded_closedBall.subset (S11y.thickening_subset_closedBall_of_subset hWb (by linarith)))
  have hUsub : closure U ⊆ thickening (5 * δ) (closure U) := fun x hx =>
    mem_thickening_iff.2 ⟨x, hx, by rw [dist_self]; linarith⟩
  obtain ⟨ψ, hψs, _, hψ1, hψ0, hψ01⟩ :=
    exists_smooth_bump_on hUc isOpen_thickening hUsub
      (isBounded_closedBall.subset (S11y.thickening_subset_closedBall_of_subset hUcl (by linarith)))
  refine ⟨fun z => χ z * (1 - ψ z), hχs.mul (contDiff_const.sub hψs), hχc.mul_right, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨h1a, h1b⟩ := hχ01 z
    obtain ⟨h2a, h2b⟩ := hψ01 z
    exact ⟨mul_nonneg h1a (by linarith), by nlinarith⟩
  · intro z hz
    have hnot : z ∉ thickening (5 * δ) (closure U) := by
      intro hzU
      obtain ⟨x, hx, hd⟩ := mem_thickening_iff.1 hzU
      have hfar := S11y.far_closure_U_of_K2 hgeo hδ z hz x hx
      rw [dist_comm] at hfar
      linarith
    change χ z * (1 - ψ z) = 1
    rw [hχ1 z hz, hψ0 z hnot]
    ring
  · intro z hz
    simp [hψ1 z hz]
  · have hsupport : Function.support (fun z => χ z * (1 - ψ z)) ⊆
        thickening (9 * δ / 2) W := by
      intro z hz
      by_contra hn
      apply hz
      simp [hχ0 z hn]
    exact (closure_mono hsupport).trans
      ((closure_thickening_subset_cthickening _ _).trans
        (cthickening_subset_thickening' (by linarith) (by linarith) W))

/-- The local triple holds after the prescribed smooth contraction on the
first-two-event threshold set. -/
theorem IsBufferedPinchGeometry.local_triple_of_third_cutoff
    {U V W T Q' Q : Set ℂ} {δ ξ γ M c₁ c₂ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hξ : 0 < ξ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {φ : ℂ → ℝ} (hφC : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ01 : ∀ z, φ z ∈ Icc (0 : ℝ) 1)
    (hφ1 : ∀ z ∈ closure (thickening δ (S11y.pinchK2 W V δ)), φ z = 1)
    (hφU : ∀ z ∈ closure U, φ z = 0) (hφsupp : tsupport φ ⊆ thickening (5 * δ) W)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {μ : Measure ℂ}
    (hE1 : pinchFirstEventLocal D W T Q' Q δ) (hE2 : pinchSecondEventLocal μ D U V δ M)
    (ha : c₁ ≤ setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))
    (hd : internalDiam D δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal c₂) :
    let f := S11y.shiftWeight3 ξ (min 1 (c₁ / (2 * c₂))) φ
    pinchFirstEventLocal (fun x y => (weylScaling D ξ f x y).toReal) W T Q' Q δ ∧
    pinchSecondEventLocal (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
      (fun x y => (weylScaling D ξ f x y).toReal) U V δ M ∧
    pinchThirdEventLocal (fun x y => (weylScaling D ξ f x y).toReal) V W δ := by
  have hk : 0 < min 1 (c₁ / (2 * c₂)) := lt_min (by norm_num) (div_pos hc₁ (by positivity))
  have hkbound : min 1 (c₁ / (2 * c₂)) * c₂ ≤ c₁ / 2 := by
    calc
      min 1 (c₁ / (2 * c₂)) * c₂ ≤ (c₁ / (2 * c₂)) * c₂ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hc₂.le
      _ = c₁ / 2 := by field_simp
  have hout : ∀ z, z ∉ thickening (6 * δ) W → φ z = 0 := by
    intro z hz
    by_contra hn
    exact hz ((thickening_mono (by linarith [hgeo.delta_pos]) W)
      (hφsupp (subset_closure hn)))
  exact S11y.pinchLocal_E3_of_shift_bump hgeo hD hξ hk (min_le_left _ _) hc₁ hkbound
    hφC hφc hφ01 hφ1 hφU hout hE1 hE2 ha hd

/-- A single smooth buffered cutoff realizes the prescribed third-event shift
for every measure and length metric satisfying the threshold conditions. -/
theorem IsBufferedPinchGeometry.exists_third_shift_local_triple
    {U V W T Q' Q : Set ℂ} {δ ξ c₁ c₂ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hξ : 0 < ξ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closure (thickening δ (S11y.pinchK2 W V δ)), φ z = 1) ∧
      (∀ z ∈ closure U, φ z = 0) ∧ tsupport φ ⊆ thickening (5 * δ) W ∧
      ∀ (D : ℂ → ℂ → ℝ) (μ : Measure ℂ) (γ M : ℝ),
        IsEuclideanLengthMetric D → pinchFirstEventLocal D W T Q' Q δ →
        pinchSecondEventLocal μ D U V δ M →
        c₁ ≤ setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)) →
        internalDiam D δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal c₂ →
        let f := S11y.shiftWeight3 ξ (min 1 (c₁ / (2 * c₂))) φ
        pinchFirstEventLocal (fun x y => (weylScaling D ξ f x y).toReal) W T Q' Q δ ∧
        pinchSecondEventLocal (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
          (fun x y => (weylScaling D ξ f x y).toReal) U V δ M ∧
        pinchThirdEventLocal (fun x y => (weylScaling D ξ f x y).toReal) V W δ := by
  obtain ⟨φ, hφC, hφc, hφ01, hφ1, hφU, hφsupp⟩ := hgeo.exists_third_cutoff
  refine ⟨φ, hφC, hφc, hφ01, hφ1, hφU, hφsupp, ?_⟩
  intro D μ γ M hD hE1 hE2 ha hd
  exact hgeo.local_triple_of_third_cutoff hξ hc₁ hc₂ hφC hφc hφ01 hφ1 hφU hφsupp
    hD hE1 hE2 ha hd

end HarmonicBalls
