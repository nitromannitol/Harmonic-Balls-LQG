import HarmonicBalls.FirstPass.S11al
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11j.C42Six

/-!
# Certificate containments for the paper's pinch geometry (fp-S11ap, Lemma 11.13)

Paper `paper/lqg_harmonic_ball-corrected.tex`:
* the component `Ω` of `0` in `B₇ \ (closure B_{2δ}(Q) ∪ closure B_{2δ}(W))` (lines 3180-3191), i.e.
  `pinchOmegaGeom W Q δ`;
* the three local certificates use the radii `δ, 2δ, 3δ` (`O_i = B_δ(K_i)`, lines 3595-3612), i.e. `η = δ`, and the
  internal metric in `Ω` (`A = sup_{x∈∂B₅} D(0,x;Ω)`, line 3624), i.e. `Ostar = Ω`.

Results (no hypothesis beyond `IsBufferedPinchGeometry`):
* `certificateContainments_of_buffered`: `CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q`;
* `zero_union_sphere_subset_pinchOmegaGeom`: the clause `insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ`
  (sphere part from `IsBufferedPinchGeometry.sphere_subset_connectedComponentIn_six`, C42Six.lean:155);
* `pinchOmegaGeom_certificate_data`: the geometric clauses (open, `0 ∈`, sphere `⊆`) and the containments together;
* `certificateEvent_pinch_congr`: locality of `CertificateEvent` for `Ostar = Ω`, `η = δ`.

Not provided here: the containment for an arbitrary `Ostar` with the geometric clauses of `GammaZoomIdentityStmt`
(`Assembly13.lean`, the existential `∃ Ostar`). That existential does not fix `Ostar`, so `Ostar ⊆ closedBall 0 7`
does not follow for it (gap report in `notes/q1.md`).
-/

namespace FirstPassS11ap

open MeasureTheory Metric Set
open HarmonicBalls FirstPassS11i

/-- The annulus `annulus c r₁ r₂ = ball c r₂ \ closedBall c r₁` lies in `closedBall c R` when `r₂ ≤ R`. -/
lemma annulus_subset_closedBall' (c : ℂ) (r₁ r₂ R : ℝ) (h : r₂ ≤ R) : annulus c r₁ r₂ ⊆ closedBall c R :=
  fun _ hx => closedBall_subset_closedBall h (ball_subset_closedBall hx.1)

/-- A point at distance at most `r₁` from `c` is not in the annulus `annulus c r₁ r₂`. -/
lemma not_mem_annulus_of_dist_le (c x : ℂ) (r₁ r₂ : ℝ) (hx : dist x c ≤ r₁) : x ∉ annulus c r₁ r₂ :=
  fun h => h.2 (mem_closedBall.2 hx)

/-- A closure of a `s`-thickening lies in `F` when the `10 d`-buffer of the closure of `E` does and `s ≤ 10 d`
(the buffer conditions of `IsBufferedPinchGeometry`, eq:buffers). -/
lemma closure_thickening_subset_of_buffer {E F : Set ℂ} {s d : ℝ} (hs : s ≤ 10 * d)
    (hF : closure (thickening (10 * d) (closure E)) ⊆ F) : closure (thickening s E) ⊆ F :=
  (closure_mono ((thickening_mono hs E).trans (thickening_subset_of_subset _ subset_closure))).trans hF

/-- The `s`-thickening of `E` lies in `F` under the same buffer hypothesis. -/
lemma thickening_subset_of_buffer {E F : Set ℂ} {s d : ℝ} (hs : s ≤ 10 * d)
    (hF : closure (thickening (10 * d) (closure E)) ⊆ F) : thickening s E ⊆ F :=
  subset_closure.trans (closure_thickening_subset_of_buffer hs hF)

/-- `Ω = pinchOmegaGeom W Q δ` is open (a connected component of an open set, which is open in `ℂ`). -/
lemma isOpen_pinchOmegaGeom (W Q : Set ℂ) (δ : ℝ) : IsOpen (pinchOmegaGeom W Q δ) := by
  unfold pinchOmegaGeom
  exact (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)).connectedComponentIn

/-- **Containments for the paper's certificate geometry.** For a buffered pinch geometry with buffer `δ`, the set
`Ω = pinchOmegaGeom W Q δ` and the parameter `η = δ` satisfy every field of `CertificateContainments`. -/
theorem certificateContainments_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hδ1 : δ < 1 / 1000 := hgeo.delta_lt
  have hQ : Q ⊆ closedBall 0 7 :=
    subset_closure.trans (hgeo.closure_Q_subset.trans
      (Set.sdiff_subset.trans (annulus_subset_closedBall' 0 4 5 7 (by norm_num))))
  have hQ' : Q' ⊆ closedBall 0 7 := subset_closure.trans (hgeo.closure_Q'_subset_Q.trans hQ)
  have hT : thickening δ T ⊆ closedBall 0 7 :=
    (thickening_subset_of_buffer (s := δ) (d := δ) (by linarith) hgeo.buffer_T).trans
      (annulus_subset_closedBall' 0 1 6 7 (by norm_num))
  have hV : thickening δ V ⊆ closedBall 0 7 :=
    (thickening_subset_of_buffer (s := δ) (d := δ) (by linarith) hgeo.buffer_V).trans
      (hgeo.W_subset.trans (annulus_subset_closedBall' 0 1 2 7 (by norm_num)))
  have hW : thickening (4 * δ) W ⊆ closedBall 0 7 :=
    (thickening_subset_of_buffer (s := 4 * δ) (d := δ) (by linarith) hgeo.buffer_W).trans
      (Set.inter_subset_right.trans (annulus_subset_closedBall' 0 1 2 7 (by norm_num)))
  have hΩ : pinchOmegaGeom W Q δ ⊆ closedBall 0 7 := by
    intro x hx
    unfold pinchOmegaGeom at hx
    exact ball_subset_closedBall (connectedComponentIn_subset _ _ hx).1
  exact
    { eta_pos := hδ
      three_eta_le := by linarith
      Ostar_sub := hΩ
      Qprime_sub := hQ'
      Q_sub := hQ
      T_thick := hT
      V_thick := hV
      W_thick := hW }

/-- The clause `{0} ∪ ∂B₅ ⊆ pinchOmegaGeom W Q δ` (paper lines 3186-3199) follows from the buffered geometry: the sphere
lies in the component of `0` in `B₆ \ (…)` (C42Six.lean:155), and `0` lies in `B₇ \ (…)` because `0` is outside the
closures of the two thickenings (`0 ∉ annulus 0 4 5 ⊇ closure B_{2δ}(Q)` and `0 ∉ annulus 0 1 2 ⊇ closure B_{2δ}(W)`). -/
theorem zero_union_sphere_subset_pinchOmegaGeom {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hsph : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := by
    unfold pinchOmegaGeom
    exact hgeo.sphere_subset_connectedComponentIn_six.trans
      (connectedComponentIn_mono 0 (sdiff_subset_sdiff_left (ball_subset_ball (by norm_num))))
  have h0 : (0 : ℂ) ∈ pinchOmegaGeom W Q δ := by
    unfold pinchOmegaGeom
    refine mem_connectedComponentIn ⟨mem_ball_self (by norm_num), ?_⟩
    rintro (hm | hm)
    · have hmQ := closure_thickening_subset_of_buffer (s := 2 * δ) (d := δ) (by linarith) hgeo.buffer_Q hm
      exact not_mem_annulus_of_dist_le 0 0 4 5 (by norm_num) hmQ.1
    · have hmW := closure_thickening_subset_of_buffer (s := 2 * δ) (d := δ) (by linarith) hgeo.buffer_W hm
      exact not_mem_annulus_of_dist_le 0 0 1 2 (by norm_num) hmW.2
  exact insert_subset_iff.2 ⟨h0, hsph⟩

/-- The geometric clauses of `ZoomIdentityStmt` and `GammaZoomIdentityStmt` for `Ostar = pinchOmegaGeom W Q δ`
(open, `0 ∈`, `∂B₅ ⊆`), together with the containments of `CertificateContainments δ Ostar V W T Q' Q`. -/
theorem pinchOmegaGeom_certificate_data {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    IsOpen (pinchOmegaGeom W Q δ) ∧ (0 : ℂ) ∈ pinchOmegaGeom W Q δ ∧ sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ ∧
      CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q := by
  have hcl := zero_union_sphere_subset_pinchOmegaGeom hgeo
  exact ⟨isOpen_pinchOmegaGeom W Q δ, hcl (mem_insert _ _), fun x hx => hcl (mem_insert_of_mem _ hx),
    certificateContainments_of_buffered hgeo⟩

/-- Locality of the paper's certificate event: for `Ostar = pinchOmegaGeom W Q δ` and `η = δ`, the event
`CertificateEvent μ D Ostar U V W T Q' Q δ M r z` depends on `D` only on `closedBall z (7r) ×ˢ closedBall z (7r)`. -/
theorem certificateEvent_pinch_congr {μ : Measure ℂ} {D D' : ℂ → ℂ → ℝ} {U V W T Q' Q : Set ℂ} {δ M r : ℝ}
    {z : ℂ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hr : 0 < r)
    (hEq : Set.EqOn (Function.uncurry D) (Function.uncurry D') (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    CertificateEvent μ D (pinchOmegaGeom W Q δ) U V W T Q' Q δ M r z ↔
      CertificateEvent μ D' (pinchOmegaGeom W Q δ) U V W T Q' Q δ M r z :=
  certificateEvent_congr_of_eqOn_closedBall (certificateContainments_of_buffered hgeo) hr hEq

end FirstPassS11ap

#print axioms FirstPassS11ap.certificateContainments_of_buffered
#print axioms FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom
#print axioms FirstPassS11ap.pinchOmegaGeom_certificate_data
#print axioms FirstPassS11ap.certificateEvent_pinch_congr
