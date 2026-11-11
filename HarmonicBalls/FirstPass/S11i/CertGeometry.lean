import HarmonicBalls.FirstPass.S11i.CertHcert
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Geometric non-emptiness for the certificate with buffer `η = δ`

The hypotheses of `certificate_subset_pinchPointEvent` (`hF`, `hQ'`, `hK02`, `hK21`) follow from the buffered pinch
geometry `IsBufferedPinchGeometry U V W T Q' Q δ` with the buffer `η = δ`. Only the buffer clauses, openness, connectedness and
boundedness are used; no drawing is needed.
-/

namespace FirstPassS11i

open MeasureTheory Metric Set Filter Topology
open HarmonicBalls

/-- `A ⊆ thickening ε A` for `ε > 0`. -/
lemma subset_thickening_of_pos {E : Set ℂ} {ε : ℝ} (hε : 0 < ε) : E ⊆ thickening ε E :=
  fun x hx => mem_thickening_iff.2 ⟨x, hx, by simpa [dist_self] using hε⟩

/-- A nonempty open subset of a ball is not `ℂ`, so its frontier is nonempty (`ℂ` is connected). -/
lemma frontier_nonempty_of_isOpen_subset_ball {S : Set ℂ} {R : ℝ} (hne : S.Nonempty)
    (hsub : S ⊆ ball (0 : ℂ) R) : (frontier S).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hcl : IsClopen S := isClopen_iff_frontier_eq_empty.2 h
  have huniv : S = univ := hcl.eq_univ hne
  have hmem : ((|R| + 1 : ℝ) : ℂ) ∈ S := by
    rw [huniv]
    exact mem_univ _
  have h1 := hsub hmem
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  linarith [le_abs_self R, abs_nonneg R]

namespace BufferedGeom

variable {U V W T Q' Q : Set ℂ} {δ : ℝ}

lemma closure_V_subset (hg : IsBufferedPinchGeometry U V W T Q' Q δ) : closure V ⊆ W :=
  fun x hx => hg.buffer_V (subset_closure (subset_thickening_of_pos (by linarith [hg.delta_pos]) hx))

lemma closure_U_subset (hg : IsBufferedPinchGeometry U V W T Q' Q δ) : closure U ⊆ V :=
  fun x hx => hg.buffer_U (subset_closure (subset_thickening_of_pos (by linarith [hg.delta_pos]) hx))

lemma V_nonempty (hg : IsBufferedPinchGeometry U V W T Q' Q δ) : V.Nonempty :=
  hg.U_nonempty.mono (subset_closure.trans (closure_U_subset hg))

lemma frontier_Q_nonempty (hg : IsBufferedPinchGeometry U V W T Q' Q δ) : (frontier Q).Nonempty :=
  frontier_nonempty_of_isOpen_subset_ball hg.isConnected_Q.nonempty
    (fun _ hx => (hg.closure_Q_subset (subset_closure hx)).1.1)

lemma Q'_nonempty (hg : IsBufferedPinchGeometry U V W T Q' Q δ) : Q'.Nonempty :=
  hg.isConnected_Q'.nonempty

/-- `Ŵ := thickening (3δ) W` is a nonempty open set with frontier, contained in `T`. -/
lemma thick_sub_closure_T (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    closure (thickening (3 * δ) W) ⊆ T := by
  have hsub : thickening (3 * δ) W ⊆ thickening (10 * δ) (closure W) := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_thickening_iff.1 hx
    exact mem_thickening_iff.2 ⟨w, subset_closure hw, by linarith [hg.delta_pos]⟩
  intro x hx
  exact (hg.buffer_W (closure_mono hsub hx)).1

lemma thick_sub_ball (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    thickening (3 * δ) W ⊆ ball (0 : ℂ) 3 := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_thickening_iff.1 hx
  have h1 : dist w 0 < 2 := mem_ball.1 (hg.W_subset hw).1
  have h2 : dist x 0 < 3 := by linarith [dist_triangle x w 0, hg.delta_lt, hg.delta_pos]
  exact mem_ball.2 h2

end BufferedGeom

open BufferedGeom

/-- `hF` for the buffer `η = δ`. -/
lemma frontier_thickening_nonempty {U V W T Q' Q : Set ℂ} {δ : ℝ} (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    (frontier (thickening (3 * δ) W)).Nonempty := by
  have hne : (thickening (3 * δ) W).Nonempty := by
    obtain ⟨w, hw⟩ := V_nonempty hg
    exact ⟨w, subset_thickening_of_pos (by linarith [hg.delta_pos])
      (closure_V_subset hg (subset_closure hw))⟩
  exact frontier_nonempty_of_isOpen_subset_ball hne (thick_sub_ball hg)

lemma certK21_nonempty {U V W T Q' Q : Set ℂ} {δ : ℝ} (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    (certK2 V W δ ∩ certK1 V).Nonempty := by
  obtain ⟨x, hxF⟩ := frontier_nonempty_of_isOpen_subset_ball (V_nonempty hg)
    (fun y hy => (hg.V_subset hy).1)
  rw [frontier_eq_closure_inter_closure] at hxF
  have hxVc : x ∈ closure V := hxF.1
  have hxA : x ∈ thickening (3 * δ) W :=
    subset_thickening_of_pos (by linarith [hg.delta_pos]) (closure_V_subset hg hxVc)
  refine ⟨x, ?_, hxVc⟩
  show x ∈ closure (thickening (3 * δ) W \ V)
  rw [Set.sdiff_eq]
  exact isOpen_thickening.inter_closure ⟨hxA, hxF.2⟩

lemma certK02_nonempty {U V W T Q' Q : Set ℂ} {δ : ℝ} (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    (certK0 T W δ ∩ certK2 V W δ).Nonempty := by
  obtain ⟨x, hxF⟩ := frontier_thickening_nonempty hg
  have hxcl : x ∈ closure (thickening (3 * δ) W) := frontier_subset_closure hxF
  have hxA' : x ∉ thickening (3 * δ) W := by
    have h := hxF
    rw [isOpen_thickening.frontier_eq] at h
    exact h.2
  have hxc : x ∈ closure (thickening (3 * δ) W)ᶜ := by
    have h := hxF
    rw [frontier_eq_closure_inter_closure] at h
    exact h.2
  have hxT : x ∈ T := thick_sub_closure_T hg hxcl
  have hxnV : x ∉ closure V := fun h =>
    hxA' (subset_thickening_of_pos (by linarith [hg.delta_pos]) (closure_V_subset hg h))
  have hK0 : x ∈ certK0 T W δ := by
    show x ∈ closure (T \ thickening (3 * δ) W)
    rw [Set.sdiff_eq]
    exact hg.isOpen_T.inter_closure ⟨hxT, hxc⟩
  have hK2 : x ∈ certK2 V W δ := by
    show x ∈ closure (thickening (3 * δ) W \ V)
    have hopen : IsOpen ((closure V)ᶜ) := isClosed_closure.isOpen_compl
    have hsub : (closure V)ᶜ ∩ thickening (3 * δ) W ⊆ thickening (3 * δ) W \ V :=
      fun y hy => ⟨hy.2, fun hyV => hy.1 (subset_closure hyV)⟩
    exact closure_mono hsub (hopen.inter_closure ⟨hxnV, hxcl⟩)
  exact ⟨x, hK0, hK2⟩

/-- The rescaled certificate implies the pinch event at every centre, for the buffered geometry with buffer `η = δ`
(`hcert_of_scale` with its geometric hypotheses discharged). -/
theorem hcert_of_buffered {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℂ → ℂ → ℝ)
    (hDlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hDk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    {Ostar U V W T Q' Q : Set ℂ} {δ M : ℝ} (hg : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), ∀ n : ℕ,
      windowCert Ostar U V W T Q' Q δ M μk Dk k ω n w →
        pinchPointEvent (μk k ω) (Dk k ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w :=
  hcert_of_scale P D hDlen μk Dk hDk hg.delta_pos (by linarith [hg.delta_lt])
    (Q'_nonempty hg) (frontier_Q_nonempty hg) (certK02_nonempty hg) (certK21_nonempty hg)

end FirstPassS11i

