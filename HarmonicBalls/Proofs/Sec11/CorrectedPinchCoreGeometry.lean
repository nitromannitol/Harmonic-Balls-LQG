import HarmonicBalls.Proofs.Sec11.ConditionalCoreMeasurability
import HarmonicBalls.Draft.Section11Corrected

/-! # Compact connected core for the corrected pinch configuration -/

namespace HarmonicBalls
open Set Metric

/-- Every nonempty open set contains a closed axis-parallel square of
positive side length. -/
theorem exists_closedSquare_subset_of_isOpen {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  refine ⟨z, r / 4, by positivity, ?_⟩
  intro x hx
  apply hrU
  rw [Metric.mem_ball, dist_eq_norm]
  have hx' : z.re ≤ x.re ∧ x.re ≤ z.re + r / 4 ∧
      z.im ≤ x.im ∧ x.im ≤ z.im + r / 4 := by
    simpa only [closedSquare, Complex.mem_reProdIm, mem_Icc, and_assoc] using hx
  have hre : |(x - z).re| ≤ r / 4 := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [hx'.1, hx'.2.1]
  have him : |(x - z).im| ≤ r / 4 := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [hx'.2.2.1, hx'.2.2.2]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (x - z)
  linarith

/-- The intermediate ball has compact connected closure; every set inside
the innermost ball is contained in the interior of that closure. -/
theorem IsCorrectedPinchConfiguration.closure_V_core
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    IsCompact (closure V) ∧ IsConnected (closure V) ∧ U ⊆ interior (closure V) := by
  have hUV : U ⊆ V := subset_closure.trans h.closure_U_subset_V
  obtain ⟨c, rU, rV, rW, hU, hV, hW⟩ := h.concentric
  have hVne : V.Nonempty := h.isConnected_U.nonempty.mono hUV
  have hrV : 0 < rV := by rw [hV, nonempty_ball] at hVne; exact hVne
  have hcV : IsConnected V := by rw [hV]; exact isConnected_ball hrV
  have hVopen : IsOpen V := by rw [hV]; exact isOpen_ball
  have hVbounded : Bornology.IsBounded V := by rw [hV]; exact isBounded_ball
  exact ⟨hVbounded.isCompact_closure, hcV.closure,
    hUV.trans (hVopen.subset_interior_iff.mpr subset_closure)⟩

/-- The complement of the outer closed ball contains the unit circle and
has closure disjoint from the intermediate closed ball. -/
theorem IsCorrectedPinchConfiguration.outside_core
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ ∧
      Disjoint (closure V) (closure ((closure W)ᶜ)) := by
  obtain ⟨c, rU, rV, rW, hU, hV, hW⟩ := h.concentric
  have hWo : IsOpen W := by rw [hW]; exact isOpen_ball
  have hout : closure ((closure W)ᶜ) ⊆ Wᶜ :=
    closure_minimal (compl_subset_compl.mpr subset_closure) hWo.isClosed_compl
  constructor
  · intro x hx hxW
    have hxT := h.closure_W_subset_T hxW
    have hxann := h.T_subset hxT
    have hxcl : x ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, ← mem_sphere.mp hx]
    exact hxann.2 hxcl
  · apply disjoint_left.mpr
    intro x hxV hxO
    exact hout hxO (h.closure_V_subset_W hxV)

/-- Unit-scale neighborhoods of the mass set lie in the ball of radius
three about the origin. -/
theorem IsCorrectedPinchConfiguration.mass_buffer
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ∀ n x, x ∈ U → closedBall x (dyadicScale n) ⊆ ball (0 : ℂ) 3 := by
  intro n x hx y hy
  have hx2 : dist x (0 : ℂ) < 2 := by
    exact mem_ball.mp ((h.U_subset hx).1)
  have hyx : dist y x ≤ dyadicScale n := mem_closedBall.mp hy
  have hn : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  apply mem_ball.mpr
  have ht := dist_triangle y x (0 : ℂ)
  linarith

/-- A single square in the mass set satisfies the geometric hypotheses for
the conditional dyadic core, with a deterministic radius-three buffer. -/
theorem IsCorrectedPinchConfiguration.exists_mass_core_square
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      closedSquare z L ⊆ interior (closure V) ∧
      ∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball (0 : ℂ) 3 := by
  obtain ⟨z, L, hL, hSU⟩ := exists_closedSquare_subset_of_isOpen h.isOpen_U
    h.isConnected_U.nonempty
  exact ⟨z, L, hL, hSU, hSU.trans h.closure_V_core.2.2,
    fun n x hx => h.mass_buffer n x (hSU hx)⟩

#print axioms IsCorrectedPinchConfiguration.closure_V_core
#print axioms exists_closedSquare_subset_of_isOpen
#print axioms IsCorrectedPinchConfiguration.outside_core
#print axioms IsCorrectedPinchConfiguration.mass_buffer
#print axioms IsCorrectedPinchConfiguration.exists_mass_core_square
end HarmonicBalls
