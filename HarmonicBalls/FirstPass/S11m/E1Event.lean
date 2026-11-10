import HarmonicBalls.FirstPass.S11m.E1Bounds
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents

/-!
# The local first event `E₁` for the Weyl-shifted metric (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 6.2; paper `lem:E1`
(`paper/lqg_harmonic_ball-corrected.tex`, lines 3661-3700). Deterministic part only.

For a Euclidean length metric `D` and a weight `f` with `ξ f = log b_Q φ_Q + log b φ_0` (the paper's
`ξ⁻¹ log b_Q φ_Q + ξ⁻¹ log b φ_0`), the shifted metric `E := (weylScaling D ξ f).toReal` satisfies
`pinchFirstEventLocal E W T Q' Q δ` whenever `D` satisfies the event bounds `L ≥ c₁`, `A ≤ c₂`,
`D(0, ∂B_{δ/2}) ≥ c₃`, `d₀ ≤ c₄`, with `2 c₄ ≤ b c₃` and `2 b c₂ ≤ b_Q c₁`.

Inputs: `hE`, the Euclidean length property of the shifted metric, is a hypothesis (not yet sourced).
The bumps are Urysohn functions (continuous; the paper's smoothness is not used by the estimates).
-/
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls.S11m.E1Event

open HarmonicBalls.S11m.E1Bounds HarmonicBalls.S11m.WeylShiftE1

/-- Internal diameter comparison: if the weight is `≤ 0` on the `δ`-neighbourhood of `A`, the internal diameter of
`A` for the shifted metric is at most that for `D` (paper `lem:E1`, `d₀,new = d₀` with `d₀,new ≤ d₀` suffices). -/
theorem internalDiam_weylScaling_le {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ δ : ℝ} {f : ℂ → ℝ}
    {A : Set ℂ} (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) (hweight : ∀ z ∈ thickening δ A, ξ * f z ≤ 0) :
    internalDiam (fun x y => (weylScaling D ξ f x y).toReal) δ A ≤ internalDiam D δ A := by
  unfold internalDiam
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
  have key := hD.internalMetric_weylScaling_le hE (fun x y => ENNReal.toReal_nonneg) isOpen_thickening
    (hD.weylScaling_zero ξ) (fun x y => ENNReal.ofReal_toReal (hfin x y)) hweight x y
  rw [Real.exp_zero, ENNReal.ofReal_one, one_mul] at key
  exact key.trans ((le_iSup₂ (f := fun y (_ : y ∈ A) => internalMetric D (thickening δ A) x y) y hy).trans
    (le_iSup₂ (f := fun x (_ : x ∈ A) => ⨆ y ∈ A, internalMetric D (thickening δ A) x y) x hx))

/-- The `δ`-neighbourhood of the closed set `K₀ = closure (T \ B_{3δ}(W))` avoids `B_δ(0)` and `B_δ(Q)`
(paper `lem:E1`: "both bumps vanish on `O₀`"). Uses `closure T ⊆ annulus 0 1 6` and `buffer_Q`. -/
theorem thickening_K0_disjoint {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ z ∈ thickening δ (closure (T \ thickening (3 * δ) W)), z ∉ thickening δ Q ∧ z ∉ ball (0 : ℂ) δ := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 hz
  have hwT : w ∈ closure T := closure_mono sdiff_subset hw
  have hwA := hgeo.closure_T_subset hwT
  have hw1 : 1 < dist w 0 := not_le.1 fun h => hwA.2 (mem_closedBall.2 h)
  have hδ := hgeo.delta_pos
  have hδ1 := hgeo.delta_lt
  constructor
  · intro hzQ
    obtain ⟨q, hqQ, hzq⟩ := mem_thickening_iff.1 hzQ
    have hq1 : q ∈ thickening (10 * δ) (closure Q) :=
      mem_thickening_iff.2 ⟨q, subset_closure hqQ, by rw [dist_self]; linarith⟩
    have hq2 := (hgeo.buffer_Q (subset_closure hq1)).2
    apply hq2
    refine mem_thickening_iff.2 ⟨w, hwT, ?_⟩
    have h1 := dist_triangle q z w
    rw [dist_comm q z] at h1
    linarith
  · intro hz0
    rw [mem_ball] at hz0
    have h1 := dist_triangle w z 0
    rw [dist_comm w z] at h1
    linarith

/-- Urysohn bumps: a continuous `φ : ℂ → [0,1]` with `φ = 0` on `s` and `φ = 1` on `t` for disjoint closed `s, t`. -/
theorem exists_urysohn_bump {s t : Set ℂ} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ φ : ℂ → ℝ, (∀ z ∈ s, φ z = 0) ∧ (∀ z ∈ t, φ z = 1) ∧ ∀ z, φ z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨g, h0, h1, hI⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  exact ⟨g, fun z hz => h0 hz, fun z hz => h1 hz, hI⟩

/-- The two pinch bumps of paper `lem:E1`: `φ_Q = 1` on `Q̄`, `φ_Q = 0` off `B_δ(Q)`; `φ_0 = 1` on `B̄_{δ/2}`,
`φ_0 = 0` off `B_δ(0)`. -/
theorem exists_pinch_bumps {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ φQ φ0 : ℂ → ℝ, (∀ z ∈ closure Q, φQ z = 1) ∧ (∀ z, z ∉ thickening δ Q → φQ z = 0) ∧
      (∀ z, φQ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) ∧ (∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) ∧
      (∀ z, φ0 z ∈ Icc (0 : ℝ) 1) := by
  have hδ := hgeo.delta_pos
  obtain ⟨φQ, hQ0, hQ1, hQI⟩ := exists_urysohn_bump (s := (thickening δ Q)ᶜ) (t := closure Q)
    isOpen_thickening.isClosed_compl isClosed_closure
    (Set.disjoint_left.2 fun z hz hz' => hz (closure_subset_thickening hδ Q hz'))
  obtain ⟨φ0, h00, h01, hφI⟩ := exists_urysohn_bump (s := (ball (0 : ℂ) δ)ᶜ) (t := closedBall (0 : ℂ) (δ / 2))
    isOpen_ball.isClosed_compl isClosed_closedBall
    (Set.disjoint_left.2 fun z hz hz' => hz (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz') (by linarith))))
  exact ⟨φQ, φ0, hQ1, fun z hz => hQ0 z hz, hQI, h01, fun z hz => h00 z hz, hφI⟩

/-- The weight `f = ξ⁻¹ (log b_Q φ_Q + log b φ_0)` satisfies `ξ f = log b_Q φ_Q + log b φ_0`. -/
theorem weight_xi_mul {ξ : ℝ} (hξ : 0 < ξ) (s : ℝ) : ξ * (ξ⁻¹ * s) = s :=
  mul_inv_cancel_left₀ hξ.ne' s

/-- Deterministic first event for the shifted metric (paper `lem:E1`, on the event `F`): given the bounds
`L ≥ c₁`, `A ≤ c₂`, `D(0, ∂B_{δ/2}) ≥ c₃`, `d₀ ≤ c₄` for `D`, the shifted metric satisfies `E₁`. The hypothesis
`hE` (the Euclidean length property of the Weyl-scaled metric) is an input, not yet sourced. -/
theorem pinchFirstEventLocal_weylScaling {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {ξ b bQ c₁ c₂ c₃ c₄ : ℝ} (hξ : 0 < ξ) (hb1 : 1 ≤ b) (hbQ1 : 1 ≤ bQ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hb : 2 * c₄ ≤ b * c₃) (hbQ : 2 * (b * c₂) ≤ bQ * c₁)
    (hL : c₁ ≤ pinchLocalL D Q' Q) (hA : pinchLocalA D W Q δ ≤ ENNReal.ofReal c₂)
    (hA0 : c₃ ≤ setDist D {0} (sphere (0 : ℂ) (δ / 2)))
    (hd0 : internalDiam D δ (closure (T \ thickening (3 * δ) W)) ≤ ENNReal.ofReal c₄)
    {φQ φ0 : ℂ → ℝ} (hφQ1 : ∀ z ∈ closure Q, φQ z = 1) (hφQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0)
    (hφQI : ∀ z, φQ z ∈ Icc (0 : ℝ) 1)
    (hφ01 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) (hφ00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0)
    (hφ0I : ∀ z, φ0 z ∈ Icc (0 : ℝ) 1)
    {f : ℂ → ℝ} (hfsum : ∀ z, ξ * f z = Real.log bQ * φQ z + Real.log b * φ0 z)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal)) :
    pinchFirstEventLocal (fun x y => (weylScaling D ξ f x y).toReal) W T Q' Q δ := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlbQ : 0 ≤ Real.log bQ := Real.log_nonneg hbQ1
  have hb0 : 0 < b := by linarith
  have hbQ0 : 0 < bQ := by linarith
  have hbc2 : 0 < b * c₂ := mul_pos hb0 hc₂
  have hbc3 : 0 < b * c₃ := mul_pos hb0 hc₃
  -- pointwise bounds on `ξ f`
  have hfle : ∀ z, ξ * f z ≤ Real.log bQ + Real.log b := fun z => by
    rw [hfsum z]
    linarith [mul_le_mul_of_nonneg_left (hφQI z).2 hlbQ, mul_le_mul_of_nonneg_left (hφ0I z).2 hlb]
  have hfge_Q : ∀ z ∈ closure Q, Real.log bQ ≤ ξ * f z := fun z hz => by
    rw [hfsum z, hφQ1 z hz]
    linarith [mul_nonneg hlb (hφ0I z).1]
  have hfge_0 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), Real.log b ≤ ξ * f z := fun z hz => by
    rw [hfsum z, hφ01 z hz]
    linarith [mul_nonneg hlbQ (hφQI z).1]
  have hfle_Ω : ∀ z ∈ pinchOmegaGeom W Q δ, ξ * f z ≤ Real.log b := fun z hz => by
    have hsub : thickening δ Q ⊆ thickening (2 * δ) (Q ∪ W) :=
      (thickening_mono (by linarith) Q).trans (thickening_subset_of_subset _ subset_union_left)
    have hzQ : z ∉ thickening δ Q := fun h => pinchOmegaGeom_subset W Q δ hz (hsub h)
    rw [hfsum z, hφQ0 z hzQ]
    linarith [mul_le_mul_of_nonneg_left (hφ0I z).2 hlb]
  have hfle_U : ∀ z ∈ thickening δ (closure (T \ thickening (3 * δ) W)), ξ * f z ≤ 0 := fun z hz => by
    obtain ⟨hzQ, hz0⟩ := thickening_K0_disjoint hgeo z hz
    rw [hfsum z, hφQ0 z hzQ, hφ00 z hz0]
    simp
  -- finiteness of the shifted metric
  have hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤ := by
    intro u v
    have hle : ∀ z, f z ≤ ξ⁻¹ * (Real.log bQ + Real.log b) := fun z => by
      refine le_of_mul_le_mul_left ?_ hξ
      rw [weight_xi_mul hξ]
      exact hfle z
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (weylScaling_le_const hD hξ.le hle u v)
  -- the `L` bound: `bQ L ≤ L_new`
  have hLnew : bQ * pinchLocalL D Q' Q ≤ pinchLocalL (fun x y => (weylScaling D ξ f x y).toReal) Q' Q := by
    have hF : (frontier Q).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      unfold pinchLocalL setDist at hL
      rw [h, Set.image2_empty_right, Real.sInf_empty] at hL
      linarith
    have hQ' : (closure Q').Nonempty := hgeo.isConnected_Q'.nonempty.closure
    have hQQ : closure Q' ⊆ closure Q := hgeo.closure_Q'_subset_Q.trans subset_closure
    have hfcQ : ∀ z ∈ closure Q, ξ⁻¹ * Real.log bQ ≤ f z := fun z hz => by
      refine le_of_mul_le_mul_left ?_ hξ
      rw [weight_xi_mul hξ]
      exact hfge_Q z hz
    have key := setDist_weylScaling_ge_frontier (c := ξ⁻¹ * Real.log bQ) (f := f) hD hξ.le hQQ hfcQ hfin hQ' hF
    have hexp : Real.exp (ξ * (ξ⁻¹ * Real.log bQ)) = bQ := by
      rw [weight_xi_mul hξ, Real.exp_log hbQ0]
    rw [hexp] at key
    unfold pinchLocalL
    exact key
  -- the `A` bound: `A_new ≤ b A ≤ b c₂`
  have hAnew : pinchLocalA (fun x y => (weylScaling D ξ f x y).toReal) W Q δ ≤ ENNReal.ofReal (b * c₂) := by
    refine (pinchLocalA_weylScaling_le hD hE hb0 hfin W Q δ hfle_Ω).trans ?_
    rw [ENNReal.ofReal_mul hb0.le]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  -- first conjunct: `A_new < L_new`
  have hfirst : pinchLocalA (fun x y => (weylScaling D ξ f x y).toReal) W Q δ <
      ENNReal.ofReal (pinchLocalL (fun x y => (weylScaling D ξ f x y).toReal) Q' Q) := by
    have h1 : ENNReal.ofReal (b * c₂) < ENNReal.ofReal (bQ * c₁) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have h2 : ENNReal.ofReal (bQ * c₁) ≤
        ENNReal.ofReal (pinchLocalL (fun x y => (weylScaling D ξ f x y).toReal) Q' Q) :=
      ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hL hbQ0.le).trans hLnew)
    exact lt_of_le_of_lt hAnew (h1.trans_le h2)
  -- second conjunct: `d₀,new ≤ d₀ ≤ c₄ < b c₃ ≤ a₀,new`
  have hsecond : internalDiam (fun x y => (weylScaling D ξ f x y).toReal) δ
      (closure (T \ thickening (3 * δ) W)) <
      ENNReal.ofReal (setDist (fun x y => (weylScaling D ξ f x y).toReal) {0} (sphere (0 : ℂ) δ)) := by
    have hd0' := (internalDiam_weylScaling_le hD hE hfin hfle_U).trans hd0
    have hexp : Real.exp (ξ * (ξ⁻¹ * Real.log b)) = b := by
      rw [weight_xi_mul hξ, Real.exp_log hb0]
    have hfc0 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), ξ⁻¹ * Real.log b ≤ f z := fun z hz => by
      refine le_of_mul_le_mul_left ?_ hξ
      rw [weight_xi_mul hξ]
      exact hfge_0 z hz
    have hS := setDist_weylScaling_ge_sphere (c := ξ⁻¹ * Real.log b) (f := f) hD hξ.le hδ hfc0 hfin
    rw [hexp] at hS
    have hS' : b * c₃ ≤ setDist (fun x y => (weylScaling D ξ f x y).toReal) {0} (sphere (0 : ℂ) δ) :=
      (mul_le_mul_of_nonneg_left hA0 hb0.le).trans hS
    exact lt_of_le_of_lt hd0' ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  unfold pinchFirstEventLocal
  exact ⟨hfirst, hsecond⟩
