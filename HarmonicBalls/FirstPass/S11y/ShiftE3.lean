import HarmonicBalls.FirstPass.S11y.ShiftGeom
import HarmonicBalls.FirstPass.S11m.E1Bounds
import HarmonicBalls.FirstPass.S11m.WeylShift
import HarmonicBalls.FirstPass.S11i.Crossing
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds

/-!
# The deterministic third shift (Lemma 11.12, E3; corrected paper lines 3729-3755, z4 note §6.4)

For the shift `f = ξ⁻¹ log k · φ` (`φ` the bump of `ShiftGeom.lean`, `0 < k ≤ 1`), a field whose metric `D` satisfies
the first and second local events and has `a₂ ≥ c`, `d₂ ≤ d` with `k d ≤ c/2`, keeps `E₁` and `E₂` and satisfies `E₃`
after the shift. Notation: `a₀, a₁, a₂, L` are the setDist quantities (lower bounds only: they are unchanged up to a
lower bound, since the weight is `0` near them); `A, d₀, d₁` are internal quantities (they only decrease, weight `≤ 0`);
`d₂` is scaled by at most `k` (weight `log k / ξ` on `thickening δ K₂`).

Only the weylScaling identities of FirstPass/S11m (E1Bounds, WeylShift) and Steps (WeylAnnulusBounds,
PinchMeasureWeylShift) are used. The length-metric property of the shifted metric is a hypothesis (`hE`) here;
`ShiftLength.lean` derives it for a smooth compactly supported bump (`shiftLength_of_bump`), so this file needs no
frozen input.
-/

open MeasureTheory Set Metric Filter
open HarmonicBalls.S11m HarmonicBalls.S11m.E1Bounds FirstPassS11i

namespace HarmonicBalls
namespace S11y

variable {D : ℂ → ℂ → ℝ}

/-- The shift weight `ξ⁻¹ · log k · φ` (paper `u = ξ⁻¹ log k φ`). -/
noncomputable def shiftWeight3 (ξ k : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ :=
  fun z => ξ⁻¹ * (Real.log k * φ z)

lemma weylScaling_ne_top_of_nonpos (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hf : ∀ z, f z ≤ 0) (u v : ℂ) : weylScaling D ξ f u v ≠ ⊤ := by
  have h : weylScaling D ξ f u v ≤ weylScaling D ξ 0 u v :=
    weylScaling_mono hξ (g := 0) (fun z => hf z) u v
  rw [hD.weylScaling_zero ξ u v] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- Internal comparison: the shifted internal metric on `U` is at most `e^B` times the original one. -/
lemma internalMetric_shift_le (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) {B : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hw : ∀ z ∈ U, ξ * f z ≤ B) (x y : ℂ) :
    internalMetric (fun x y => (weylScaling D ξ f x y).toReal) U x y ≤
      ENNReal.ofReal (Real.exp B) * internalMetric D U x y :=
  hD.internalMetric_weylScaling_le hE (fun _ _ => ENNReal.toReal_nonneg) hU (hD.weylScaling_zero ξ)
    (fun u v => ENNReal.ofReal_toReal (hfin u v)) hw x y

lemma internalMetric_shift_le_zero (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) {U : Set ℂ} (hU : IsOpen U)
    (hw : ∀ z ∈ U, ξ * f z ≤ 0) (x y : ℂ) :
    internalMetric (fun x y => (weylScaling D ξ f x y).toReal) U x y ≤ internalMetric D U x y := by
  simpa using internalMetric_shift_le hD hE hfin hU hw x y

/-- Internal diameter comparison: `internalDiam` of the shifted metric is at most `e^B` times the original one,
provided the weight satisfies `ξ f ≤ B` on the thickening `thickening δ A` (the domain of `internalDiam`). -/
lemma internalDiam_shift_le (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) {B δ : ℝ} {A : Set ℂ}
    (hw : ∀ z ∈ thickening δ A, ξ * f z ≤ B) :
    internalDiam (fun x y => (weylScaling D ξ f x y).toReal) δ A ≤
      ENNReal.ofReal (Real.exp B) * internalDiam D δ A := by
  unfold internalDiam
  calc (⨆ x ∈ A, ⨆ y ∈ A, internalMetric (fun x y => (weylScaling D ξ f x y).toReal) (thickening δ A) x y)
      ≤ ⨆ x ∈ A, ⨆ y ∈ A, ENNReal.ofReal (Real.exp B) * internalMetric D (thickening δ A) x y :=
        iSup₂_mono fun x _ => iSup₂_mono fun y _ =>
          internalMetric_shift_le hD hE hfin isOpen_thickening hw x y
    _ = ENNReal.ofReal (Real.exp B) * ⨆ x ∈ A, ⨆ y ∈ A, internalMetric D (thickening δ A) x y := by
        simp only [ENNReal.mul_iSup]

lemma internalDiam_shift_le_zero (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) {δ : ℝ} {A : Set ℂ}
    (hw : ∀ z ∈ thickening δ A, ξ * f z ≤ 0) :
    internalDiam (fun x y => (weylScaling D ξ f x y).toReal) δ A ≤ internalDiam D δ A := by
  simpa using internalDiam_shift_le hD hE hfin (B := 0) hw

/-- Lower bound for a setDist across the frontier of `Q`: the weight vanishes on `closure Q`, so the shifted
setDist between `S ⊆ Q` and `T = frontier Q` is at least the original one (exit point argument of
`weylScaling_ge_of_exit`). -/
lemma setDist_le_setDist_shift (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hf : ∀ z, f z ≤ 0) {Q S T : Set ℂ} (_hQ : IsOpen Q) (hSQ : S ⊆ Q) (hfQ : ∀ z ∈ closure Q, f z = 0)
    (hTQ : frontier Q = T) (hS : S.Nonempty) (hT : T.Nonempty) :
    setDist D S T ≤ setDist (fun x y => (weylScaling D ξ f x y).toReal) S T := by
  subst hTQ
  refine le_setDist_weylScaling hS hT (fun u v => weylScaling_ne_top_of_nonpos hD hξ hf u v) ?_
  intro u hu v hv
  have hr : ∀ w ∈ frontier Q, setDist D S (frontier Q) ≤ D u w := fun w hw => setDist_le_of_mem hD hu hw
  have h := weylScaling_ge_of_exit hD hξ (c := 0) (fun z hz => le_of_eq (hfQ z hz).symm)
    (subset_closure (hSQ hu)) hv.2 hr
  simpa using h

/-- A weight `≤ 0` vanishing outside `thickening (6δ) W` vanishes on the closed balls of radius `R < 1 - 6δ`. -/
lemma weight_zero_on_closure_ball {W : Set ℂ} (hW : W ⊆ annulus (0 : ℂ) 1 2) {δ R : ℝ}
    (hR : R < 1 - 6 * δ) {f : ℂ → ℝ} (hf : ∀ z, z ∉ thickening (6 * δ) W → f z = 0) :
    ∀ z ∈ closure (ball (0 : ℂ) R), f z = 0 := by
  intro z hz
  apply hf
  intro hzW
  have h1 : ‖z‖ ≤ R := by
    have h := closure_ball_subset_closedBall hz
    rw [mem_closedBall, dist_zero_right] at h
    exact h
  have h2 := (norm_bounds_of_thickening hW hzW).1
  linarith

/-- A bounded set with a nonempty subset in `ℂ` has nonempty frontier (ℂ is connected). -/
lemma frontier_nonempty_of_bounded {Q S : Set ℂ} (hQb : Bornology.IsBounded Q) (hSQ : S ⊆ Q)
    (hS : S.Nonempty) : (frontier Q).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hcl : closure Q ⊆ interior Q := fun x hx => by
    by_contra hx'
    have hfr : x ∈ frontier Q := ⟨hx, hx'⟩
    rw [h] at hfr
    exact hfr
  have hQcl : IsClosed Q := isClosed_of_closure_subset (hcl.trans interior_subset)
  have hQeq : Q = interior Q := Set.Subset.antisymm (fun x hx => hcl (subset_closure hx)) interior_subset
  have hQop : IsOpen Q := by rw [hQeq]; exact isOpen_interior
  rcases isClopen_iff.1 ⟨hQcl, hQop⟩ with h0 | hT
  · obtain ⟨x, hx⟩ := hS
    have hx' := hSQ hx
    rw [h0] at hx'
    exact hx'
  · obtain ⟨R, hR⟩ := hQb.subset_closedBall 0
    rw [hT] at hR
    have h1 := hR (mem_univ ((|R| + 1 : ℝ) : ℂ))
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |R| + 1)] at h1
    linarith [le_abs_self R]

/-- `L` is at least the original one (the weight vanishes on `closure Q`). -/
theorem pinchLocal_shift_L (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hf : ∀ z, f z ≤ 0) {Q Q' : Set ℂ} (hQ : IsOpen Q) (hQ'Q : closure Q' ⊆ Q)
    (hfQ : ∀ z ∈ closure Q, f z = 0) (hQ'ne : (closure Q').Nonempty) (hFr : (frontier Q).Nonempty) :
    setDist D (closure Q') (frontier Q) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) (closure Q') (frontier Q) :=
  setDist_le_setDist_shift hD hξ hf hQ hQ'Q hfQ rfl hQ'ne hFr

/-- Shifted `pinchLocalA` (sup of internal distances from `0` to the sphere of radius `5`) does not increase. -/
lemma pinchLocalA_shift_le (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤) (hwall : ∀ z, ξ * f z ≤ 0) (W Q : Set ℂ) (δ : ℝ) :
    pinchLocalA (fun x y => (weylScaling D ξ f x y).toReal) W Q δ ≤ pinchLocalA D W Q δ := by
  unfold pinchLocalA
  exact iSup₂_mono fun x _ =>
    internalMetric_shift_le_zero hD hE hfin (pinchOmegaGeom_isOpen W Q δ) (fun z _ => hwall z) 0 x

/-- Main statement (`E₁`, `E₂`, `E₃` after the shift). Hypotheses: `hgeo` buffered geometry; `hD` length metric
of the field; `φ` the bump (`ShiftGeom.exists_pinchShift_bump`); `hE` the length-metric property of the shifted
metric (frozen input); `hE1`, `hE2` the events on `D`; `ha2 : c ≤ a₂ D`; `hd2 : d₂ D ≤ d`; `k d ≤ c/2`. -/
theorem pinchLocal_E3_of_shift {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hD : IsEuclideanLengthMetric D) {μ : Measure ℂ} {γ ξ M c d k : ℝ}
    (hξ : 0 < ξ) (hk0 : 0 < k) (hk1 : k ≤ 1) (hc : 0 < c) (hkcd : k * d ≤ c / 2)
    {φ : ℂ → ℝ} (hφ01 : ∀ z, φ z ∈ Icc (0 : ℝ) 1)
    (hφ1 : ∀ z ∈ closure (thickening δ (pinchK2 W V δ)), φ z = 1)
    (hφU : ∀ z ∈ closure U, φ z = 0) (hφout : ∀ z, z ∉ thickening (6 * δ) W → φ z = 0)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal))
    (hE1 : pinchFirstEventLocal D W T Q' Q δ) (hE2 : pinchSecondEventLocal μ D U V δ M)
    (ha2 : c ≤ setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))
    (hd2 : internalDiam D δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal d) :
    pinchFirstEventLocal (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) W T Q' Q δ ∧
    pinchSecondEventLocal (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * shiftWeight3 ξ k φ x)))
      (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) U V δ M ∧
    pinchThirdEventLocal (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) V W δ := by
  set f := shiftWeight3 ξ k φ with hf_def
  have hδ : 0 < δ := hgeo.delta_pos
  have hδ1 : δ < 1 / 1000 := hgeo.delta_lt
  have hξ0 : (0 : ℝ) ≤ ξ := hξ.le
  -- sign and vanishing of the weight
  have hf_nonpos : ∀ z, f z ≤ 0 := by
    intro z
    have hlog : Real.log k ≤ 0 := Real.log_nonpos hk0.le hk1
    have h2 : Real.log k * φ z ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hlog, (hφ01 z).1⟩)
    rw [hf_def]
    show ξ⁻¹ * (Real.log k * φ z) ≤ 0
    exact mul_nonpos_iff.2 (Or.inl ⟨inv_nonneg.2 hξ0, h2⟩)
  have hwall : ∀ z, ξ * f z ≤ 0 := fun z => mul_nonpos_iff.2 (Or.inl ⟨hξ0, hf_nonpos z⟩)
  have hfout : ∀ z, z ∉ thickening (6 * δ) W → f z = 0 := by
    intro z hz
    rw [hf_def]
    simp [shiftWeight3, hφout z hz]
  have hfU : ∀ z ∈ closure U, f z = 0 := by
    intro z hz
    rw [hf_def]
    simp [shiftWeight3, hφU z hz]
  have hfK : ∀ z ∈ thickening δ (pinchK2 W V δ), ξ * f z = Real.log k := by
    intro z hz
    rw [hf_def]
    show ξ * (ξ⁻¹ * (Real.log k * φ z)) = Real.log k
    rw [hφ1 z (subset_closure hz), mul_one, mul_inv_cancel_left₀ hξ.ne']
  have hfin : ∀ u v, weylScaling D ξ f u v ≠ ⊤ := weylScaling_ne_top_of_nonpos hD hξ0 hf_nonpos
  -- the sets where the weight vanishes
  have hfQ : ∀ z ∈ closure Q, f z = 0 := fun z hz =>
    hfout z (fun h6 => not_mem_closure_Q_of_thickening hgeo hδ h6 hz)
  have hsph : ∀ R : ℝ, R < 1 - 6 * δ → ∀ z ∈ closure (ball (0 : ℂ) R), f z = 0 := fun R hR =>
    weight_zero_on_closure_ball hgeo.W_subset hR hfout
  have hne_sph : ∀ R : ℝ, 0 < R → (sphere (0 : ℂ) R).Nonempty := fun R hR =>
    NormedSpace.sphere_nonempty.2 hR.le
  -- E₁: lower bounds for L and a₀, upper bound for A and d₀
  have hQsub : Q ⊆ closedBall (0 : ℂ) 5 := fun z hz =>
    mem_closedBall.2 (le_of_lt (mem_ball.1 ((hgeo.closure_Q_subset (subset_closure hz)).1).1))
  have hFr : (frontier Q).Nonempty :=
    frontier_nonempty_of_bounded (isBounded_closedBall.subset hQsub)
      (subset_closure.trans hgeo.closure_Q'_subset_Q) hgeo.isConnected_Q'.nonempty
  have hL : setDist D (closure Q') (frontier Q) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) (closure Q') (frontier Q) :=
    pinchLocal_shift_L hD hξ0 hf_nonpos hgeo.isOpen_Q hgeo.closure_Q'_subset_Q hfQ
      (hgeo.isConnected_Q'.nonempty.closure) hFr
  have ha0 : setDist D {0} (sphere 0 δ) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) {0} (sphere 0 δ) :=
    setDist_le_setDist_shift hD hξ0 hf_nonpos isOpen_ball
      (singleton_subset_iff.2 (mem_ball_self hδ))
      (hsph δ (by linarith)) (frontier_ball _ hδ.ne') (Set.singleton_nonempty _) (hne_sph δ hδ)
  have hA := pinchLocalA_shift_le hD hE hfin hwall W Q δ
  have hd0 := internalDiam_shift_le_zero hD hE hfin (δ := δ)
    (A := closure (T \ thickening (3 * δ) W)) (fun z _ => hwall z)
  have hE1' : pinchFirstEventLocal (fun x y => (weylScaling D ξ f x y).toReal) W T Q' Q δ := by
    unfold pinchFirstEventLocal pinchLocalL at hE1 ⊢
    exact ⟨lt_of_le_of_lt hA (lt_of_lt_of_le hE1.1 (ENNReal.ofReal_le_ofReal hL)),
      lt_of_le_of_lt hd0 (lt_of_lt_of_le hE1.2 (ENNReal.ofReal_le_ofReal ha0))⟩
  -- E₂: the measure terms are unchanged; the internal diameter decreases; a₁ is bounded below
  have hA1 : setDist D (sphere 0 δ) (sphere 0 (2 * δ)) ≤
      setDist (fun x y => (weylScaling D ξ f x y).toReal) (sphere 0 δ) (sphere 0 (2 * δ)) :=
    setDist_le_setDist_shift hD hξ0 hf_nonpos isOpen_ball
      (fun z hz => mem_ball.2 (by rw [mem_sphere.1 hz]; linarith))
      (hsph (2 * δ) (by linarith)) (frontier_ball _ (ne_of_gt (by linarith))) (hne_sph δ hδ)
      (hne_sph (2 * δ) (by linarith))
  have hmeasU : MeasurableSet U := hgeo.isOpen_U.measurableSet
  have hMU := restrict_withDensity_exp_eq_of_eq_zero μ γ f hmeasU (fun x hx => hfU x (subset_closure hx))
  have hmassU : (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) U = μ U := by
    have h := congrArg (fun ν : Measure ℂ => ν U) hMU
    simpa only [Measure.restrict_apply hmeasU, inter_self] using h
  have hann : ∀ x ∈ annulus (0 : ℂ) 3 6, f x = 0 := by
    intro x hx
    apply hfout x
    intro h6
    have h1 := (norm_bounds_of_thickening hgeo.W_subset h6).2
    have h2 : 3 < ‖x‖ := not_le.1 (fun h => hx.2 (by rw [mem_closedBall, dist_zero_right]; exact h))
    linarith
  have hSann := annulusGreenPotentialSup_eq_of_restrict_eq 0 3 6
    (restrict_withDensity_exp_eq_of_eq_zero μ γ f (measurableSet_ball.diff measurableSet_closedBall) hann)
  have hE2' : pinchSecondEventLocal (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
      (fun x y => (weylScaling D ξ f x y).toReal) U V δ M := by
    unfold pinchSecondEventLocal at hE2 ⊢
    refine ⟨lt_of_le_of_lt (internalDiam_shift_le_zero hD hE hfin (δ := δ) (A := closure V) (fun z _ => hwall z))
      (lt_of_lt_of_le hE2.1 (ENNReal.ofReal_le_ofReal hA1)), ?_⟩
    rw [hSann, hmassU]
    exact hE2.2
  -- E₃: d₂ is multiplied by at most k, and a₂ is bounded below by c
  have ha2' : c ≤ setDist (fun x y => (weylScaling D ξ f x y).toReal) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)) := by
    have h := setDist_le_setDist_shift hD hξ0 hf_nonpos isOpen_ball
      (fun z hz => mem_ball.2 (by rw [mem_sphere.1 hz]; linarith))
      (hsph (3 * δ) (by linarith)) (frontier_ball _ (ne_of_gt (by linarith)))
      (hne_sph (2 * δ) (by linarith)) (hne_sph (3 * δ) (by linarith))
    exact le_trans ha2 h
  have hE3 : pinchThirdEventLocal (fun x y => (weylScaling D ξ f x y).toReal) V W δ := by
    unfold pinchThirdEventLocal
    have hd2' := internalDiam_shift_le hD hE hfin (B := Real.log k) (δ := δ) (A := pinchK2 W V δ)
      (fun z hz => (hfK z hz).le)
    rw [Real.exp_log hk0] at hd2'
    calc internalDiam (fun x y => (weylScaling D ξ f x y).toReal) δ (closure (thickening (3 * δ) W \ V))
        ≤ ENNReal.ofReal k * internalDiam D δ (closure (thickening (3 * δ) W \ V)) := hd2'
      _ ≤ ENNReal.ofReal k * ENNReal.ofReal d := by gcongr
      _ = ENNReal.ofReal (k * d) := (ENNReal.ofReal_mul hk0.le).symm
      _ ≤ ENNReal.ofReal (c / 2) := ENNReal.ofReal_le_ofReal hkcd
      _ < ENNReal.ofReal c := (ENNReal.ofReal_lt_ofReal_iff hc).2 (by linarith)
      _ ≤ ENNReal.ofReal (setDist (fun x y => (weylScaling D ξ f x y).toReal) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) :=
        ENNReal.ofReal_le_ofReal ha2'
  exact ⟨hE1', hE2', hE3⟩

end S11y
end HarmonicBalls
