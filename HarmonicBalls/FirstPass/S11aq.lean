import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11c.GreenTranslate11_7
import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph

/-!
# Translation covariance and measure-side locality of the certificate event

Deterministic inputs for Steps 6-7 of Lemma 11.13 (the rooted identification; `FirstPass/S11ai/RootedInstance.lean`,
the hypotheses `hCov` and `hG` there):

* `certificateEvent_translate_iff` (translation covariance). The certificate event of the translated pair
  `(μ.map (· - a), D(· + a, · + a))` at centre `z` is the certificate event of `(μ, D)` at the translated centre `z + a`.
  Here `μ.map (· - a)` is the translate `S ↦ μ(S + a)` (the mass of the translated field) and `D(· + a, · + a)` is the
  translated length metric.
* `certificateEvent_measure_congr` (measure-side locality). The certificate event depends on the mass measure only through
  its restriction to the closed ball `closedBall z (7 r)`. This is the measure analogue of
  `FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall` (S11al), which does the same for the metric.
  The only containment needed is `U ⊆ B₇`, which is the buffer `U ⊆ 𝔸_{1,2}` of `IsBufferedPinchGeometry`.

Existing inputs (no new mathematics): `iSup_internalMetric_comp_homeomorph`, `setDist_comp_homeomorph`,
`iSup_iSup_internalMetric_comp_homeomorph` (`Steps/Sec11/InternalMetricHomeomorph.lean`);
`annulusGreenPotentialSup_map_add_right` (`S11c/GreenTranslate11_7.lean`); `rescaledSet_subset_closedBall'` (S11al);
`annulus_subset_closedBall'` (S11ap). Certificate notation: `FirstPass/S11i/Certificate.lean:42`.
-/

namespace FirstPassS11aq

open MeasureTheory Metric Set
open HarmonicBalls FirstPassS11i

/-! ## Translation of the metric pieces -/

/-- The image of a rescaled set under the translation `w ↦ w + a` is the rescaled set about the translated centre. -/
lemma image_addRight_rescaledSet (a : ℂ) (S : Set ℂ) (r : ℝ) (z : ℂ) :
    (fun w : ℂ => w + a) '' rescaledSet S r z = rescaledSet S r (z + a) := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by push_cast; ring⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(r : ℂ) * x + z, ⟨x, hx, rfl⟩, by push_cast; ring⟩

/-- The image of a sphere under the translation `w ↦ w + a` is the sphere about the translated centre. -/
lemma image_addRight_sphere (a z : ℂ) (s : ℝ) :
    (fun w : ℂ => w + a) '' sphere z s = sphere (z + a) s := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_sphere] at hx
    rw [mem_sphere]
    show dist (x + a) (z + a) = s
    rw [dist_add_right]
    exact hx
  · intro hw
    rw [mem_sphere] at hw
    refine ⟨w - a, ?_, by simp⟩
    rw [mem_sphere]
    have h := dist_add_right (w - a) z a
    rw [sub_add_cancel] at h
    rw [← h]
    exact hw

/-- The image of a point under the translation `w ↦ w + a` is the translated point. -/
lemma image_addRight_singleton (a z : ℂ) : (fun w : ℂ => w + a) '' {z} = {z + a} := by
  simp

/-- The image of a closure under the translation `w ↦ w + a`. -/
lemma image_addRight_closure (a : ℂ) (S : Set ℂ) :
    (fun w : ℂ => w + a) '' closure S = closure ((fun w : ℂ => w + a) '' S) :=
  (Homeomorph.addRight a).image_closure S

/-- The image of a frontier under the translation `w ↦ w + a`. -/
lemma image_addRight_frontier (a : ℂ) (S : Set ℂ) :
    (fun w : ℂ => w + a) '' frontier S = frontier ((fun w : ℂ => w + a) '' S) :=
  (Homeomorph.addRight a).image_frontier S

/-- The image of a thickening under the translation `w ↦ w + a`. -/
lemma image_addRight_thickening (a : ℂ) (δ : ℝ) (A : Set ℂ) :
    (fun w : ℂ => w + a) '' thickening δ A = thickening δ ((fun w : ℂ => w + a) '' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.1 hx
    refine mem_thickening_iff.2 ⟨p + a, ⟨p, hp, rfl⟩, ?_⟩
    simpa [dist_add_right] using hxp
  · intro hy
    obtain ⟨_, ⟨p, hp, rfl⟩, hpy⟩ := mem_thickening_iff.1 hy
    refine ⟨y - a, mem_thickening_iff.2 ⟨p, hp, ?_⟩, by simp⟩
    have h := dist_add_right (y - a) p a
    rw [sub_add_cancel] at h
    rw [← h]
    exact hpy

/-- Translation of the `iSup` of internal metrics: the centre is fixed and the second point moves. -/
lemma iSup_internalMetric_translate (D : ℂ → ℂ → ℝ) (a : ℂ) (U A : Set ℂ) (x : ℂ) :
    (⨆ y ∈ A, internalMetric (fun u v => D (u + a) (v + a)) U x y) =
      ⨆ y ∈ (fun w : ℂ => w + a) '' A, internalMetric D ((fun w : ℂ => w + a) '' U) (x + a) y :=
  iSup_internalMetric_comp_homeomorph D (Homeomorph.addRight a) U A x

/-- Translation of the set distance. -/
lemma setDist_translate (D : ℂ → ℂ → ℝ) (a : ℂ) (A B : Set ℂ) :
    setDist (fun u v => D (u + a) (v + a)) A B =
      setDist D ((fun w : ℂ => w + a) '' A) ((fun w : ℂ => w + a) '' B) :=
  setDist_comp_homeomorph D (Homeomorph.addRight a) A B

/-- Translation of the internal diameter `diam^δ`. -/
lemma internalDiam_translate (D : ℂ → ℂ → ℝ) (a : ℂ) (δ : ℝ) (A : Set ℂ) :
    internalDiam (fun u v => D (u + a) (v + a)) δ A =
      internalDiam D δ ((fun w : ℂ => w + a) '' A) := by
  unfold internalDiam
  refine (iSup_iSup_internalMetric_comp_homeomorph D (Homeomorph.addRight a) (thickening δ A) A).trans ?_
  show ⨆ x ∈ (fun w : ℂ => w + a) '' A, ⨆ y ∈ (fun w : ℂ => w + a) '' A,
      internalMetric D ((fun w : ℂ => w + a) '' thickening δ A) x y = _
  rw [image_addRight_thickening]

/-! ## Translation of the mass measure and of the annulus potential -/

/-- The preimage of a rescaled set under the translation `w ↦ w - a` is the rescaled set about `z + a`. -/
lemma map_sub_preimage_rescaledSet (a : ℂ) (U : Set ℂ) (r : ℝ) (z : ℂ) :
    (fun w : ℂ => w - a) ⁻¹' rescaledSet U r z = rescaledSet U r (z + a) := by
  rw [← image_addRight_rescaledSet a U r z]
  ext w
  constructor
  · intro hw
    exact ⟨w - a, hw, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- The translated mass of a rescaled set: `(μ.map (· - a))(rescaledSet U r z) = μ(rescaledSet U r (z + a))`. -/
lemma map_sub_apply_rescaledSet (μ : Measure ℂ) (a : ℂ) (U : Set ℂ) (r : ℝ) (z : ℂ) :
    (μ.map (fun w : ℂ => w - a)) (rescaledSet U r z) = μ (rescaledSet U r (z + a)) := by
  rw [← map_sub_preimage_rescaledSet a U r z]
  exact MeasurableEquiv.map_apply (MeasurableEquiv.subRight a) _

/-- Centre translation of the annulus potential, with the centre moved to `0`:
`SG(ν.map (· - c), 0) = SG(ν, c)`, from `annulusGreenPotentialSup_map_add_right`. -/
lemma annulusGreenPotentialSup_map_sub_centre (ν : Measure ℂ) (c : ℂ) (s t : ℝ) :
    annulusGreenPotentialSup (ν.map (fun w : ℂ => w - c)) 0 s t = annulusGreenPotentialSup ν c s t := by
  have key : ∀ (ρ : Measure ℂ) (d : ℂ), (ρ.map (fun w : ℂ => w - d)).map (fun w : ℂ => w + d) = ρ := by
    intro ρ d
    have hm1 : Measurable (fun w : ℂ => w - d) := by fun_prop
    have hm2 : Measurable (fun w : ℂ => w + d) := by fun_prop
    rw [Measure.map_map hm2 hm1]
    have hid : ((fun w : ℂ => w + d) ∘ (fun w : ℂ => w - d)) = id := by
      funext w
      simp
    rw [hid, Measure.map_id]
  have h := HarmonicBalls.S11c.annulusGreenPotentialSup_map_add_right (ν.map (fun w : ℂ => w - c)) c s t
  rw [key] at h
  exact h.symm

/-- The annulus potential of the translated mass is the potential at the translated centre:
`SG(μ.map (· - a), z) = SG(μ, z + a)`. -/
lemma annulusGreenPotentialSup_map_sub_shift (μ : Measure ℂ) (a z : ℂ) (s t : ℝ) :
    annulusGreenPotentialSup (μ.map (fun w : ℂ => w - a)) z s t = annulusGreenPotentialSup μ (z + a) s t := by
  have hm1 : Measurable (fun w : ℂ => w - z) := by fun_prop
  have hm2 : Measurable (fun w : ℂ => w - a) := by fun_prop
  rw [← annulusGreenPotentialSup_map_sub_centre (μ.map (fun w : ℂ => w - a)) z s t, Measure.map_map hm1 hm2,
    ← annulusGreenPotentialSup_map_sub_centre μ (z + a) s t]
  have hc : ((fun w : ℂ => w - z) ∘ (fun w : ℂ => w - a)) = (fun w : ℂ => w - (z + a)) := by
    funext w
    simp only [Function.comp_apply]
    ring
  rw [hc]

/-! ## Translation covariance of the certificate event -/

/-- **Translation covariance of the certificate event (Lemma 11.13, Steps 6-7).** The certificate event of the translated
mass `μ.map (· - a)` and the translated length metric `D(· + a, · + a)` at centre `z` is the certificate event of
`(μ, D)` at the translated centre `z + a`. Each of the five metric quantities and the two mass quantities of
`CertificateEvent` is transported by the translation `w ↦ w + a`. -/
theorem certificateEvent_translate_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z a : ℂ) :
    CertificateEvent (μ.map (fun w : ℂ => w - a)) (fun x y => D (x + a) (y + a)) Ostar U V W T Q' Q η M r z ↔
      CertificateEvent μ D Ostar U V W T Q' Q η M r (z + a) := by
  unfold CertificateEvent
  rw [iSup_internalMetric_translate D a (rescaledSet Ostar r z) (sphere z (5 * r)) z,
    setDist_translate D a (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z)),
    internalDiam_translate D a (r * η) (rescaledSet (certK0 T W η) r z),
    setDist_translate D a {z} (sphere z (r * η)),
    internalDiam_translate D a (r * η) (rescaledSet (certK1 V) r z),
    setDist_translate D a (sphere z (r * η)) (sphere z (2 * r * η)),
    internalDiam_translate D a (r * η) (rescaledSet (certK2 V W η) r z),
    setDist_translate D a (sphere z (2 * r * η)) (sphere z (3 * r * η)),
    map_sub_apply_rescaledSet μ a U r z,
    annulusGreenPotentialSup_map_sub_shift μ a z (3 * r) (6 * r)]
  simp only [image_addRight_rescaledSet, image_addRight_sphere, image_addRight_singleton,
    image_addRight_closure, image_addRight_frontier]

/-! ## Measure-side locality of the certificate event -/

/-- **Measure-side locality of the certificate event.** If `U ⊆ B₇` and the two masses agree on the closed ball
`closedBall z (7 r)`, then the certificate event is the same for both masses. Every mass quantity of
`CertificateEvent` (`μ (rescaledSet U r z)` and the annulus potential `SG_{3r,6r}(z)`) only sees `μ` inside
`closedBall z (7 r)`. The metric `D` is unchanged. -/
theorem certificateEvent_measure_congr {μ μ' : Measure ℂ} (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z : ℂ) (hr : 0 < r) (hU : U ⊆ closedBall 0 7)
    (hμ : μ.restrict (closedBall z (7 * r)) = μ'.restrict (closedBall z (7 * r))) :
    CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔ CertificateEvent μ' D Ostar U V W T Q' Q η M r z := by
  have hB : MeasurableSet (closedBall z (7 * r)) := measurableSet_closedBall
  have hA : ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall z (7 * r) → μ.restrict A = μ'.restrict A := by
    intro A hAm hAB
    calc μ.restrict A = (μ.restrict (closedBall z (7 * r))).restrict A := by
          rw [Measure.restrict_restrict hAm, inter_eq_left.2 hAB]
      _ = (μ'.restrict (closedBall z (7 * r))).restrict A := by rw [hμ]
      _ = μ'.restrict A := by rw [Measure.restrict_restrict hAm, inter_eq_left.2 hAB]
  have hS : ∀ S : Set ℂ, S ⊆ closedBall z (7 * r) → μ S = μ' S := by
    intro S hSB
    have h : μ.restrict (closedBall z (7 * r)) S = μ'.restrict (closedBall z (7 * r)) S := by rw [hμ]
    rw [Measure.restrict_apply' hB, Measure.restrict_apply' hB, inter_eq_left.2 hSB] at h
    exact h
  have hsup : annulusGreenPotentialSup μ z (3 * r) (6 * r) = annulusGreenPotentialSup μ' z (3 * r) (6 * r) := by
    have hAn : annulus z (3 * r) (6 * r) ⊆ closedBall z (7 * r) :=
      FirstPassS11ap.annulus_subset_closedBall' z (3 * r) (6 * r) (7 * r) (by linarith)
    have hAm : MeasurableSet (annulus z (3 * r) (6 * r)) :=
      measurableSet_ball.diff measurableSet_closedBall
    unfold annulusGreenPotentialSup
    rw [hA _ hAm hAn]
  have hrect : μ (rescaledSet U r z) = μ' (rescaledSet U r z) :=
    hS _ (rescaledSet_subset_closedBall' hr.le hU)
  unfold CertificateEvent
  rw [hsup, hrect]

/-- Measure-side locality for a buffered pinch geometry: the containment `U ⊆ B₇` is the buffer `U ⊆ 𝔸_{1,2}` of
`IsBufferedPinchGeometry`. -/
theorem certificateEvent_measure_congr_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) {μ μ' : Measure ℂ} (D : ℂ → ℂ → ℝ) (Ostar : Set ℂ)
    (η M r : ℝ) (z : ℂ) (hr : 0 < r)
    (hμ : μ.restrict (closedBall z (7 * r)) = μ'.restrict (closedBall z (7 * r))) :
    CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔ CertificateEvent μ' D Ostar U V W T Q' Q η M r z :=
  certificateEvent_measure_congr D Ostar U V W T Q' Q η M r z hr
    (hgeo.U_subset.trans (FirstPassS11ap.annulus_subset_closedBall' 0 1 2 7 (by norm_num))) hμ

end FirstPassS11aq

