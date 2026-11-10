import HarmonicBalls.FirstPass.S11i.Certificate
import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.InternalMetricPullback
import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph
import HarmonicBalls.FirstPass.S11i.PinchMeasurable

/-!
# Measurability of the internal distances of the corrected local certificate in `(ω, z)`
(fp-S11i-11-13, round 31; eq. (27) of `notes/fp-gaps/CHATGPT-n3-B1-B2.md`, section 5.1).

For a measurable family `D ω` of Euclidean length metrics, the internal distances occurring in `CertificateEvent`
are measurable in `(ω, z)`. The parametrisation `x ↦ r x + z` turns the `z`-dependent domain `rescaledSet O r z`
into the fixed domain `O` for the family `affFamily D r`, so the Steps lemmas `measurable_iSup_internalMetric`
and `iSup_internalMetric_comp_homeomorph` apply.
-/

namespace FirstPassS11i

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The affine homeomorphism `x ↦ r x + z`; `rescaledSet A r z = affHomeo r hr z '' A` (`Defs/Geometry.lean:172`). -/
noncomputable def affHomeo (r : ℝ) (hr : r ≠ 0) (z : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr)).trans (Homeomorph.addRight z)

lemma affHomeo_apply {r : ℝ} (hr : r ≠ 0) (z x : ℂ) : affHomeo r hr z x = (r : ℂ) * x + z := rfl

lemma affHomeo_zero {r : ℝ} (hr : r ≠ 0) (z : ℂ) : affHomeo r hr z 0 = z := by
  simp [affHomeo_apply]

/-- The reparametrised family `(ω, z) ↦ D ω (r a + z) (r b + z)`: its internal metrics on a fixed domain are the
internal metrics of `D ω` on the rescaled domain `rescaledSet O r z`. -/
def affFamily (D : Ω → ℂ → ℂ → ℝ) (r : ℝ) (p : Ω × ℂ) (a b : ℂ) : ℝ :=
  D p.1 ((r : ℂ) * a + p.2) ((r : ℂ) * b + p.2)

lemma measurable_affFamily_apply {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2) (r : ℝ) (a b : ℂ) :
    Measurable fun p : Ω × ℂ => affFamily D r p a b := by
  have hc : Measurable fun p : Ω × ℂ => (p.1, ((r : ℂ) * a + p.2, (r : ℂ) * b + p.2)) :=
    measurable_fst.prodMk ((measurable_const.add measurable_snd).prodMk (measurable_const.add measurable_snd))
  exact hDm.comp hc

omit [MeasurableSpace Ω] in
lemma isEuclideanLengthMetric_affFamily {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    {r : ℝ} (hr : r ≠ 0) (p : Ω × ℂ) : IsEuclideanLengthMetric (affFamily D r p) :=
  (hD p.1).comp_homeomorph (affHomeo r hr p.2)

omit [MeasurableSpace Ω] in
lemma internalMetric_affFamily (D : Ω → ℂ → ℂ → ℝ) {r : ℝ} (hr : r ≠ 0) (p : Ω × ℂ) (O : Set ℂ) (a b : ℂ) :
    internalMetric (affFamily D r p) O a b =
      internalMetric (D p.1) (rescaledSet O r p.2) (r * a + p.2) (r * b + p.2) :=
  internalMetric_comp_homeomorph (D p.1) (affHomeo r hr p.2) O a b

lemma affHomeo_image_sphere {r : ℝ} (hr : 0 < r) (z : ℂ) (s : ℝ) :
    affHomeo r hr.ne' z '' sphere (0 : ℂ) s = sphere z (r * s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hx
    rw [mem_sphere, affHomeo_apply, dist_eq_norm, add_sub_cancel_right, norm_mul, hx,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  · intro hy
    rw [mem_sphere, dist_eq_norm] at hy
    refine ⟨(y - z) / (r : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, hy,
        mul_div_cancel_left₀ s hr.ne']
    · rw [affHomeo_apply]
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring

lemma iSup_sphere_internalMetric_affine {D : ℂ → ℂ → ℝ} {r : ℝ} (hr : 0 < r) (z : ℂ) (O : Set ℂ) :
    (⨆ x ∈ sphere z (5 * r), internalMetric D (rescaledSet O r z) z x) =
      ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (fun a b => D ((r : ℂ) * a + z) ((r : ℂ) * b + z)) O 0 y := by
  have h := iSup_internalMetric_comp_homeomorph D (affHomeo r hr.ne' z) O (sphere (0 : ℂ) 5) 0
  rw [affHomeo_zero, affHomeo_image_sphere hr] at h
  rw [mul_comm 5 r] 
  exact h.symm

lemma thickening_rescaledSet {r : ℝ} (hr : 0 < r) (z : ℂ) (η : ℝ) (K : Set ℂ) :
    thickening (r * η) (rescaledSet K r z) = affHomeo r hr.ne' z '' thickening η K := by
  ext y
  simp only [mem_thickening_iff, mem_image, rescaledSet, affHomeo_apply]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · rintro ⟨w, ⟨k, hk, rfl⟩, hd⟩
    rw [dist_eq_norm] at hd
    refine ⟨(y - z) / (r : ℂ), ⟨k, hk, ?_⟩, ?_⟩
    · have h1 : (y - z) / (r : ℂ) - k = (y - ((r : ℂ) * k + z)) / r := by
        field_simp
        ring
      rw [dist_eq_norm, h1, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_iff₀ hr]
      linarith
    · rw [mul_div_assoc', mul_div_cancel_left₀ _ hr0, sub_add_cancel]
  · rintro ⟨x, ⟨k, hk, hkx⟩, rfl⟩
    rw [dist_eq_norm] at hkx
    refine ⟨(r : ℂ) * k + z, ⟨k, hk, rfl⟩, ?_⟩
    rw [dist_eq_norm, show (r : ℂ) * x + z - ((r : ℂ) * k + z) = r * (x - k) by ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_of_pos_left hkx hr

lemma internalDiam_rescaledSet_eq {D : ℂ → ℂ → ℝ} {r : ℝ} (hr : 0 < r) (z : ℂ) (η : ℝ) (K : Set ℂ) :
    (⨆ x ∈ rescaledSet K r z, ⨆ y ∈ rescaledSet K r z,
        internalMetric D (thickening (r * η) (rescaledSet K r z)) x y) =
      ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (fun a b => D ((r : ℂ) * a + z) ((r : ℂ) * b + z)) (thickening η K) x y := by
  have h := iSup_iSup_internalMetric_comp_homeomorph D (affHomeo r hr.ne' z) (thickening η K) K
  rw [thickening_rescaledSet hr z η K]
  exact h.symm

lemma measurable_sphere_sup_affine {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2) (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω x y, 0 ≤ D ω x y) {r : ℝ} (hr : 0 < r) {O : Set ℂ} (hO : IsOpen O)
    (h0 : (0 : ℂ) ∈ O) (hsph : sphere (0 : ℂ) 5 ⊆ O) :
    Measurable fun p : Ω × ℂ => ⨆ x ∈ sphere p.2 (5 * r), internalMetric (D p.1) (rescaledSet O r p.2) p.2 x := by
  have key : (fun p : Ω × ℂ => ⨆ x ∈ sphere p.2 (5 * r), internalMetric (D p.1) (rescaledSet O r p.2) p.2 x) =
      fun p : Ω × ℂ => ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (affFamily D r p) O 0 y := by
    funext p
    exact iSup_sphere_internalMetric_affine hr p.2 O
  rw [key]
  have hnn : ∀ p : Ω × ℂ, ∀ x y : ℂ, 0 ≤ affFamily D r p x y := fun p x y => hnonneg p.1 _ _
  have hmeas : ∀ x ∈ ({0} : Set ℂ), ∀ y ∈ sphere (0 : ℂ) 5,
      Measurable fun p : Ω × ℂ => internalMetric (affFamily D r p) O x y := by
    intro x hx y _
    rw [mem_singleton_iff] at hx
    subst hx
    exact measurable_internalMetric_of_lengthMetric hO h0 y (fun a b => measurable_affFamily_apply hDm r a b)
      (fun p => isEuclideanLengthMetric_affFamily hD hr.ne' p)
  have hm := measurable_iSup_internalMetric (D := affFamily D r) (V := O) (A := {0})
    (B := sphere (0 : ℂ) 5) hO (singleton_subset_iff.2 h0) hsph
    (fun p => isEuclideanLengthMetric_affFamily hD hr.ne' p) hnn hmeas
  simpa only [iSup_singleton] using hm

lemma measurable_internalDiam_affine {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2) (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω x y, 0 ≤ D ω x y) {r : ℝ} (hr : 0 < r) {η : ℝ} (hη : 0 < η) (K : Set ℂ) :
    Measurable fun p : Ω × ℂ => ⨆ x ∈ rescaledSet K r p.2, ⨆ y ∈ rescaledSet K r p.2,
      internalMetric (D p.1) (thickening (r * η) (rescaledSet K r p.2)) x y := by
  have key : (fun p : Ω × ℂ => ⨆ x ∈ rescaledSet K r p.2, ⨆ y ∈ rescaledSet K r p.2,
      internalMetric (D p.1) (thickening (r * η) (rescaledSet K r p.2)) x y) =
      fun p : Ω × ℂ => ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (affFamily D r p) (thickening η K) x y := by
    funext p
    exact internalDiam_rescaledSet_eq hr p.2 η K
  rw [key]
  have hsub : K ⊆ thickening η K := self_subset_thickening hη K
  have hmeas : ∀ x ∈ K, ∀ y ∈ K, Measurable fun p : Ω × ℂ => internalMetric (affFamily D r p) (thickening η K) x y :=
    fun x hx y _ => measurable_internalMetric_of_lengthMetric isOpen_thickening (hsub hx) y
      (fun a b => measurable_affFamily_apply hDm r a b) (fun p => isEuclideanLengthMetric_affFamily hD hr.ne' p)
  exact measurable_iSup_internalMetric isOpen_thickening hsub hsub
    (fun p => isEuclideanLengthMetric_affFamily hD hr.ne' p) (fun p x y => hnonneg p.1 _ _) hmeas

/-- Distances between two concentric spheres and from the closure: measurable in `(ω, z)`. -/
lemma measurable_setDist_spheres {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {r : ℝ} (hr : 0 < r) {ρ1 ρ2 : ℝ}
    (_h1 : 0 < ρ1) (h2 : 0 < ρ2) :
    Measurable fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (sphere p.2 ρ1) (sphere p.2 ρ2)) := by
  obtain ⟨SA, hSAs, hSAc, hSAd⟩ := HarmonicBalls.PinchMeasurable.exists_countable_subset_closure (sphere (0 : ℂ) (ρ1 / r))
  obtain ⟨SF, hSFs, hSFc, hSFd⟩ := HarmonicBalls.PinchMeasurable.exists_countable_subset_closure (frontier (ball (0 : ℂ) (ρ2 / r)))
  have hm := HarmonicBalls.PinchMeasurable.measurable_setDist_frontier hDm hDc hr.ne' hSAs hSAc hSAd hSFs hSFc hSFd
  have hrρ : ∀ ρ : ℝ, r * (ρ / r) = ρ := fun ρ => by rw [mul_div_assoc', mul_div_cancel_left₀ _ hr.ne']
  have e1 : ∀ z : ℂ, sphere z ρ1 = rescaledSet (sphere (0 : ℂ) (ρ1 / r)) r z := by
    intro z
    show sphere z ρ1 = affHomeo r hr.ne' z '' sphere (0 : ℂ) (ρ1 / r)
    rw [affHomeo_image_sphere hr z (ρ1 / r), hrρ]
  have e2 : ∀ z : ℂ, sphere z ρ2 = frontier (rescaledSet (ball (0 : ℂ) (ρ2 / r)) r z) := by
    intro z
    have hs : ρ2 / r ≠ 0 := (div_pos h2 hr).ne'
    show sphere z ρ2 = frontier (affHomeo r hr.ne' z '' ball (0 : ℂ) (ρ2 / r))
    rw [← (affHomeo r hr.ne' z).image_frontier, frontier_ball _ hs, affHomeo_image_sphere hr z (ρ2 / r), hrρ]
  have key : (fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (sphere p.2 ρ1) (sphere p.2 ρ2))) =
      fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (rescaledSet (sphere (0 : ℂ) (ρ1 / r)) r p.2)
        (frontier (rescaledSet (ball (0 : ℂ) (ρ2 / r)) r p.2))) := by
    funext p
    rw [e1 p.2, e2 p.2]
  rw [key]
  exact hm

/-- Distance from a closure: `closure (rescaledSet Q' r z) = rescaledSet (closure Q') r z`. -/
lemma measurable_setDist_closure_frontier {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2) {r : ℝ} (hr : 0 < r) (Q' Q : Set ℂ) :
    Measurable fun p : Ω × ℂ =>
      ENNReal.ofReal (setDist (D p.1) (closure (rescaledSet Q' r p.2)) (frontier (rescaledSet Q r p.2))) := by
  obtain ⟨SQ, hSQs, hSQc, hSQd⟩ := HarmonicBalls.PinchMeasurable.exists_countable_subset_closure (closure Q')
  obtain ⟨SF, hSFs, hSFc, hSFd⟩ := HarmonicBalls.PinchMeasurable.exists_countable_subset_closure (frontier Q)
  have hm := HarmonicBalls.PinchMeasurable.measurable_setDist_frontier hDm hDc hr.ne' hSQs hSQc hSQd hSFs hSFc hSFd
  have hc : ∀ z : ℂ, closure (rescaledSet Q' r z) = rescaledSet (closure Q') r z := fun z =>
    ((affHomeo r hr.ne' z).image_closure Q').symm
  have key : (fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (closure (rescaledSet Q' r p.2))
      (frontier (rescaledSet Q r p.2)))) =
      fun p : Ω × ℂ => ENNReal.ofReal (setDist (D p.1) (rescaledSet (closure Q') r p.2)
        (frontier (rescaledSet Q r p.2))) := by
    funext p
    rw [hc p.2]
  rw [key]
  exact hm

/-- **Measurability of the corrected local certificate in `(ω, z)` (eq. (27) of CHATGPT-n3-B1-B2, sec. 5.1).**
For a measurable family of Euclidean length metrics `D ω` (continuous in the points) and a Kernel `κ` of measures,
the set of `(ω, z)` at which `CertificateEvent (κ ω) (D ω) Ostar U V W T Q' Q η M r z` holds is measurable.
Hypotheses on `Ostar`: open, containing `0` and the sphere of radius `5` (the domain of the sphere supremum; without
them the supremum is `⊤` and the event is empty). -/
theorem measurableSet_certificateEvent (κ : ProbabilityTheory.Kernel Ω ℂ) [ProbabilityTheory.IsSFiniteKernel κ]
    {D : Ω → ℂ → ℂ → ℝ}
    (hDm : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hDc : ∀ ω, Continuous fun q : ℂ × ℂ => D ω q.1 q.2)
    (hD : ∀ ω, IsEuclideanLengthMetric (D ω)) (hnonneg : ∀ ω x y, 0 ≤ D ω x y)
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {p : Ω × ℂ | CertificateEvent (κ p.1) (D p.1) Ostar U V W T Q' Q η M r p.2} := by
  obtain ⟨SC, hSCs, hSCc, hSCd⟩ := HarmonicBalls.PinchMeasurable.exists_countable_subset_closure (sphere (0 : ℂ) 1)
  have m1 := measurable_sphere_sup_affine hDm hD hnonneg hr hOstar h0 hsph
  have m2 := measurable_setDist_closure_frontier hDm hDc hr Q' Q
  have m3 := measurable_internalDiam_affine hDm hD hnonneg hr hη (certK0 T W η)
  have m4 := HarmonicBalls.PinchMeasurable.measurable_setDist_sphere hDm hDc (mul_pos hr hη) hSCs hSCc hSCd
  have m5 := measurable_internalDiam_affine hDm hD hnonneg hr hη (certK1 V)
  have m6 := measurable_setDist_spheres hDm hDc hr (mul_pos hr hη)
    (by positivity : (0 : ℝ) < 2 * r * η)
  have m7 : Measurable fun p : Ω × ℂ =>
      ENNReal.ofReal M * annulusGreenPotentialSup (κ p.1) p.2 (3 * r) (6 * r) :=
    (measurable_kernel_annulusGreenPotentialSup κ _ _).const_mul _
  have m8 := HarmonicBalls.PinchMeasurable.measurable_kernel_rescaled (κ := κ) hU hr.ne'
  have m9 := measurable_internalDiam_affine hDm hD hnonneg hr hη (certK2 V W η)
  have m10 := measurable_setDist_spheres hDm hDc hr (by positivity : (0 : ℝ) < 2 * r * η)
    (by positivity : (0 : ℝ) < 3 * r * η)
  have s1 := measurableSet_lt m1 m2
  have s2 := measurableSet_lt m3 m4
  have s3 := measurableSet_lt m5 m6
  have s4 := measurableSet_lt m7 m8
  have s5 := measurableSet_lt m9 m10
  simp only [CertificateEvent, internalDiam, Set.ofPred_and]
  exact ((s1.inter s2).inter ((s3.inter s4).inter s5))

end FirstPassS11i

#print axioms FirstPassS11i.measurableSet_certificateEvent
#print axioms FirstPassS11i.measurable_internalDiam_affine
