import HarmonicBalls.Proofs.GFF.InsertedLocalJointShiftLaw
import HarmonicBalls.FirstPass.S11am
import HarmonicBalls.FirstPass.S11ba
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11m.DecodedMass

/-!
# Coordinates for local pinch events

A countable family of admissible internal-metric coordinates supplies the measurable
metric readout for the three local pinch events.
-/

open HarmonicBalls MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- There are countable admissible metric coordinates with a measurable readout for all three local events. -/
theorem exists_pinch_countable_metric_coordinates {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (I : S11am.PinchCountSets V W T Q' Q δ) :
    ∃ (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ),
      (∀ n, IsOpen (domain n) ∧ ((0 : ℂ) ∈ domain n → IsConnected (domain n)) ∧
        (pair n).1 ∈ domain n ∧ (pair n).2 ∈ domain n) ∧
      (∀ O x y, Measurable (coordinateReadout domain pair (O, (x, y)))) ∧
      ∀ (D : ℂ → ℂ → ℝ) (b : ℝ),
        S11am.DecodesOnSets I
          (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) D b
          (fun n => ENNReal.ofReal b * internalMetric D (domain n) (pair n).1 (pair n).2) := by
  let O₀ := pinchOmegaGeom W Q δ
  let O₁ := thickening δ (closure (T \ thickening (3 * δ) W))
  let O₂ := thickening δ (closure V)
  let O₃ := thickening δ (closure (thickening (3 * δ) W \ V))
  let Os : Set (Set ℂ) := {O₀, O₁, O₂, O₃, univ}
  let A : Set ℂ := {0} ∪ I.sp ∪ I.qp ∪ I.fp ∪ I.cp ∪ I.ep ∪ I.s2 ∪ I.s3 ∪ I.cv ∪ I.t2 ∪ I.t3 ∪ I.ct
  have hOs : Os.Countable := by
    dsimp [Os]
    exact (by simp : ({O₀, O₁, O₂, O₃, univ} : Set (Set ℂ)).Finite).countable
  have hA : A.Countable := by
    dsimp [A]
    exact (((((((((((countable_singleton 0).union I.sp_dense.2.2).union I.qp_dense.2.2).union
      I.fp_dense.2.2).union I.cp_dense.2.2).union I.ep_dense.2.2).union I.s2_dense.2.2).union
      I.s3_dense.2.2).union I.cv_dense.2.2).union I.t2_dense.2.2).union I.t3_dense.2.2).union I.ct_dense.2.2
  let S : Set (Set ℂ × (ℂ × ℂ)) := {t | t.1 ∈ Os ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A ∧ t.2.1 ∈ t.1 ∧ t.2.2 ∈ t.1}
  have hS : S.Countable := ((hOs.prod (hA.prod hA)).mono (by
    intro t ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1⟩))
  have hO : ({0} ∪ sphere (0 : ℂ) 5) ⊆ O₀ := by
    simpa only [singleton_union] using FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo
  have ha0 := S11ba.admissible_pinchOmegaGeom hgeo hO
  have ha1 := S11ba.admissible_diam_first hgeo hO
  have ha2 := S11ba.admissible_diam_second hgeo hO
  have ha3 := S11ba.admissible_diam_third hgeo hO
  have valid : ∀ t ∈ S, IsOpen t.1 ∧ ((0 : ℂ) ∈ t.1 → IsConnected t.1) ∧ t.2.1 ∈ t.1 ∧ t.2.2 ∈ t.1 := by
    intro t ht
    have ho : IsOpen t.1 ∧ ((0 : ℂ) ∈ t.1 → IsConnected t.1) := by
      have hm := ht.1
      simp only [Os, mem_insert_iff, mem_singleton_iff] at hm
      rcases hm with h | h | h | h | h
      · rw [h]; exact ⟨ha0.1, ha0.2.2⟩
      · rw [h]; exact ⟨ha1.1, ha1.2.2⟩
      · rw [h]; exact ⟨ha2.1, ha2.2.2⟩
      · rw [h]; exact ⟨ha3.1, ha3.2.2⟩
      · rw [h]; exact ⟨isOpen_univ, fun _ => isConnected_univ⟩
    exact ⟨ho.1, ho.2, ht.2.2.2.1, ht.2.2.2.2⟩
  obtain ⟨domain, pair, hv, hc⟩ := exists_countable_admissible_metric_coordinates S hS valid
  refine ⟨domain, pair, hv, fun O x y => measurable_coordinateReadout domain pair _, ?_⟩
  intro D b
  have recover : ∀ O ∈ Os, ∀ x ∈ A, ∀ y ∈ A, x ∈ O → y ∈ O →
      coordinateReadout domain pair (O, (x, y))
        (fun n => ENNReal.ofReal b * internalMetric D (domain n) (pair n).1 (pair n).2) =
      ENNReal.ofReal b * internalMetric D O x y := by
    intro O hO' x hx y hy hxO hyO
    have h := hc (O, (x, y)) ⟨hO', hx, hy, hxO, hyO⟩
    have h' : ∃ n, (domain n, pair n) = (O, (x, y)) := by
      obtain ⟨n, hn, hp⟩ := h
      exact ⟨n, Prod.ext hn hp⟩
    exact coordinateReadout_apply domain pair (O, (x, y)) h'
      (fun t => ENNReal.ofReal b * internalMetric D t.1 t.2.1 t.2.2)
  have points : ∀ z : ℂ, z = 0 ∨ z ∈ I.sp ∨ z ∈ I.qp ∨ z ∈ I.fp ∨ z ∈ I.cp ∨ z ∈ I.ep ∨
      z ∈ I.s2 ∨ z ∈ I.s3 ∨ z ∈ I.cv ∨ z ∈ I.t2 ∨ z ∈ I.t3 ∨ z ∈ I.ct → z ∈ A := by
    intro z hz
    simp only [A, mem_union, mem_singleton_iff]
    tauto
  have p0 : (0 : ℂ) ∈ A := points 0 (Or.inl rfl)
  have d0 : O₀ ∈ Os := by simp [Os]
  have d1 : O₁ ∈ Os := by simp [Os]
  have d2 : O₂ ∈ Os := by simp [Os]
  have d3 : O₃ ∈ Os := by simp [Os]
  have du : (univ : Set ℂ) ∈ Os := by simp [Os]
  have a0 : (0 : ℂ) ∈ O₀ := hO (by simp)
  have psp : ∀ y ∈ I.sp, y ∈ A := fun y hy => points y (by tauto)
  have pqp : ∀ y ∈ I.qp, y ∈ A := fun y hy => points y (by tauto)
  have pfp : ∀ y ∈ I.fp, y ∈ A := fun y hy => points y (by tauto)
  have pcp : ∀ y ∈ I.cp, y ∈ A := fun y hy => points y (by tauto)
  have pep : ∀ y ∈ I.ep, y ∈ A := fun y hy => points y (by tauto)
  have ps2 : ∀ y ∈ I.s2, y ∈ A := fun y hy => points y (by tauto)
  have ps3 : ∀ y ∈ I.s3, y ∈ A := fun y hy => points y (by tauto)
  have pcv : ∀ y ∈ I.cv, y ∈ A := fun y hy => points y (by tauto)
  have pt2 : ∀ y ∈ I.t2, y ∈ A := fun y hy => points y (by tauto)
  have pt3 : ∀ y ∈ I.t3, y ∈ A := fun y hy => points y (by tauto)
  have pct : ∀ y ∈ I.ct, y ∈ A := fun y hy => points y (by tauto)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact recover O₀ d0 0 p0 y (psp y hy) a0 (hO (Or.inr (I.sp_dense.1 hy)))
  · intro x hx y hy
    exact recover univ du x (pqp x hx) y (pfp y hy) (mem_univ _) (mem_univ _)
  · intro x hx y hy
    exact recover O₁ d1 x (pcp x hx) y (pcp y hy)
      (self_subset_thickening hgeo.delta_pos _ (I.cp_dense.1 hx))
      (self_subset_thickening hgeo.delta_pos _ (I.cp_dense.1 hy))
  · intro y hy
    exact recover univ du 0 p0 y (pep y hy) (mem_univ _) (mem_univ _)
  · intro x hx y hy
    exact recover O₂ d2 x (pcv x hx) y (pcv y hy)
      (self_subset_thickening hgeo.delta_pos _ (I.cv_dense.1 hx))
      (self_subset_thickening hgeo.delta_pos _ (I.cv_dense.1 hy))
  · intro x hx y hy
    exact recover univ du x (ps2 x hx) y (ps3 y hy) (mem_univ _) (mem_univ _)
  · intro x hx y hy
    exact recover O₃ d3 x (pct x hx) y (pct y hy)
      (self_subset_thickening hgeo.delta_pos _ (I.ct_dense.1 hx))
      (self_subset_thickening hgeo.delta_pos _ (I.ct_dense.1 hy))
  · intro x hx y hy
    exact recover univ du x (pt2 x hx) y (pt3 y hy) (mem_univ _) (mem_univ _)

/-- The actual local field, normalized measure, and the metric coordinates of all three local events have equivalent
joint laws after each smooth compact perturbation. -/
theorem HarmonicBalls.IsWholePlaneGFF.exists_joint_smooth_shift_law_for_pinch_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1) (hξ : 0 ≤ ξ) :
    ∃ (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ) (R : ℝ),
      R ∈ Ioo (6 : ℝ) 7 ∧
      (∀ n, IsOpen (domain n) ∧ ((0 : ℂ) ∈ domain n → IsConnected (domain n)) ∧
        (pair n).1 ∈ domain n ∧ (pair n).2 ∈ domain n) ∧
      (∀ O x y, Measurable (coordinateReadout domain pair (O, (x, y)))) ∧
      (∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
        (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
        (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2)) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (domain n) (pair n).1 (pair n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 7) ω,
           normalizedRestriction (μ ω) (ball 0 R), fun n =>
             ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
               internalMetric (D ω) (domain n) (pair n).1 (pair n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 7) ω,
           normalizedRestriction (μ ω) (ball 0 R), fun n =>
             ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
               internalMetric (D ω) (domain n) (pair n).1 (pair n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (domain n) (pair n).1 (pair n).2)) := by
  obtain ⟨domain, pair, hv, hm, hd⟩ := exists_pinch_countable_metric_coordinates hgeo I
  obtain ⟨R, hR, hlaw⟩ := h.exists_joint_smooth_shift_law_on_domains_between_of_field hμ hγ hγ2 hα
    (a := 6) (ε := 7) (by norm_num) (by norm_num) hDfield haxioms domain
    (fun n => (hv n).1) (fun n => (hv n).2.1) ψ hψ hψint pair (fun n => (hv n).2.2) hξ
  exact ⟨domain, pair, R, hR, hv, hm, hd, hlaw⟩

/-- The local pinch rule evaluated on a normalized measure and metric coordinates. -/
noncomputable def pinchCoordinateEvent {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (I : S11am.PinchCountSets V W T Q' Q δ) (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ)
    (M : ℝ) : Set (Measure ℂ × (ℕ → ℝ≥0∞)) :=
  S11am.decodedPinchRule I
    (fun O x y a => coordinateReadout domain pair (O, (x, y)) a.2)
    (fun a => annulusGreenPotentialSup a.1 0 3 6) (fun a => a.1 U) M

/-- The local pinch rule is measurable in its measure and metric coordinates. -/
theorem measurableSet_pinchCoordinateEvent {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hU : MeasurableSet U) (I : S11am.PinchCountSets V W T Q' Q δ)
    (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ) (M : ℝ) :
    MeasurableSet (pinchCoordinateEvent (U := U) I domain pair M) := by
  apply S11am.measurableSet_decodedPinchRule I
  · intro O hO x y
    exact (measurable_coordinateReadout domain pair (O, (x, y))).comp measurable_snd
  · exact (HarmonicBalls.measurable_annulusGreenPotentialSup 0 3 6).comp measurable_fst
  · exact (Measure.measurable_measure.mp measurable_fst) U hU

/-- The coordinate rule identifies the local event when the reference mass is positive and finite. -/
theorem pinchCoordinateEvent_iff {U V W T Q' Q : Set ℂ} {δ R : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hR : 6 < R)
    (I : S11am.PinchCountSets V W T Q' Q δ)
    (domain : ℕ → Set ℂ) (pair : ℕ → ℂ × ℂ)
    (hd : ∀ (d : ℂ → ℂ → ℝ) (b : ℝ), S11am.DecodesOnSets I
      (fun O x y a => coordinateReadout domain pair (O, (x, y)) a) d b
      (fun n => ENNReal.ofReal b * internalMetric d (domain n) (pair n).1 (pair n).2))
    (μ : Measure ℂ) (hμ0 : μ (ball 0 R) ≠ 0) (hμtop : μ (ball 0 R) ≠ ⊤)
    (D : ℂ → ℂ → ℝ) (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    (b : ℝ) (hb : 0 < b) (M : ℝ) :
    (normalizedRestriction μ (ball 0 R),
      fun n => ENNReal.ofReal b * internalMetric D (domain n) (pair n).1 (pair n).2) ∈
      pinchCoordinateEvent (U := U) I domain pair M ↔
    S11m.LocalRule.pinchLocalRule μ D W T Q' Q U V δ M ∧
      annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
  have hU : U ⊆ ball (0 : ℂ) R := by
    intro z hz
    exact ball_subset_ball (by linarith) ((hgeo.U_subset hz).1)
  have hA : annulus (0 : ℂ) 3 6 ⊆ ball 0 R := fun z hz => ball_subset_ball hR.le hz.1
  have hpos : 0 < (μ (ball 0 R)).toReal := ENNReal.toReal_pos hμ0 hμtop
  have hscale : ENNReal.ofReal ((μ (ball 0 R)).toReal⁻¹) = (μ (ball 0 R))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_toReal hμtop]
  have hm := S11m.decodedMasses_of_restrict measurableSet_ball hU hA
    (μ := μ) (c := (μ (ball 0 R))⁻¹) (ν := normalizedRestriction μ (ball 0 R)) rfl
  have hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := by
    intro z hz
    exact FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo (Or.inr hz)
  apply S11am.decodedPinchRule_iff hD hnn hb (inv_pos.mpr hpos) hgeo hΩ I
  · exact hd D b
  · simpa [hscale] using hm.2
  · simpa [hscale] using hm.1

