import HarmonicBalls.FirstPass.S11k.ExteriorPairings
import HarmonicBalls.Draft.Section11
import HarmonicBalls.FirstPass.S11u

/-!
# Section 11: exterior versions of exit distances

Exit distances `setDist D A (frontier U)` and the sphere-to-sphere distance `setDist D (∂B_δ) (∂B_{2δ})` of the
metric, for an open `U` and an open `V ⊆ E` with `closure U ⊆ V`, have almost-sure versions measurable for the
zero-mean exterior sigma-algebra of `E` (`ExteriorPairings.exists_exterior_ofReal_setDist_version`). These are the
exit-distance inputs of `PinchSecondExteriorVersionsStep`: `a₀ = D(Q', ∂Q)`,
`d₀ = D(0, ∂B_δ)` (eq. (26)) and `d = D(∂B_δ, ∂B_{2δ})` (eq. (27), with the open annulus replaced by `B_{3δ}`).

Locality hypothesis `hloc` is item II of `LQGMetricFieldAxioms` (Proposed/LQG.lean:206) for the open sets `V ⊆ E`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace ExteriorDistances

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- A length-metric distance is nonnegative: `0 = D(z,z) ≤ D(z,w) + D(w,z) = 2 D(z,w)` by the triangle inequality. -/
theorem isEuclideanLengthMetric_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) :
    0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- The metric distance between two sets is nonnegative (an infimum of nonnegative numbers). -/
theorem setDist_nonneg_of_metric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (A B : Set ℂ) :
    0 ≤ setDist D A B := by
  unfold setDist
  apply Real.sInf_nonneg
  rintro _ ⟨x, _, y, _, rfl⟩
  exact isEuclideanLengthMetric_nonneg hD x y

/-- Exterior version of the exit distance `D(A, ∂U)`, as an extended real. -/
theorem exists_exterior_setDist_exit
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hloc : ∀ V : Set ℂ, IsOpen V → V ⊆ E → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {U V A : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hVE : V ⊆ E) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty) :
    ∃ a : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] a ∧
      ∀ᵐ ω ∂P, a ω = ENNReal.ofReal (setDist (D ω) A (frontier U)) :=
  ExteriorPairings.exists_exterior_ofReal_setDist_version hGFF α₀ hE hsph hmetric hU hV hVE hAU hUV hA hfront
    (hloc V hV hVE)

/-- Exterior version of the origin-to-circle distance `d₀ = D(0, ∂B_δ)`, for `B_{2δ} ⊆ E`. -/
theorem exists_exterior_setDist_origin
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hloc : ∀ V : Set ℂ, IsOpen V → V ⊆ E → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {δ : ℝ} (hδ : 0 < δ) (hBE : ball (0 : ℂ) (2 * δ) ⊆ E) :
    ∃ a : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] a ∧
      ∀ᵐ ω ∂P, a ω = ENNReal.ofReal (setDist (D ω) {0} (sphere (0 : ℂ) δ)) := by
  have hfront : frontier (ball (0 : ℂ) δ) = sphere (0 : ℂ) δ := frontier_ball 0 hδ.ne'
  obtain ⟨a, ham, haa⟩ := exists_exterior_setDist_exit hGFF α₀ hE hsph hmetric hloc
    (U := ball (0 : ℂ) δ) (V := ball (0 : ℂ) (2 * δ)) (A := {0}) isOpen_ball isOpen_ball hBE
    (singleton_subset_iff.2 (mem_ball_self hδ)) ((closure_ball_subset_closedBall).trans
      (closedBall_subset_ball (by linarith))) (singleton_nonempty 0)
    (by rw [hfront]; exact NormedSpace.sphere_nonempty.2 hδ.le)
  exact ⟨a, ham, by filter_upwards [haa] with ω h; rw [h, hfront]⟩

/-- Exterior version of the sphere-to-sphere distance `d = D(∂B_δ, ∂B_{2δ})` as a real number (with the open domain `B_{3δ}`), for `B_{3δ} ⊆ E`. -/
theorem exists_exterior_setDist_spheres
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hloc : ∀ V : Set ℂ, IsOpen V → V ⊆ E → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {δ : ℝ} (hδ : 0 < δ) (hBE : ball (0 : ℂ) (3 * δ) ⊆ E) :
    ∃ d : Ω → ℝ, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] d ∧
      ∀ᵐ ω ∂P, d ω = setDist (D ω) (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ)) := by
  have hfront : frontier (ball (0 : ℂ) (2 * δ)) = sphere (0 : ℂ) (2 * δ) :=
    frontier_ball 0 (by linarith : (0 : ℝ) < 2 * δ).ne'
  obtain ⟨a, ham, haa⟩ := exists_exterior_setDist_exit hGFF α₀ hE hsph hmetric hloc
    (U := ball (0 : ℂ) (2 * δ)) (V := ball (0 : ℂ) (3 * δ)) (A := sphere (0 : ℂ) δ)
    isOpen_ball isOpen_ball hBE
    (fun z hz => by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [mem_ball_zero_iff]
      linarith)
    ((closure_ball_subset_closedBall).trans (closedBall_subset_ball (by linarith)))
    (NormedSpace.sphere_nonempty.2 hδ.le)
    (by rw [hfront]; exact NormedSpace.sphere_nonempty.2 (by linarith))
  refine ⟨fun ω => (a ω).toReal, ham.ennreal_toReal, ?_⟩
  filter_upwards [haa, hmetric] with ω h1 h2
  rw [h1, hfront, ENNReal.toReal_ofReal (setDist_nonneg_of_metric h2 _ _)]

/-- The `δ`-thickening of a set `A` avoids `closure W` when `A` avoids `thickening (3δ) W`: a point `z` within `δ` of
`x ∈ A` and within `2δ` of `W` would put `x` within `3δ` of `W`. -/
theorem thickening_subset_compl_closure {δ : ℝ} (hδ : 0 < δ) {A W : Set ℂ}
    (hA : ∀ x ∈ A, x ∉ thickening (3 * δ) W) : thickening δ A ⊆ (closure W)ᶜ := by
  intro z hz hzW
  obtain ⟨x, hxA, hzx⟩ := mem_thickening_iff.1 hz
  obtain ⟨w, hwW, hzw⟩ := Metric.mem_closure_iff.1 hzW (2 * δ) (by linarith)
  refine hA x hxA (mem_thickening_iff.2 ⟨w, hwW, ?_⟩)
  have h1 := dist_triangle x z w
  rw [dist_comm x z] at h1
  linarith

/-- Exterior version of the internal diameter `internalDiam D δ A = sup_{x,y ∈ A} D(x,y; B_δ(A))` (Draft
`internalDiam`, paper line 3252), for `B_δ(A) ⊆ E`. The supremum is measurable for `fieldSigmaAlgebra (B_δ(A))`
(`exists_local_iSup_internalMetric_representative`), hence has a zero-mean exterior version. -/
theorem exists_exterior_internalDiam_version
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hloc : ∀ V : Set ℂ, IsOpen V → V ⊆ E → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {δ : ℝ} (hδ : 0 < δ) {A : Set ℂ} (hVE : thickening δ A ⊆ E) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] Y ∧
      ∀ᵐ ω ∂P, internalDiam (D ω) δ A = Y ω := by
  have hV : IsOpen (thickening δ A) := Metric.isOpen_thickening
  have hAV : A ⊆ thickening δ A := self_subset_thickening hδ A
  obtain ⟨G, hGm, hGa⟩ := hloc (thickening δ A) hV hVE
  obtain ⟨Y, hY, hYa⟩ := exists_local_iSup_internalMetric_representative (m := fieldSigmaAlgebra α₀ hC (thickening δ A))
    hV hAV hAV hmetric (fun x _ y _ => hGm x y)
    (hGa.mono fun ω h x hx y hy => h x (hAV hx) y (hAV hy))
  obtain ⟨Y', hY'm, hY'a⟩ := ExteriorPairings.exists_exterior_version_of_fieldSigmaAlgebra hGFF α₀ hE hsph hVE Y hY
  exact ⟨Y', hY'm, by filter_upwards [hYa, hY'a] with ω h1 h2; rw [internalDiam, h1, h2]⟩

end ExteriorDistances

end HarmonicBalls
