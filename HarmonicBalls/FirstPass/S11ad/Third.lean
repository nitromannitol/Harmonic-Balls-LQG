import HarmonicBalls.FirstPass.S11h.OuterDiamFinite
import HarmonicBalls.FirstPass.S11h.SetDistPos
import HarmonicBalls.FirstPass.S11ad

/-!
# Deterministic and a.s. bounds for the third local event (note §6.4, step 5 of the certificate)

For the third event `E₃ = {a₂ > d₂}` of `pinchThirdEventLocal`, with `a₂ = D(∂B_{2δ}, ∂B_{3δ})` and
`d₂ = diam^δ_D(closure (B_{3δ}(W) \ V))`:

* `setDist_sphere_pos`: `a₂ > 0` for every Euclidean length metric;
* `internalDiam_third_closure_lt_top`: `d₂ < ∞` for every Euclidean length metric (the
  closure version of `IsBufferedPinchGeometry.internalDiam_third_lt_top`, same case split);
* `exists_const_pos_of_pos_ae`: the a.e. form of `S11ad.exists_const_pos_of_pos`;
* `pinch_third_const_ae`: on a set of positive probability there are `c, d > 0` with `c ≤ a₂` and `d₂ ≤ d`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

universe u

/-- Closure version of `internalDiam_thickening_ball_sdiff_ball_lt_top`. -/
theorem internalDiam_thickening_ball_sdiff_ball_closure_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (c : ℂ) (a b : ℝ) :
    internalDiam D δ (closure (thickening (3 * δ) (ball c b) \ ball c a)) < ⊤ := by
  have hnonneg : ∀ x y, 0 ≤ D x y := hD.nonneg_apply
  by_cases hb : b ≤ 0
  · rw [ball_eq_empty.mpr hb, thickening_empty, empty_sdiff]
    simp [internalDiam]
  · have hb0 : 0 < b := not_le.mp hb
    rw [thickening_ball (by linarith : (0 : ℝ) < 3 * δ) hb0]
    by_cases ha : a ≤ 0
    · rw [ball_eq_empty.mpr ha, sdiff_empty]
      exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hδ isBounded_ball.closure
        (IsConnected.thickening_complex
          ((convex_ball c (3 * δ + b)).isConnected ⟨c, mem_ball_self (by linarith)⟩).closure hδ)
    · have ha0 : 0 < a := not_le.mp ha
      by_cases hab : 3 * δ + b ≤ a
      · rw [sdiff_eq_empty.mpr (ball_subset_ball hab)]
        simp [internalDiam]
      · have hab0 : a < 3 * δ + b := not_le.mp hab
        have hconn : IsConnected (ball c (3 * δ + b) \ ball c a) :=
          isConnected_ball_sdiff_ball_complex c ha0 hab0
        exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hδ
          (isBounded_ball.subset sdiff_subset).closure (IsConnected.thickening_complex hconn.closure hδ)

/-- `d₂ < ∞` for the closed third-event set `closure (B_{3δ}(W) \ V)` of a buffered pinch geometry. -/
theorem internalDiam_third_closure_lt_top {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    internalDiam D δ (closure (thickening (3 * δ) W \ V)) < ⊤ := by
  obtain ⟨c, ρU, ρV, ρW, -, hV, hW⟩ := hgeo.concentric
  rw [hV, hW]
  exact internalDiam_thickening_ball_sdiff_ball_closure_lt_top hD hgeo.delta_pos c ρV ρW

/-- `a₂ > 0` for the sphere distance `D(∂B_{2δ}, ∂B_{3δ})` of every Euclidean length metric. -/
theorem setDist_sphere_pos {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ) :
    0 < setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)) := by
  refine setDist_pos_of_isEuclideanLengthMetric hD (isCompact_sphere _ _) (isCompact_sphere _ _)
    (NormedSpace.sphere_nonempty.2 (by positivity)) (NormedSpace.sphere_nonempty.2 (by positivity))
    (Set.disjoint_left.2 fun z h1 h2 => ?_)
  rw [mem_sphere_zero_iff_norm] at h1 h2
  linarith

/-- The a.e. form of `exists_const_pos_of_pos`: the pointwise hypothesis is only needed off a null set. -/
theorem exists_const_pos_of_pos_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    (hAp : 0 < P A) {good : Ω → Prop} (hgood : ∀ᵐ ω ∂P, good ω) {a₂ : Ω → ℝ} {d₂ : Ω → ℝ≥0∞}
    (hpos : ∀ ω ∈ A, good ω → 0 < a₂ ω ∧ d₂ ω ≠ ∞) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ 0 < P (A ∩ {ω | c ≤ a₂ ω ∧ d₂ ω ≤ ENNReal.ofReal d}) := by
  set S := toMeasurable P {ω | ¬ good ω} with hSdef
  have hS : P S = 0 := by
    rw [hSdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hAS : 0 < P (A \ S) := by rw [measure_sdiff_null hS]; exact hAp
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_const_pos_of_pos hAS (a₂ := a₂) (d₂ := d₂) (fun ω hω => by
    have hgω : good ω := by
      by_contra hng
      exact hω.2 (subset_toMeasurable P _ hng)
    exact hpos ω hω.1 hgω)
  exact ⟨c, d, hc, hd, lt_of_lt_of_le hcd (measure_mono fun ω hω => ⟨hω.1.1, hω.2⟩)⟩

/-- On a set `A` of positive probability there are constants `c, d > 0` with `c ≤ a₂` and `d₂ ≤ d` on a subset of
positive probability, for the third event of a buffered pinch geometry (note §6.4). -/
theorem pinch_third_const_ae {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) {A : Set Ω} (hAp : 0 < P A) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ 0 < P (A ∩ {ω | c ≤ setDist (D ω) (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)) ∧
      internalDiam (D ω) δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal d}) :=
  exists_const_pos_of_pos_ae hAp (good := fun ω => IsEuclideanLengthMetric (D ω)) hD
    (a₂ := fun ω => setDist (D ω) (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)))
    (d₂ := fun ω => internalDiam (D ω) δ (closure (thickening (3 * δ) W \ V)))
    (fun _ _ hgood => ⟨setDist_sphere_pos hgood hgeo.delta_pos,
      (internalDiam_third_closure_lt_top hgeo hgood).ne⟩)

end S11ad
end HarmonicBalls
