import HarmonicBalls.Draft.Section11

/-!
# Metric inequalities in the pinch-point argument

The two strict metric inequalities of the pinch event, written pointwise.
These are independent of the construction of the LQG metric and valid for any
nonnegative symmetric distance function.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- A metric inducing the Euclidean topology is Euclidean-continuous in each
argument. -/
theorem IsEuclideanLengthMetric.continuous_left {D : ℂ → ℂ → ℝ}
    (h : IsEuclideanLengthMetric D) (y : ℂ) : Continuous fun x => D x y := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hopen : IsOpen {a : ℂ | D x a < ε} := by
    apply (h.isOpen_iff _).2
    intro a ha
    refine ⟨ε - D x a, sub_pos.mpr ha, ?_⟩
    intro b hb
    change D x b < ε
    have ht := h.triangle x a b
    linarith
  have hx : x ∈ {a : ℂ | D x a < ε} := by
    change D x x < ε
    rw [h.self_eq_zero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  have hnear : D x a < ε := hball ha
  have h₁ := h.triangle a x y
  have h₂ := h.triangle x a y
  rw [h.symm a x] at h₁
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A point on the Euclidean frontier of an open `D`-ball has the ball's
radius as its `D`-distance from the centre. -/
theorem IsEuclideanLengthMetric.distance_eq_of_mem_frontier_ball
    {D : ℂ → ℂ → ℝ} (h : IsEuclideanLengthMetric D) (w z : ℂ) (u : ℝ)
    (hz : z ∈ frontier (lqgMetricBall D w u)) : D w z = u := by
  have hcont : Continuous fun x => D w x := by
    simpa only [h.symm w] using h.continuous_left w
  have hopen : IsOpen (lqgMetricBall D w u) := isOpen_lt hcont continuous_const
  have hle : D w z ≤ u := by
    apply closure_minimal (s := lqgMetricBall D w u) _ (isClosed_le hcont continuous_const)
      (frontier_subset_closure hz)
    intro x hx
    change D w x ≤ u
    change D w x < u at hx
    exact le_of_lt hx
  have hnot : z ∉ lqgMetricBall D w u := by
    rw [hopen.frontier_eq] at hz
    exact hz.2
  change ¬ D w z < u at hnot
  exact le_antisymm hle (le_of_not_gt hnot)

/-- The set distance is bounded by the distance between any two selected points. -/
theorem setDist_le_of_nonneg (D : ℂ → ℂ → ℝ) (hD : ∀ x y, 0 ≤ D x y)
    {A B : Set ℂ} {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) :
    setDist D A B ≤ D x y := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hD a b
  · exact Set.mem_image2_of_mem hx hy

/-- The first pinch inequality compares each radial distance to each distance
from `Q'` to the boundary of `Q`. -/
theorem pinchPointEvent_radial_lt_boundary
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r : ℝ) (z q a b : ℂ) (hD : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z)
    (hq : q ∈ sphere z (5 * r)) (ha : a ∈ rescaledSet Q' r z)
    (hb : b ∈ frontier (rescaledSet Q r z)) : D z q < D a b := by
  have hs : ENNReal.ofReal (D z q) ≤ ⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x) :=
    le_iSup_of_le q (le_iSup_of_le hq le_rfl)
  have hd := setDist_le_of_nonneg D hD ha hb
  have hh : ENNReal.ofReal (D z q) < ENNReal.ofReal (D a b) :=
    lt_of_lt_of_le (lt_of_le_of_lt hs hp.1) (ENNReal.ofReal_le_ofReal hd)
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hD z q)).mp hh

/-- The second pinch inequality bounds every distance within `T` by every
radial distance to the sphere. -/
theorem pinchPointEvent_diam_lt_radial
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r : ℝ) (z q x y : ℂ) (hD : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z)
    (hq : q ∈ sphere z (5 * r)) (hx : x ∈ rescaledSet T r z)
    (hy : y ∈ rescaledSet T r z) : D x y < D z q := by
  have hs : ENNReal.ofReal (D x y) ≤
      ⨆ a ∈ rescaledSet T r z, ⨆ b ∈ rescaledSet T r z, ENNReal.ofReal (D a b) :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
  have hd := setDist_le_of_nonneg D hD (Set.mem_singleton z) hq
  have hh : ENNReal.ofReal (D x y) < ENNReal.ofReal (D z q) :=
    lt_of_lt_of_le (lt_of_le_of_lt hs hp.2.1) (ENNReal.ofReal_le_ofReal hd)
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hD x y)).mp hh

/-- The diameter comparison extends to a point in the closure of `T`. This
is the closure step used when a geodesic meets the outer sphere in Lemma 11.14. -/
theorem pinchPointEvent_closure_diam_lt_radial
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r : ℝ) (z q x y : ℂ) (hD : ∀ x y, 0 ≤ D x y)
    (hcont : Continuous fun a => D a y)
    (hp : pinchPointEvent μ D U T Q' Q M r z)
    (hq : q ∈ sphere z (5 * r)) (hx : x ∈ closure (rescaledSet T r z))
    (hy : y ∈ rescaledSet T r z) : D x y < D z q := by
  let S : ℝ≥0∞ := ⨆ a ∈ rescaledSet T r z,
    ⨆ b ∈ rescaledSet T r z, ENNReal.ofReal (D a b)
  have hd := setDist_le_of_nonneg D hD (Set.mem_singleton z) hq
  have hS : S < ENNReal.ofReal (D z q) :=
    lt_of_lt_of_le hp.2.1 (ENNReal.ofReal_le_ofReal hd)
  have hStop : S ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hS le_top)
  have hclosure : D x y ≤ S.toReal := by
    apply closure_minimal (s := rescaledSet T r z) _ (isClosed_le hcont continuous_const) hx
    intro a ha
    have haS : ENNReal.ofReal (D a y) ≤ S :=
      le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    have := ENNReal.toReal_mono hStop haS
    change D a y ≤ S.toReal
    simpa only [ENNReal.toReal_ofReal (hD a y)] using this
  have hlt : S.toReal < D z q := by
    have := (ENNReal.toReal_lt_toReal hStop ENNReal.ofReal_ne_top).2 hS
    simpa only [ENNReal.toReal_ofReal (hD z q)] using this
  exact lt_of_le_of_lt hclosure hlt

/-- The outer sphere of a scaled pinch configuration lies in the closure of
its scaled keyhole region. -/
theorem sphere_subset_closure_rescaledSet {U T Q' Q : Set ℂ}
    (hconfig : IsPinchPointConfiguration U T Q' Q) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    sphere z (5 * r) ⊆ closure (rescaledSet T r z) := by
  intro q hq
  let a : ℂ := (r : ℂ)⁻¹ * (q - z)
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hqa : (r : ℂ) * a + z = q := by
    dsimp [a]
    field_simp
    ring
  have ha : a ∈ sphere (0 : ℂ) 5 := by
    rw [Metric.mem_sphere, dist_zero_right]
    dsimp [a]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hq' : ‖q - z‖ = 5 * r := by simpa [Metric.mem_sphere, dist_eq_norm] using hq
    rw [hq']
    field_simp
  have hac : a ∈ closure T := frontier_subset_closure (hconfig.sphere_subset_frontier ha)
  have hc : Continuous (fun x : ℂ => (r : ℂ) * x + z) := by fun_prop
  have himage := image_closure_subset_closure_image hc ⟨a, hac, hqa⟩
  exact himage

/-- A path from outside a Euclidean ball to its centre meets its boundary. -/
theorem path_meets_sphere_of_dist_le {w z : ℂ} (p : Path w z) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw : ρ ≤ dist w z) :
    ∃ t ∈ Icc (0 : ℝ) 1, p.extend t ∈ sphere z ρ := by
  have hc : Continuous fun t : ℝ => dist (p.extend t) z :=
    p.continuous_extend.dist continuous_const
  have hm := intermediate_value_Icc' (zero_le_one' ℝ) hc.continuousOn
  have hmem : ρ ∈ Icc (dist (p.extend 1) z) (dist (p.extend 0) z) := by
    simpa only [p.extend_one, p.extend_zero, dist_self] using ⟨hρ, hw⟩
  obtain ⟨t, ht, heq⟩ := hm hmem
  exact ⟨t, ht, heq⟩

/-- The first part of the pinch argument once a geodesic to the chosen point
has crossed the sphere and then the boundary of `Q`. The centre is arbitrary. -/
theorem pinchPointEvent_outside_ball_of_geodesic_points
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z q b a : ℂ) (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z)
    (hq : q ∈ sphere z (5 * r)) (ha : a ∈ rescaledSet Q' r z)
    (hb : b ∈ frontier (rescaledSet Q r z)) (hu : D w z = u)
    (hpath : D w a = D w q + D q b + D b a) :
    a ∉ lqgMetricBall D w u := by
  have hsep := pinchPointEvent_radial_lt_boundary μ D U T Q' Q M r z q a b hnonneg hp hq ha hb
  have htri := hD.triangle w q z
  have hpos := hnonneg q b
  rw [hD.symm q z] at htri
  rw [hD.symm a b] at hsep
  change ¬ D w a < u
  linarith

/-- The second part of the pinch argument once a geodesic to `z` has crossed
both the outer sphere and the closure of `T`. The centre is arbitrary. -/
theorem pinchPointEvent_subset_ball_of_geodesic_point
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z q : ℂ) (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z)
    (hq : q ∈ sphere z (5 * r)) (hqT : q ∈ closure (rescaledSet T r z))
    (hu : D w z = u) (hpath : D w z = D w q + D q z) :
    rescaledSet T r z ⊆ lqgMetricBall D w u := by
  intro y hy
  have hsep := pinchPointEvent_closure_diam_lt_radial μ D U T Q' Q M r z q q y
    hnonneg (hD.continuous_left y) hp hq hqT hy
  have htri := hD.triangle w q y
  rw [hD.symm z q] at hsep
  change D w y < u
  linarith

/-- The inner part of Lemma 11.14 from a geodesic to the boundary point and
the scaled configuration's sphere inclusion. -/
theorem pinchPointEvent_subset_ball_of_geodesic
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z : ℂ) (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z) (hr : 0 ≤ r)
    (hw : 5 * r ≤ dist w z)
    (hsphere : sphere z (5 * r) ⊆ closure (rescaledSet T r z))
    (hz : z ∈ frontier (lqgMetricBall D w u)) (p : Path w z)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1,
      D w z = D w (p.extend t) + D (p.extend t) z) :
    rescaledSet T r z ⊆ lqgMetricBall D w u := by
  obtain ⟨t, ht, hq⟩ := path_meets_sphere_of_dist_le p (by positivity) hw
  exact pinchPointEvent_subset_ball_of_geodesic_point μ D U T Q' Q M r u w z
    (p.extend t) hD hnonneg hp hq (hsphere hq)
    (hD.distance_eq_of_mem_frontier_ball w z u hz) (hgeo t ht)

/-- The `T` inclusion in Lemma 11.14, assuming a geodesic to the marked
boundary point. The conclusion and hypotheses allow an arbitrary ball centre. -/
theorem pinchPointEvent_subset_ball_of_configuration_and_geodesic
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z) (hr : 0 < r)
    (hw : w ∉ ball z (10 * r))
    (hz : z ∈ frontier (lqgMetricBall D w u)) (p : Path w z)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1,
      D w z = D w (p.extend t) + D (p.extend t) z) :
    rescaledSet T r z ⊆ lqgMetricBall D w u := by
  have hdist : 10 * r ≤ dist w z := le_of_not_gt hw
  apply pinchPointEvent_subset_ball_of_geodesic μ D U T Q' Q M r u w z hD hnonneg hp hr.le
    (by linarith) (sphere_subset_closure_rescaledSet hconfig hr z) hz p hgeo

end HarmonicBalls
