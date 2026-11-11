import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.LocalExtremaRepresentatives

/-!
# Outside form of the exit and crossing distances of Lemma 11.16

The three set distances of the exterior first event (`PinchSecondExteriorEventStep`, `FirstPass/S11k.lean`) are
(i) the exit distance `D(Q', ∂Q)`, (ii) the exit distance `D(0, ∂B_δ)` from the origin, and (iii) the crossing distance
`D(∂B_δ, ∂B_{2δ})`. Each is an infimum of internal metric values on any open `V` containing the closure of its exit domain
. With
`V = (closure W)ᶜ` they are functions of the field outside `closure W`.

The identities are the general exit-distance lemma `ofReal_setDist_boundary_eq_internalMetric`
(`Steps/Sec11/LocalPathLength.lean`), specialised to the three configurations. The countable collar form is not needed for the identities; its measurable content is supplied by
`exists_local_iInf_internalMetric_representative` (`Steps/Sec11/LocalExtremaRepresentatives.lean`), wrapped in
`exists_outside_ofReal_setDist_of_internalMetric`, which reduces the outside-measurability of the three distances to a
measurable family of internal metrics that agrees with `internalMetric (D ω) V` almost surely. No EXTERNAL input.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Exit distance from `Q'` to the boundary of an open `Q` is the internal metric infimum on any open `V ⊇ closure Q`
(with `K = closure Q'`, `O = Q`; the endpoint lies on `∂Q`). -/
theorem ofReal_setDist_exit_frontier_eq_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {Q' Q V : Set ℂ} (hQ : IsOpen Q) (hQ'Q : Q' ⊆ Q) (hQV : closure Q ⊆ V)
    (hQ' : Q'.Nonempty) (hfront : (frontier Q).Nonempty) :
    ENNReal.ofReal (setDist D Q' (frontier Q)) = ⨅ x ∈ Q', ⨅ y ∈ frontier Q, internalMetric D V x y :=
  ofReal_setDist_boundary_eq_internalMetric hD hQ hQ'Q hQV hQ' hfront

/-- Exit distance from the origin to the circle `∂B_δ` is the internal metric infimum on any open `V ⊇ closure B_δ`
(with `K = {0}`, `O = B_δ(0)`). -/
theorem ofReal_setDist_origin_sphere_eq_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) {V : Set ℂ} (hV : closure (ball (0 : ℂ) δ) ⊆ V) :
    ENNReal.ofReal (setDist D {0} (sphere (0 : ℂ) δ)) = ⨅ y ∈ sphere (0 : ℂ) δ, internalMetric D V 0 y := by
  have hfront : frontier (ball (0 : ℂ) δ) = sphere (0 : ℂ) δ := frontier_ball 0 hδ.ne'
  have hsub : ({0} : Set ℂ) ⊆ ball (0 : ℂ) δ := by
    intro x hx
    rw [mem_singleton_iff.mp hx]
    exact mem_ball_self hδ
  have hne : (sphere (0 : ℂ) δ).Nonempty := ⟨(δ : ℂ), by simp [abs_of_pos hδ]⟩
  have h := ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hsub hV (singleton_nonempty 0)
    (by rw [hfront]; exact hne)
  rw [hfront, iInf_singleton] at h
  exact h

/-- Crossing distance between the circles `∂B_δ` and `∂B_{2δ}` is the internal metric infimum on any open
`V ⊇ closure B_{2δ}` (the annulus is `U = B_{2δ}` with `∂U = ∂B_{2δ}`). -/
theorem ofReal_setDist_sphere_sphere_eq_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) {V : Set ℂ} (hV : closure (ball (0 : ℂ) (2 * δ)) ⊆ V) :
    ENNReal.ofReal (setDist D (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) =
      ⨅ x ∈ sphere (0 : ℂ) δ, ⨅ y ∈ sphere (0 : ℂ) (2 * δ), internalMetric D V x y := by
  have h2 : 0 < 2 * δ := by positivity
  have hfront : frontier (ball (0 : ℂ) (2 * δ)) = sphere (0 : ℂ) (2 * δ) := frontier_ball 0 h2.ne'
  have hsub : sphere (0 : ℂ) δ ⊆ ball (0 : ℂ) (2 * δ) := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx
    rw [mem_ball_zero_iff]
    linarith
  have hne : (sphere (0 : ℂ) δ).Nonempty := ⟨(δ : ℂ), by simp [abs_of_pos hδ]⟩
  have h := ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hsub hV hne
    (by rw [hfront]; exact NormedSpace.sphere_nonempty.mpr h2.le)
  rw [hfront] at h
  exact h

/-- Reduction of the outside measurability of an exit distance to a measurable family of internal metrics. If `G` is
`m`-measurable for each pair of points of `A × ∂U` and agrees almost surely with `internalMetric (D ω) V` on `A × ∂U`
(uniformly in the pair), then `ENNReal.ofReal (setDist (D ω) A (frontier U))` has an `m`-measurable version. This is the
measurability input of the outside-field distances `D(Q', ∂Q)`, `D(0, ∂B_δ)`, `D(∂B_δ, ∂B_{2δ})` with `V = (closure W)ᶜ`;
the family `G` is the open input (weighted singular metric). -/
theorem exists_outside_ofReal_setDist_of_internalMetric {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω} {D : Ω → ℂ → ℂ → ℝ} {G : Ω → ℂ → ℂ → ℝ≥0∞} {V A U : Set ℂ}
    (hV : IsOpen V) (hU : IsOpen U) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x ∈ A, ∀ y ∈ frontier U, Measurable[m] fun ω => G ω x y)
    (hEq : ∀ᵐ ω ∂P, ∀ x ∈ A, ∀ y ∈ frontier U, internalMetric (D ω) V x y = G ω x y) :
    ∃ a : Ω → ℝ≥0∞, Measurable[m] a ∧
      ∀ᵐ ω ∂P, a ω = ENNReal.ofReal (setDist (D ω) A (frontier U)) := by
  have hB : frontier U ⊆ V := frontier_subset_closure.trans hUV
  obtain ⟨Y, hY, hYae⟩ := exists_local_iInf_internalMetric_representative (mΩ := mΩ) (m := m) hV
    (hAU.trans (subset_closure.trans hUV)) hB hmetric hG hEq
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYae, hmetric] with ω h1 h2
  rw [ofReal_setDist_boundary_eq_internalMetric h2 hU hAU hUV hA hfront, h1]

end HarmonicBalls
