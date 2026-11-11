import HarmonicBalls.FirstPass.S11h.OuterDiamFinite
import HarmonicBalls.Steps.Sec11.LocalPathLength

/-!
# Section 11: exit distances and the certificate for the first pinch event

Locality facts of the corrected paper (`corrected paper lines 3419-3434`: exit and crossing distances are local by
first-boundary-hit truncation; "arbitrary point-to-point distances need not be local"), used for the first pinch event
`Ẽ₁` (`pinchFirstEvent`, `Draft/Section11.lean:95`). Only the two directions needed for event inclusions are proved:

* `iInf_frontier_internalMetric_le_ofReal`: the global distance from `x ∈ U` to `y ∈ ∂U` is at least the infimum over
  `z ∈ ∂U` of the internal distances `D(x, z; O)` with `closure U ⊆ O` (first-frontier cut, `exists_frontier_subpath`);
* `internalMetric_mono_set`: monotonicity of the internal metric in the domain (trivial);
* `first_conjunct_of_certificate`: an upper bound on the internal metric of the closed complement `(B_{2δ}(Q ∪ W))ᶜ`, by an
  internal metric of an open subset, and a lower bound on `setDist`, give the first conjunct of `pinchFirstEvent`.

Nothing here is a hypothesis; no EXTERNAL input is used.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Internal distance is antitone in the domain: a larger domain has more admissible paths, so smaller infimum. -/
theorem internalMetric_mono_set {D : ℂ → ℂ → ℝ} {U V : Set ℂ} (hUV : U ⊆ V) (z w : ℂ) :
    internalMetric D V z w ≤ internalMetric D U z w := by
  unfold internalMetric
  exact le_iInf₂ fun P hP => iInf₂_le P (fun t => hUV (hP t))

/-- Exit truncation: for an open `U` with `closure U ⊆ O`, `x ∈ U` and `y ∈ ∂U`, the global distance `D(x, y)` is at least
`inf_{z ∈ ∂U} D(x, z; O)` (every path from `x` to `y` is cut at its first frontier time). -/
theorem iInf_frontier_internalMetric_le_ofReal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U O : Set ℂ} (hU : IsOpen U) (hclO : closure U ⊆ O) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ frontier U) :
    (⨅ z ∈ frontier U, internalMetric D O x z) ≤ ENNReal.ofReal (D x y) := by
  rw [hD.ofReal_eq_internalMetric x y]
  unfold internalMetric
  refine le_iInf₂ fun p _ => ?_
  obtain ⟨y', hy', q, hq, hlen⟩ := exists_frontier_subpath D p hU hx hy hclO
  exact (iInf₂_le y' hy').trans ((iInf₂_le q hq).trans hlen)

/-- A lower bound by a common value: `r ≤ ofReal(setDist D A B)` as soon as `r ≤ ofReal(D x y)` for all pairs. -/
theorem le_ofReal_setDist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A B : Set ℂ}
    (hA : A.Nonempty) (hB : B.Nonempty) {r : ℝ≥0∞}
    (h : ∀ x ∈ A, ∀ y ∈ B, r ≤ ENNReal.ofReal (D x y)) : r ≤ ENNReal.ofReal (setDist D A B) := by
  obtain ⟨x0, hx0⟩ := hA
  obtain ⟨y0, hy0⟩ := hB
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h x0 hx0 y0 hy0)
  have hkey : ∀ x ∈ A, ∀ y ∈ B, r.toReal ≤ D x y := fun x hx y hy =>
    (ENNReal.le_ofReal_iff_toReal_le hr (hD.nonneg_apply x y)).mp (h x hx y hy)
  have hle : r.toReal ≤ setDist D A B := by
    unfold setDist
    refine le_csInf ⟨D x0 y0, mem_image2_of_mem hx0 hy0⟩ ?_
    intro b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_image2.mp hb
    exact hkey x hx y hy
  calc r = ENNReal.ofReal r.toReal := (ENNReal.ofReal_toReal hr).symm
    _ ≤ ENNReal.ofReal (setDist D A B) := ENNReal.ofReal_le_ofReal hle

/-- The exit lower bound for the set distance `setDist D Q' (∂U)`, with `Q' ⊆ U`. -/
theorem iInf_internalMetric_le_ofReal_setDist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U O Q' : Set ℂ} (hU : IsOpen U) (hclO : closure U ⊆ O) (hQ' : Q' ⊆ U) (hQ'ne : Q'.Nonempty)
    (hfr : (frontier U).Nonempty) :
    (⨅ x ∈ Q', ⨅ z ∈ frontier U, internalMetric D O x z) ≤ ENNReal.ofReal (setDist D Q' (frontier U)) := by
  refine le_ofReal_setDist hD hQ'ne hfr fun x hx y hy => ?_
  exact (iInf₂_le x hx).trans (iInf_frontier_internalMetric_le_ofReal hD hU hclO (hQ' hx) hy)

/-- The first conjunct of `Ẽ₁` (`pinchFirstEvent`), from a certificate: an open `O' ⊆ (B_{2δ}(Q ∪ W))ᶜ` whose
internal sup over `∂B₅` is below the exit lower bound through `O ⊇ closure Q`. -/
theorem first_conjunct_of_certificate {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {W Q Q' O O' : Set ℂ} {δ : ℝ} (hQ : IsOpen Q) (hclO : closure Q ⊆ O) (hQ' : Q' ⊆ Q)
    (hQ'ne : Q'.Nonempty) (hfr : (frontier Q).Nonempty) (hO' : O' ⊆ (thickening (2 * δ) (Q ∪ W))ᶜ)
    (hcert : (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D O' 0 x) <
      ⨅ x ∈ Q', ⨅ z ∈ frontier Q, internalMetric D O x z) :
    (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le hcert (iInf_internalMetric_le_ofReal_setDist hD hQ hclO hQ' hQ'ne hfr))
  exact iSup₂_mono fun x _ => internalMetric_mono_set hO' 0 x

#print axioms first_conjunct_of_certificate
#print axioms iInf_internalMetric_le_ofReal_setDist

/-- The second conjunct of `Ẽ₁` (`pinchFirstEvent`), from a certificate: the internal diameter of the set is below the
internal distances from `0` to the circle `∂B_δ` inside `O ⊇ closure B_δ`; the set distance from `0` to `∂B_δ` is
its exit lower bound (`frontier (ball 0 δ) = sphere 0 δ`). -/
theorem second_conjunct_of_certificate {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A O : Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hclO : closure (ball (0 : ℂ) δ) ⊆ O)
    (hcert : internalDiam D δ A < ⨅ z ∈ sphere (0 : ℂ) δ, internalMetric D O 0 z) :
    internalDiam D δ A < ENNReal.ofReal (setDist D {0} (sphere (0 : ℂ) δ)) := by
  have hL := iInf_internalMetric_le_ofReal_setDist hD (U := ball (0 : ℂ) δ) (O := O) (Q' := {0})
    isOpen_ball hclO (singleton_subset_iff.mpr (mem_ball_self hδ)) (singleton_nonempty _)
    (by rw [frontier_ball (0 : ℂ) hδ.ne']; exact (NormedSpace.sphere_nonempty (x := (0 : ℂ))).mpr hδ.le)
  rw [frontier_ball (0 : ℂ) hδ.ne'] at hL
  simp only [iInf_singleton] at hL
  exact lt_of_lt_of_le hcert hL

#print axioms second_conjunct_of_certificate

end HarmonicBalls
