import HarmonicBalls.Steps.Sec11.BoundaryClearance

/-!
# No shortcut near a point of an open set

Deterministic length-space lemma. For a Euclidean length metric `D` (in the sense of Armstrong, Kuusi and Mourrat:
`IsEuclideanLengthMetric`) and an open set `U ∋ 0`, the ambient length metric equals the internal metric of `U`
on a small closed Euclidean ball about `0`. This is the statement `NoShortcutSmallBallStmt` of
`HarmonicBalls/FirstPass/S11at.lean`, which the eventual covariance lemmas take as a hypothesis.

Proof. Choose `δ > 0` with the `D`-ball of radius `δ` about `0` inside `U`. Every point outside `U` is then at
`D`-distance at least `δ` from `0`. The `D`-ball of radius `δ/4` about `0` is a Euclidean neighbourhood of `0`, since
`D` induces the Euclidean topology. For `x`, `y` in a small Euclidean ball about `0` inside it, every point outside `U`
is at `D`-distance at least `δ/2` from `x`, and `D x y < δ/2`. The boundary-clearance lemma
`IsEuclideanLengthMetric.internalMetric_eq_of_boundary_clearance` then gives `internalMetric D U x y = ofReal (D x y)`.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- **No shortcut near a point of an open set (deterministic).** Let `D` be a Euclidean length metric and `U` an open
set containing `0`. There is a Euclidean radius `ρ > 0` such that for all `x, y` in the closed Euclidean ball of radius
`ρ` about `0`, the ambient length metric equals the internal metric of `U`:
`ENNReal.ofReal (D x y) = internalMetric D U x y`. This is the locality used to replace the ambient metric by the
internal metric on a small window (step 6b). -/
theorem eq_internalMetric_on_small_ball {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
      ENNReal.ofReal (D x y) = internalMetric D U x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  -- the `D`-ball of radius `δ` about `0` lies in `U`
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff U).1 hU 0 h0
  -- the `D`-ball of radius `δ / 4` about `0` is open for the Euclidean topology
  have hS : IsOpen {w : ℂ | D 0 w < δ / 4} := by
    refine (hD.isOpen_iff _).2 fun z hz => ⟨δ / 4 - D 0 z, ?_, fun w hw => ?_⟩
    · have hz' : D 0 z < δ / 4 := hz
      linarith
    · have hz' : D 0 z < δ / 4 := hz
      have htri := hD.triangle 0 z w
      have hw' : D z w < δ / 4 - D 0 z := hw
      show D 0 w < δ / 4
      linarith
  have h00 : (0 : ℂ) ∈ {w : ℂ | D 0 w < δ / 4} := by
    show D 0 0 < δ / 4
    rw [hD.self_eq_zero]
    linarith
  obtain ⟨η, hη, hηS⟩ := Metric.isOpen_iff.1 hS 0 h00
  have key : ∀ x ∈ closedBall (0 : ℂ) (η / 2), D 0 x < δ / 4 := by
    intro x hx
    have hdist : dist x 0 < η := by
      have := mem_closedBall.1 hx
      linarith
    exact hηS (mem_ball.2 hdist)
  refine ⟨η / 2, by linarith, fun x hx y hy => ?_⟩
  have hx' := key x hx
  have hy' := key y hy
  have hxy : D x y < δ / 2 := by
    have htri := hD.triangle x 0 y
    have hsymm := hD.symm x 0
    linarith
  have hclear : ∀ z ∉ U, δ / 2 ≤ D x z := by
    intro z hz
    have hz0 : δ ≤ D 0 z := by
      by_contra hlt
      exact hz (hball z (not_le.1 hlt))
    have htri := hD.triangle 0 x z
    linarith
  exact (hD.internalMetric_eq_of_boundary_clearance hnonneg hclear hxy).symm

end HarmonicBalls
