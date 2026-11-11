import HarmonicBalls.FirstPass.S11m.RootLimit
import HarmonicBalls.Steps.Sec11.PinchConstrainedFiniteness

/-!
# Finiteness of the internal metric on a connected open set

Route Step 4.1: a length metric inducing the Euclidean topology has finite
internal metric on each connected open domain. In Lean this is the finiteness source that Step 3.5 needed as the hypothesis
`hfin` of `tendsto_sphere_iInf_internalMetric` (`RootLimit.lean`): a connected open subset of `ℂ` is path connected, so two of
its points are joined inside it, and a length metric then gives a finite internal distance
(`IsEuclideanLengthMetric.internalMetric_lt_top_of_joinedIn`, used in the same way in `FirstPass/S11d/Finite.lean`).
No external input.
-/

namespace HarmonicBalls.S11m

open Set Metric Topology Filter

/-- Two points of a connected open set `O` have finite internal distance in `O`. -/
theorem internalMetric_ne_top_of_isConnected {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ}
    (hO : IsOpen O) (hconn : IsConnected O) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    internalMetric D O x y ≠ ⊤ := by
  have hpath : IsPathConnected O := (hO.isConnected_iff_isPathConnected).mp hconn
  have hjoin : JoinedIn O x y := hpath.joinedIn x hx y hy
  exact (hD.internalMetric_lt_top_of_joinedIn (isEuclideanLengthMetric_nonneg hD) hO hjoin).ne

/-- Step 3.5 (`tendsto_sphere_iInf_internalMetric`) with its finiteness hypothesis discharged by connectedness of `O`. -/
theorem tendsto_sphere_iInf_internalMetric_of_isConnected {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O : Set ℂ} (hO : IsOpen O) (hconn : IsConnected O) (h0 : (0 : ℂ) ∈ O) {x : ℂ} (hx : x ∈ O) (hx0 : x ≠ 0)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (O ×ˢ O)) :
    Tendsto (fun s : ℝ => ⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x) (𝓝[>] 0)
      (𝓝 (internalMetric D O 0 x)) :=
  tendsto_sphere_iInf_internalMetric hD hO h0 hx0
    (internalMetric_ne_top_of_isConnected hD hO hconn h0 hx) hcont

end HarmonicBalls.S11m
