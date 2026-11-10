import HarmonicBalls.FirstPass.S11d.ShiftCore

/-!
# Proposition 11.9, the shifted event for a fixed realisation (fp-S11d, owner n3)

FIRST-PASS NEW. For one realisation, the metric `E` of the shifted field `h~` satisfies `E(·,·; W) ≤ ε` on `V`, given
(i) the square bound `D(·,·; S₂) ≤ ε/2` of `h` (from the 11.10 event), (ii) the exterior bound `D(·,·; O) ≤ n` on
`V \ S₂` (from `exists_measurable_internal_metric_bound`), (iii) the Weyl weight `ξ g ≤ 0` on an open `U ⊇ S₂` with `U ⊆ W`, and
`ξ g ≤ -c` on `O`, with `e^{-c} n ≤ ε/2`. This is the paper's chain (corrected paper lines 3127-3137).
-/

namespace HarmonicBalls

open Set

/-- The shifted-event bound for a fixed realisation (paper proof of `prop:mass-diam-gen`, lines 3127-3137). -/
theorem shifted_event_pointwise {Dr Eω : ℂ → ℂ → ℝ} {ξ c n ε : ℝ} {g : ℂ → ℝ} {V S O U W : Set ℂ}
    (hD : IsEuclideanLengthMetric Dr)
    (hE : IsEuclideanLengthMetric Eω) (hEnn : ∀ x y, 0 ≤ Eω x y)
    (hscale : ∀ x y, ENNReal.ofReal (Eω x y) = weylScaling Dr ξ g x y)
    (hε : 0 ≤ ε) (hV : IsOpen V) (hVc : IsConnected V) (hS : IsClosed S) (hSV : S ⊆ V)
    (hSne : S.Nonempty) (hO : IsOpen O) (hclO : closure (V \ S) ⊆ O) (hOW : O ⊆ W)
    (hU : IsOpen U) (hSU : S ⊆ U) (hUW : U ⊆ W)
    (hwU : ∀ z ∈ U, ξ * g z ≤ 0) (hwO : ∀ z ∈ O, ξ * g z ≤ -c)
    (hexp : Real.exp (-c) * n ≤ ε / 2)
    (hDS : ∀ u ∈ S, ∀ v ∈ S, internalMetric Dr S u v ≤ ENNReal.ofReal (ε / 2))
    (hDO : ∀ u ∈ V \ S, ∀ v ∈ V \ S, internalMetric Dr O u v ≤ ENNReal.ofReal n) :
    ∀ u ∈ V, ∀ v ∈ V, internalMetric Eω W u v ≤ ENNReal.ofReal ε := by
  have hS_W : ∀ u ∈ S, ∀ v ∈ S, internalMetric Eω W u v ≤ ENNReal.ofReal (ε / 2) :=
    shifted_bound_on_square hD hE hEnn hU hSU hUW hscale hwU hDS
  have hEO : ∀ x y, internalMetric Eω O x y ≤ ENNReal.ofReal (Real.exp (-c)) * internalMetric Dr O x y :=
    shifted_internalMetric_le_of_weight hD hE hEnn hO hscale hwO
  have hO_bd : ∀ u ∈ V \ S, ∀ v ∈ V \ S, internalMetric Eω O u v ≤ ENNReal.ofReal (ε / 2) :=
    shifted_bound_of_exterior hEO hDO hexp
  exact internalMetric_le_of_split_W hE hEnn hε hV hVc hS hSV hSne hO hclO hOW hS_W hO_bd

end HarmonicBalls
