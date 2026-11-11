import HarmonicBalls.FirstPass.S11d.Core
import HarmonicBalls.FirstPass.S11d.ShiftBound

/-!
# Proposition 11.9, the core and the square bound for the shifted metric

Three deterministic steps of the proof of `prop:mass-diam-gen` (corrected paper, lines 3127-3137) for the
Weyl-shifted metric `E` of `h~`:
* `shifted_bound_on_square`: on the closed dyadic square `S₂` the metric `E(·,·; W)` is bounded by the metric `D(·,·; S₂)`
  of `h`, because the weight of the shift is `≤ 0` on an open `U` with `S₂ ⊆ U ⊆ W` (the closed-set comparison is avoided:
  `E(W) ≤ E(U) ≤ D(U) ≤ D(S₂)`, `E(U) ≤ D(U)` by the open-set Weyl comparison `shifted_internalMetric_le_of_weight`);
* `internalMetric_le_of_split_W`: the triangle step of `Core.lean` with the square bound stated for `E(·,·; W)`;
* `shift_constants`: `c = log(2(n+ε)/ε) ≥ 0` and `e^{-c} n ≤ ε/2`, for the exterior constant `n`.
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal

/-- The square bound for the shifted metric: `E(·,·; W) ≤ a` on `S × S` from `D(·,·; S) ≤ a` on `S × S`. -/
theorem shifted_bound_on_square {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y) {ξ : ℝ} {g : ℂ → ℝ}
    {S U W : Set ℂ} {a : ℝ} (hU : IsOpen U) (hSU : S ⊆ U) (hUW : U ⊆ W)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ g x y)
    (hweight : ∀ z ∈ U, ξ * g z ≤ 0)
    (hDS : ∀ u ∈ S, ∀ v ∈ S, internalMetric D S u v ≤ ENNReal.ofReal a) :
    ∀ u ∈ S, ∀ v ∈ S, internalMetric E W u v ≤ ENNReal.ofReal a := by
  intro u hu v hv
  have hEU := shifted_internalMetric_le_of_weight hD hE hEnonneg hU hscale hweight u v
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul] at hEU
  calc internalMetric E W u v ≤ internalMetric E U u v := internalMetric_anti E hUW u v
    _ ≤ internalMetric D U u v := hEU
    _ ≤ internalMetric D S u v := internalMetric_anti D hSU u v
    _ ≤ ENNReal.ofReal a := hDS u hu v hv

/-- The triangle step of `internalMetric_le_of_split` with the square bound stated for the metric on `W`. -/
theorem internalMetric_le_of_split_W {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V S O W : Set ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hV : IsOpen V) (hVc : IsConnected V) (hS : IsClosed S) (hSV : S ⊆ V) (hSne : S.Nonempty)
    (hO : IsOpen O) (hclO : closure (V \ S) ⊆ O) (hOW : O ⊆ W)
    (hS_W : ∀ u ∈ S, ∀ v ∈ S, internalMetric D W u v ≤ ENNReal.ofReal (ε / 2))
    (hO_bd : ∀ u ∈ V \ S, ∀ v ∈ V \ S, internalMetric D O u v ≤ ENNReal.ofReal (ε / 2)) :
    ∀ u ∈ V, ∀ v ∈ V, internalMetric D W u v ≤ ENNReal.ofReal ε := by
  have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hext := internalMetric_le_on_closure hD hnonneg hO hclO hO_bd
  intro u hu v hv
  by_cases hus : u ∈ S
  · by_cases hvs : v ∈ S
    · exact (hS_W u hus v hvs).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · obtain ⟨w, hwcl, hwS⟩ := closure_diff_inter_nonempty hV hVc hS hSV hSne ⟨v, hv, hvs⟩
      have hvcl : v ∈ closure (V \ S) := subset_closure ⟨hv, hvs⟩
      calc internalMetric D W u v
          ≤ internalMetric D W u w + internalMetric D W w v := hD.internalMetric_triangle W u w v
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hS_W u hus w hwS) ((internalMetric_anti D hOW w v).trans (hext w hwcl v hvcl))
        _ = ENNReal.ofReal ε := hsum
  · by_cases hvs : v ∈ S
    · obtain ⟨w, hwcl, hwS⟩ := closure_diff_inter_nonempty hV hVc hS hSV hSne ⟨u, hu, hus⟩
      have hucl : u ∈ closure (V \ S) := subset_closure ⟨hu, hus⟩
      calc internalMetric D W u v
          ≤ internalMetric D W u w + internalMetric D W w v := hD.internalMetric_triangle W u w v
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add ((internalMetric_anti D hOW u w).trans (hext u hucl w hwcl)) (hS_W w hwS v hvs)
        _ = ENNReal.ofReal ε := hsum
    · exact (internalMetric_anti D hOW u v).trans
        ((hO_bd u ⟨hu, hus⟩ v ⟨hv, hvs⟩).trans (ENNReal.ofReal_le_ofReal (by linarith)))

/-- The constants of the shift: `c = log (2 (n+ε)/ε) ≥ 0` and `e^{-c} n ≤ ε/2` (paper line 3127, `c = log(2A/ε)`). -/
theorem shift_constants {ε n : ℝ} (hε : 0 < ε) (hn : 0 ≤ n) :
    0 ≤ Real.log (2 * (n + ε) / ε) ∧ Real.exp (-Real.log (2 * (n + ε) / ε)) * n ≤ ε / 2 := by
  have hpos : 0 < 2 * (n + ε) / ε := by positivity
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    nlinarith
  · rw [Real.exp_neg, Real.exp_log hpos, inv_mul_le_iff₀ hpos]
    have key : 2 * (n + ε) / ε * (ε / 2) = n + ε := by field_simp
    rw [key]
    linarith

end HarmonicBalls
