import HarmonicBalls.FirstPass.Phase2.ConnectedSquareUnionDiamDerived
import HarmonicBalls.FirstPass.Phase2.LQGMetricAxiomsUniv
import HarmonicBalls.FirstPass.LPBridge.M5b
import LatticeProb.LQG.InternalMetricSquareTailWeyl

/-!
# Finite internal diameter of closed squares avoiding the singularity

Let `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` be the γ-LQG metric of `h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`). For a closed
square `Q` with `0 ∉ Q`, almost surely `sup_{u, v ∈ Q} D_h(u, v; Q) < ∞`, provided the γ-LQG metric `𝔇` has a uniform
unit-square crossing tail: for some `δ < ξ (Q_γ - 2) log 2` and `p` with `∑ₙ 4ⁿ pₙ < ∞`, for every whole-plane GFF on
a probability space in `Type`, the probability that the unit square has no half crossings of `D_{h^ℂ}`-length at most
`e^{δ n}` is at most `pₙ` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13, at unit
scale). This is the case `0 ∉ Q` of the closed-square form of `ConnectedSquareUnionDiamFiniteFrozen`
(`connectedSquareUnionDiamFiniteFrozen_iff_closedSquare`); the case `0 ∈ Q` is Proposition 3.17 of the same paper.

Proof. The exponent `ξ` is positive (`LQGMetricExponentPositive`). The model `(Ω, P, h^ℂ)`, with `Ω` in any universe, is
represented on the range space in `Type` (`LQGMetricUniv.rangeMeasure`), where it is again a whole-plane GFF. There the
weight `-α₀ log |·|` is continuous on `Q`, so `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling_continuousOn`
applies; the almost sure bound transfers back to `Ω` by `LQGMetricUniv.ae_rangeMeasure_iff`, and `D_h` is almost surely
the real form of the Weyl scaling.

## Main statements

* `HarmonicBalls.ae_exists_internalMetric_closedSquare_le_of_zero_not_mem`
* `HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail`: `ConnectedSquareUnionDiamFiniteFrozen` from the
  uniform unit-square crossing tail and the closed-square case `0 ∈ Q`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- **Derived.** Finite internal diameter of a closed square avoiding `0` for the γ-LQG metric of a whole-plane GFF plus
`-α₀ log |·|`, from the positivity of the Weyl exponent and the uniform unit-square crossing tail of `𝔇`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13). The probability space may lie in any
universe. -/
theorem ae_exists_internalMetric_closedSquare_le_of_zero_not_mem (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    {γ α₀ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {Q : Set ℂ} (hQ : LatticeProb.Topology.IsClosedSquare Q) (h0 : (0 : ℂ) ∉ Q) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hξ : 0 < ξ := hXi γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨δ, hδ, p, hp, huniv⟩ := hUniv γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨x, y, s, hs, rfl⟩ := hQ
  have hQQ : lqgQ γ = LatticeProb.LQG.lqgQ γ := rfl
  set f : ℂ → ℝ := fun z => -α₀ * Real.log ‖z‖ with hfdef
  set X := LQGMetricUniv.samplePoint hC hcirc (fun _ => 0) with hX
  have hW' : LatticeProb.Gauss.IsWholePlaneGFF (LQGMetricUniv.rangeMeasure P X) (fun y => y.1.pairing)
      (fun y => y.1.circle) :=
    (LPBridge.isWholePlaneGFF_iff _ _ _).1 (LQGMetricUniv.isWholePlaneGFF_rangeMeasure (fun _ => 0) hW)
  have h𝔇' := (LPBridge.isLQGMetric_iff γ ξ 𝔇).1 h𝔇
  let E : LQGMetricUniv.RangeSpace P X → ℂ → ℂ → ℝ := fun y u v => (weylScaling (𝔇 y.1.pairing) ξ f u v).toReal
  have hE : ∀ᵐ y ∂LQGMetricUniv.rangeMeasure P X, ∀ u v,
      ENNReal.ofReal (E y u v) = LatticeProb.LQG.weylScaling (𝔇 y.1.pairing) ξ f u v := by
    refine LQGMetricUniv.ae_rangeMeasure_iff.2 ?_
    filter_upwards [hDae] with ω hω u v
    have hne : weylScaling (𝔇 (hC ω)) ξ f u v ≠ ⊤ := by
      rw [← (hω u v).2]; exact ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_toReal hne
  have hcont : ContinuousOn f (Set.Icc x (x + s) ×ℂ Set.Icc y (y + s)) := by
    refine continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, norm_eq_zero]
    rintro rfl
    exact h0 hz
  have hmain := h𝔇'.ae_exists_internalMetric_closedSquare_le_of_weylScaling_continuousOn hW' hs hξ
    (θ := (δ + ξ * (lqgQ γ - 2) * Real.log 2) / 2) (by rw [← hQQ]; linarith) (by linarith)
    (fun hC'' hcirc'' hG n => huniv _ _ hC'' hcirc'' ((LPBridge.isWholePlaneGFF_iff _ _ _).2 hG) n) hp
    (E := E) hE hcont
  have hback := LQGMetricUniv.ae_rangeMeasure_iff.1 hmain
  filter_upwards [hback, hDae] with ω hA hω
  have hEq : E (LQGMetricUniv.toRange P X ω) = D ω := by
    funext u v
    show (weylScaling (𝔇 (hC ω)) ξ f u v).toReal = D ω u v
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  obtain ⟨A, hA⟩ := hA
  refine ⟨A, fun u hu v hv => ?_⟩
  rw [LPBridge.internalMetric_eq, ← hEq]
  exact hA u hu v hv

/-- **Derived.** The finite internal diameter of compact connected finite unions of closed rectangles for the singular
LQG metric (`ConnectedSquareUnionDiamFiniteFrozen`) from the field axioms, the positivity of the Weyl exponent, the
uniform unit-square crossing tail of `𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1,
p. 13) and the closed-square case `0 ∈ Q` (`hNear0`; same paper, Proposition 3.17, pp. 43-44). Squares avoiding `0` are
`ae_exists_internalMetric_closedSquare_le_of_zero_not_mem`; unions of rectangles reduce to squares by
`connectedSquareUnionDiamFiniteFrozen_iff_closedSquare`. -/
theorem connectedSquareUnionDiamFiniteFrozen_of_unitTail (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hNear0 : ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ Q : Set ℂ, LatticeProb.Topology.IsClosedSquare Q → (0 : ℂ) ∈ Q →
      ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A) :
    ConnectedSquareUnionDiamFiniteFrozen.{u} := by
  refine (connectedSquareUnionDiamFiniteFrozen_iff_closedSquare hAx).2 ?_
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hW hD Q hQ
  by_cases h0 : (0 : ℂ) ∈ Q
  · exact hNear0 γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hW hD Q hQ h0
  · exact ae_exists_internalMetric_closedSquare_le_of_zero_not_mem hXi hUniv hγ0 hγ2 hW hD hQ h0

end HarmonicBalls
