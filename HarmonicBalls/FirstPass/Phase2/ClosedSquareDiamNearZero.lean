import HarmonicBalls.FirstPass.Phase2.ClosedSquareDiamAwayFromZero
import LatticeProb.LQG.SquareWeylDiameter

/-!
# Finite internal diameter of closed squares containing the singularity

Let `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` be the γ-LQG metric of `h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`) with
`α₀ < Q`. For a closed square `Q` with `0 ∈ Q`, almost surely `sup_{u, v ∈ Q} D_h(u, v; Q) < ∞`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17, pp. 43-44), provided the γ-LQG metric `𝔇`
has the uniform unit-square crossing tail of the same paper (Proposition 3.1, p. 13, at unit scale). This is the case
`0 ∈ Q` of the closed-square form of `ConnectedSquareUnionDiamFiniteFrozen`; with the case `0 ∉ Q`
(`ae_exists_internalMetric_closedSquare_le_of_zero_not_mem`) it removes the hypothesis `hNear0` of
`connectedSquareUnionDiamFiniteFrozen_of_unitTail`.

Proof. As for `0 ∉ Q`: the model is represented on the range space in `Type` (`LQGMetricUniv.rangeMeasure`), where
`LatticeProb.LQG.IsLQGMetric.ae_internalMetric_weylScaling_closedSquare_le_of_zero_mem` applies. That theorem needs a
positive crossing exponent `δ`; the tail at `δ` gives the tail at `δ' = max δ (K / 2)`, `K = ξ (Q - 2) log 2 > 0`, since
half crossings of length at most `e^{δ n}` have length at most `e^{δ' n}`.

## Main statements

* `HarmonicBalls.ae_exists_internalMetric_closedSquare_le_of_zero_mem`
* `HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail_derived`: `ConnectedSquareUnionDiamFiniteFrozen` from
  the field axioms, the positivity of the Weyl exponent and the uniform unit-square crossing tail.
-/

universe u

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- **Derived.** Finite internal diameter of a closed square containing `0` for the γ-LQG metric of a whole-plane GFF
plus `-α₀ log |·|` with `α₀ < Q` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17), from the
positivity of the Weyl exponent and the uniform unit-square crossing tail of `𝔇` (same paper, Proposition 3.1, p. 13).
The probability space may lie in any universe. -/
theorem ae_exists_internalMetric_closedSquare_le_of_zero_mem (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    {γ α₀ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {Q : Set ℂ} (hQ : LatticeProb.Topology.IsClosedSquare Q) (h0 : (0 : ℂ) ∈ Q) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hξ : 0 < ξ := hXi γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨δ, hδ, p, hp, huniv⟩ := hUniv γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨x, y, s, hs, rfl⟩ := hQ
  have hQQ : lqgQ γ = LatticeProb.LQG.lqgQ γ := rfl
  -- the crossing exponent `δ' = max δ (K / 2)` is positive and below `K = ξ (Q - 2) log 2`
  have hQ2 : 2 < lqgQ γ := by
    have hsq : 0 < (γ - 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
    unfold lqgQ
    have hcalc : 0 < (γ - 2) ^ 2 / (2 * γ) := div_pos hsq (by positivity)
    field_simp at hcalc ⊢
    nlinarith
  have hK : 0 < ξ * (lqgQ γ - 2) * Real.log 2 :=
    mul_pos (mul_pos hξ (by linarith)) (Real.log_pos one_lt_two)
  set K := ξ * (lqgQ γ - 2) * Real.log 2 with hKdef
  set δ' := max δ (K / 2) with hδ'def
  have hδ'K : δ' < K := max_lt hδ (by linarith)
  have hδ'0 : 0 < δ' := lt_of_lt_of_le (by linarith) (le_max_right δ (K / 2))
  have huniv' : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsWholePlaneGFF P' hC' hcirc' → ∀ n : ℕ,
        P' {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1
          (ENNReal.ofReal (Real.exp (δ' * n)))} ≤ p n := by
    intro Ω' _ P' hC' hcirc' hG n
    have hL : ENNReal.ofReal (Real.exp (δ * n)) ≤ ENNReal.ofReal (Real.exp (δ' * n)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (le_max_left δ (K / 2)) (Nat.cast_nonneg n)))
    refine le_trans (measure_mono ?_) (huniv Ω' P' hC' hcirc' hG n)
    exact fun ω hω h => hω (h.mono hL)
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
  have hmain := h𝔇'.ae_internalMetric_weylScaling_closedSquare_le_of_zero_mem hW' hξ
    (θ := (δ' + K) / 2) (by rw [← hQQ]; linarith) (by linarith) hδ'0
    (fun hC'' hcirc'' hG n => huniv' _ _ hC'' hcirc'' ((LPBridge.isWholePlaneGFF_iff _ _ _).2 hG) n) hp
    (α := α₀) (by rw [← hQQ]; exact hα) hs h0 (E := E) hE
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
LQG metric (`ConnectedSquareUnionDiamFiniteFrozen`) from the field axioms, the positivity of the Weyl exponent and the
uniform unit-square crossing tail of `𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1,
p. 13). This is `connectedSquareUnionDiamFiniteFrozen_of_unitTail` with its hypothesis `hNear0` (Proposition 3.17 of the
same paper) supplied by `ae_exists_internalMetric_closedSquare_le_of_zero_mem`. -/
theorem connectedSquareUnionDiamFiniteFrozen_of_unitTail_derived (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    ConnectedSquareUnionDiamFiniteFrozen.{u} :=
  connectedSquareUnionDiamFiniteFrozen_of_unitTail hAx hXi hUniv
    fun _ _ _ hγ0 hγ2 hα _ _ _ _ _ _ hW hD _ hQ h0 =>
      ae_exists_internalMetric_closedSquare_le_of_zero_mem hXi hUniv hγ0 hγ2 hα hW hD hQ h0

end HarmonicBalls
