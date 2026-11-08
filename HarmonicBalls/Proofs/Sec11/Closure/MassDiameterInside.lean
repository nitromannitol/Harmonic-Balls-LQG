import HarmonicBalls.Proofs.Sec11.ConditionalCoreMeasurability

/-!
# Conditional mass-diameter positivity from dyadic cores (Section 11, r7 lines 826–936)

Written argument: `notes/sec11-proof/sec11-proof-r7.tex`, the step "Large mass and small diameter" (r7 lines 826–936, Lemma `l:massdiam`). The hypothesis `hinside` of
`IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth`
(`Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`) asks, for every `n > 0` and `k : ℕ`, for the
conditional positivity of `{internalDiam D_h V < 1/n, k < μ_h(U)}` given the pinned outside σ-algebra.
This module shows that this is the conclusion of
`IsWholePlaneGFF.condExp_pinch_mass_diameter_pos_of_dyadic_cores`
(`Proofs/Sec11/ConditionalCoreMeasurability.lean:40`), for every threshold, once the dyadic tail premise
`SquareDyadicTailInput` is supplied.

The premises left open are explicit: `SquareDyadicTailInput` (the square internal-diameter tail, which the
written argument attributes to Pfeffer [P] Prop. 4.6, arXiv:2104.04020v3, not yet staged in `Proposed/`), the
full-support hypothesis `hfull` (from `LQGVolumeGrowthAllScalesStmt`), the positivity `0 < ξ`, and the geometric
hypotheses on the square and the pinned set. The producer yields null-measurability of the event; the measurable
clause of `hinside` is therefore not part of this statement.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The dyadic tail premise for the square `closedSquare z L` (leftover premise, not an input): for every
threshold `a > 0` there are a sequence `b`, an exponent `p > 2` and an error `e → 0` such that the dyadic
intermediate internal diameters of the square have the tail bound required by
`IsWholePlaneGFF.condExp_pinch_mass_diameter_pos_of_dyadic_cores`. The tail estimate of the square is the
input of Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3) in the written argument (r7 line 165). -/
def SquareDyadicTailInput {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (z : ℂ) (L : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ (b : ℕ → ℝ≥0∞) (p : ℝ) (_ : 2 < p) (e : ℕ → ℝ), Tendsto e atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, b n < ENNReal.ofReal a) ∧
    (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | b n * ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
        dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)))

/-- `hinside` of `positive_internal_pinch_of_conditional_growth` from the dyadic-core producer, for the
pinned σ-algebra `comap (localModConstPairings 0 hC O)`: the conditional positivity holds almost surely for every
`n > 0` (threshold `1/n`) and every `k : ℕ` (mass threshold `k`). The measurable clause is not included. -/
theorem hinside_of_square_dyadic_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {ε α γ ξ δ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (z : ℂ) (L : ℝ) (hL : 0 < L) (U V O : Set ℂ)
    (hU : MeasurableSet U) (hSU : closedSquare z L ⊆ U)
    (hbufferS : ∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ O)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hKc : IsCompact (closure V)) (hK : IsConnected (closure V))
    (hKO : Disjoint (closure V) (closure O))
    (hSK : closedSquare z L ⊆ interior (closure V))
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 z L) :
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance]) ω := by
  intro n hn k
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  set σ : ℝ := 1 / (n : ℝ) with hσ
  have hσpos : 0 < σ := one_div_pos.mpr hn'
  set a : ℝ := σ / 3 with ha_def
  have hapos : 0 < a := div_pos hσpos (by norm_num)
  obtain ⟨b, p, hp, e, he, hsmall, hbound⟩ := hdata a hapos
  obtain ⟨ψ, hψ, hψint⟩ :=
    IsTestFunction.exists_integral_eq_one (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  have key := h.condExp_pinch_mass_diameter_pos_of_dyadic_cores hμ hγ hξ z L hL U V O hU hSU
    hbufferS hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint (t := (k : ℝ)) (σ := σ) (a := a)
    (Nat.cast_nonneg k) hapos.le (by linarith) hKc hK hKO hSK hfull b p hp e he hsmall hbound
  have hσE : ENNReal.ofReal σ = (n : ℝ≥0∞)⁻¹ := by
    rw [hσ, one_div, ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]
  have hkE : ENNReal.ofReal (k : ℝ) = (k : ℝ≥0∞) := ENNReal.ofReal_natCast k
  rw [hσE, hkE] at key
  exact key

#print axioms hinside_of_square_dyadic_tail

end HarmonicBalls
