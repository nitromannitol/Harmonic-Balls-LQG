import HarmonicBalls.Proofs.GFF.PfefferQuadraticCrossingTightness

/-! # Normalized quadratic crossing ratios

Finite nonzero normalizations cancel from the annular crossing ratios.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- The normalization from Axiom V is finite and is nonzero when the
scale constant is positive. -/
theorem pfefferNormalization_ne_zero_ne_top {Ω : Type*} (ξ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) (c : ℝ → ℝ)
    {r : ℝ} (ω : Ω) (hc : 0 < c r) :
    pfefferNormalization ξ hcirc f c r ω ≠ 0 ∧
      pfefferNormalization ξ hcirc f c r ω ≠ ⊤ := by
  constructor
  · apply (ENNReal.ofReal_pos.mpr ?_).ne'
    exact mul_pos (inv_pos.mpr hc) (Real.exp_pos _)
  · exact ENNReal.ofReal_ne_top

/-- A finite nonzero normalization cancels from each pair of crossings. -/
theorem quadraticCrossingFamily_ratios_eq {Ω : Type*}
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {r : ℝ} {ω : Ω}
    (hN0 : N r ω ≠ 0) (hNt : N r ω ≠ ⊤)
    (hK0 : K r ω ≠ 0) (hKt : K r ω ≠ ⊤) :
    quadraticCrossingFamily D E N K 0 r ω / quadraticCrossingFamily D E N K 1 r ω =
      pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) /
        pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r) ∧
    quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω =
      pfefferAcross (E ω) 0 r (2 * r) /
        pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) := by
  constructor
  · exact ENNReal.mul_div_mul_left _ _ hN0 hNt
  · exact ENNReal.mul_div_mul_left _ _ hK0 hKt

/-- The two crossing comparisons yield an exponential lower bound for the
ratio of normalized shifted crossings. -/
theorem quadraticCrossingFamily_ratio_lower {Ω : Type*}
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {ξ r : ℝ} {ω : Ω}
    (hN0 : N r ω ≠ 0) (hNt : N r ω ≠ ⊤)
    (hK0 : K r ω ≠ 0) (hKt : K r ω ≠ ⊤)
    (hlower : ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
      pfefferAcross (E ω) 0 r (2 * r))
    (hupper : pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
      ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
        pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)) :
    ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
      (quadraticCrossingFamily D E N K 0 r ω / quadraticCrossingFamily D E N K 1 r ω) ≤
      quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω := by
  have h := ENNReal.div_le_div hlower hupper
  have hexp : ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) =
      ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) /
      ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    congr 2
    ring
  change ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
    ((N r ω * pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r)) /
      (N r ω * pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r))) ≤
    (K r ω * pfefferAcross (E ω) 0 r (2 * r)) /
      (K r ω * pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r))
  rw [ENNReal.mul_div_mul_left _ _ hN0 hNt, ENNReal.mul_div_mul_left _ _ hK0 hKt,
    hexp]
  rw [← ENNReal.mul_div_mul_comm
    (Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  exact h

/-- The constants in the ratio bounds are finite and nonzero. -/
theorem quadraticCrossingFamily_ratio_constants {M : Fin 4 → ℝ} (hM : ∀ i, 0 < M i) :
    ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1) ≠ 0 ∧
    ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1) ≠ ⊤ ∧
    ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹ ≠ 0 ∧
    ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹ ≠ ⊤ := by
  have h0 (i : Fin 4) : ENNReal.ofReal (M i) ≠ 0 := (ENNReal.ofReal_pos.mpr (hM i)).ne'
  have hi (i : Fin 4) : ENNReal.ofReal (M i)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hM i))).ne'
  exact ⟨ENNReal.div_ne_zero.mpr ⟨hi 0, ENNReal.ofReal_ne_top⟩,
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (h0 1),
    ENNReal.div_ne_zero.mpr ⟨h0 2, ENNReal.ofReal_ne_top⟩,
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (hi 3)⟩

/-- On the common crossing event, the ratio is bounded below by an
exponential factor and above by constants independent of the radius. -/
theorem quadraticCrossingFamily_ratio_bounds {Ω : Type*}
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {ξ r : ℝ} {ω : Ω}
    {M : Fin 4 → ℝ}
    (hN0 : N r ω ≠ 0) (hNt : N r ω ≠ ⊤)
    (hK0 : K r ω ≠ 0) (hKt : K r ω ≠ ⊤)
    (hb : ∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E N K i r ω ∧
      quadraticCrossingFamily D E N K i r ω ≤ ENNReal.ofReal (M i))
    (hlower : ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
      pfefferAcross (E ω) 0 r (2 * r))
    (hupper : pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
      ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
        pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)) :
    ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
        (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
      quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ∧
    quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ≤
      ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹ := by
  constructor
  · exact (mul_le_mul_right (ENNReal.div_le_div (hb 0).1 (hb 1).2) _).trans
      (quadraticCrossingFamily_ratio_lower hN0 hNt hK0 hKt hlower hupper)
  · exact ENNReal.div_le_div (hb 2).2 (hb 3).1

/-- The quantitative ratio bounds hold with arbitrarily high probability at
every positive radius under the stated metric and normalization assumptions. -/
theorem quadraticCrossingFamily_ratio_simultaneous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {ξ : ℝ}
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hpointD : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hpointE : ∀ x y, AEMeasurable (fun ω => E ω x y) P)
    (hN : ∀ r, 0 < r → AEMeasurable (N r) P)
    (hK : ∀ r, 0 < r → AEMeasurable (K r) P)
    (hNfinite : ∀ r, 0 < r → ∀ᵐ ω ∂P, N r ω ≠ 0 ∧ N r ω ≠ ⊤)
    (hKfinite : ∀ r, 0 < r → ∀ᵐ ω ∂P, K r ω ≠ 0 ∧ K r ω ≠ ⊤)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily D E N K i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
            (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
          quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ∧
        quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ≤
          ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹} := by
  obtain ⟨M, hM, hbound⟩ := quadraticCrossingFamily_simultaneous
    hξ hD hE hpointD hpointE hN hK hscale htight hε hε1
  refine ⟨M, hM, fun r hr => ?_⟩
  let A := {ω | (∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E N K i r ω ∧
      quadraticCrossingFamily D E N K i r ω ≤ ENNReal.ofReal (M i)) ∧
    ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
      pfefferAcross (E ω) 0 r (2 * r) ∧
    pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
      ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
        pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)}
  let B := {ω | ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
        (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
      quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ∧
    quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ≤
      ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹}
  have hae : A ≤ᵐ[P] B := by
    filter_upwards [hNfinite r hr, hKfinite r hr] with ω hn hk hω
    exact quadraticCrossingFamily_ratio_bounds hn.1 hn.2 hk.1 hk.2 hω.1 hω.2.1 hω.2.2
  exact (hbound r hr).trans (measure_mono_ae hae)

end HarmonicBalls
