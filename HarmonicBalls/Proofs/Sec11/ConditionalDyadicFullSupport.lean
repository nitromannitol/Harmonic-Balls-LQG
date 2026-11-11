import HarmonicBalls.Proofs.Sec11.ConditionalDyadicCore
import HarmonicBalls.Proofs.Sec11.ConditionalAbsoluteMass
import HarmonicBalls.Proofs.Sec11.OutsideLogShiftSigma

/-! # Dyadic core contraction under full support

The smooth-shift transfer uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- Full support supplies the large-mass premise in the conditional dyadic
core argument. The diameter tail and the ambient geometry remain explicit. -/
theorem IsWholePlaneGFF.condExp_mass_diameter_pos_of_full_support_dyadic_cores
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ t : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (K U : Set ℂ)
    (hbufferS : ∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hKc : IsCompact K) (hK : IsConnected K)
    (hKU : Disjoint K (closure U))
    (hSK : closedSquare z L ⊆ interior K)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hsmall : ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | ENNReal.ofReal t < μ ω (closedSquare z L) ∧
      internalDiam (𝔇 (hC ω)) δ K < ENNReal.ofReal σ}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω := by
  let V := interior (closedSquare z L)
  have hVne : V.Nonempty := by
    refine ⟨z + ⟨L / 2, L / 2⟩, ?_⟩
    change z + ⟨L / 2, L / 2⟩ ∈ interior (closedSquare z L)
    simp only [closedSquare, Complex.interior_reProdIm, interior_Icc,
      Complex.mem_reProdIm, mem_Ioo, Complex.add_re, Complex.add_im]
    constructor <;> constructor <;> linarith
  have hSc : IsCompact (closedSquare z L) := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hSclosed : MeasurableSet (closedSquare z L) := hSc.isClosed.measurableSet
  have hScomp : closedSquare z L ⊆ (closure U)ᶜ := by
    intro x hx hxU
    exact Set.disjoint_left.mp hKU ((hSK hx) |> interior_subset) hxU
  have hcond := h.condExp_absolute_mass_pos_of_full_support hμ hγ
    (show 0 ≤ 8 * t by positivity) (closedSquare z L) V (closure U)ᶜ U
    hSc hSclosed isOpen_interior hVne interior_subset isClosed_closure.isOpen_compl hScomp
    (Set.disjoint_left.mpr (fun x hx hxu => hx (subset_closure hxu)))
    hpin hbufferS hfront hfull
  rw [comap_localModConstPairings_log_shift_eq α hC U] at hcond
  apply h.condExp_mass_diameter_pos_of_dyadic_cores hμ hξ z L hL K U (thickening δ K)
    hSc.isBounded hbufferS hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint (ENNReal.ofReal t)
    ha hmargin hKc hK isOpen_thickening (self_subset_thickening hδ K) hKU (Subset.rfl)
    ((hSK.trans interior_subset).trans (self_subset_thickening hδ K))
    hSK b p hp e he ?_ hsmall hbound
  simpa [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 by norm_num)] using hcond

end HarmonicBalls
