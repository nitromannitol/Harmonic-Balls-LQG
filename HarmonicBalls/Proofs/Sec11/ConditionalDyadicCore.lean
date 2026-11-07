import HarmonicBalls.Proofs.Sec11.ConditionalVariableCore
import HarmonicBalls.Proofs.Sec11.ConditionalDyadicSeed
import HarmonicBalls.Proofs.Sec11.DyadicProtectedClass

/-! # Conditional mass and diameter via dyadic cores

The smooth-shift transfer uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- A conditional dyadic seed and a connected compact ambient core yield
conditional mass and diameter positivity. The uniform diameter tail and the
geometric containment hypotheses are explicit. -/
theorem IsWholePlaneGFF.condExp_mass_diameter_pos_of_dyadic_cores
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hξ : 0 < ξ)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (K U W : Set ℂ)
    (hbounded : Bornology.IsBounded (closedSquare z L))
    (hbufferS : ∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c : ℝ≥0∞) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hKc : IsCompact K) (hK : IsConnected K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hU : IsClosed U) (hKU : Disjoint K U) (hbuffer : W ⊆ thickening δ K)
    (hSW : closedSquare z L ⊆ W)
    (hSK : closedSquare z L ⊆ interior K)
    (hm : MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance ≤ m₀)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hH : @MeasurableSet Ω m₀ {ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare z L)})
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare z L)}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω)
    (hsmall : ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | c < μ ω (closedSquare z L) ∧
      internalDiam (𝔇 (hC ω)) δ K < ENNReal.ofReal σ}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω := by
  let : MeasurableSpace Ω := m₀
  apply h.condExp_absolute_mass_diameter_pos_of_variable_core_seeds hμ hξ
    (closedSquare z L) K U (IsCompact.reProdIm isCompact_Icc isCompact_Icc).isClosed.measurableSet
    hbounded hbufferS hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint c ha hmargin
  intro F hF hFp
  have hHK : ∀ᶠ n in atTop, ∀ (i : Fin (2 ^ n) × Fin (2 ^ n)),
      complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i ⊆ K := by
    filter_upwards [complex_enlarged_dyadic_square_eventually_subset_open z L hL
      isOpen_interior hSK] with n hn i
    have hr : 0 < L / (2 : ℝ) ^ n := by positivity
    exact (complexIntermediateGridSquare_subset_open_enlarged z _ hr i).trans
      ((complexOpenEnlargedGridSquare_subset z _ i).trans ((hn i).trans interior_subset))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hHK.and
    (complex_enlarged_dyadic_square_eventually_subset_open z L hL hW hSW))
  have hfail := h.tendsto_dyadic_square_diameters_of_power_error ξ
    (dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L)
    b (ENNReal.ofReal a) p hp e he hsmall hbound
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨n, hn, j, hpos⟩ := exists_conditional_mass_tile_seed_after P _ hm μ
    (closedSquare z L)
    (fun n j => squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)
    (fun n => {ω | ∀ i, dyadicIntermediateInternalDiameter
      (fun ω => 𝔇 (hC ω)) z L n i ω < ENNReal.ofReal a}) c N
    (complex_closed_square_subset_dyadic_classes z L hL) hH hcond hfail F hF hFp
  have hJ : ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexOpenEnlargedGridSquare z (L / (2 : ℝ) ^ n) i ⊆ W := by
    intro i
    exact (complexOpenEnlargedGridSquare_subset z _ i).trans ((hN n hn).2 i)
  let r : ℝ := L / (2 : ℝ) ^ n
  have hr : 0 < r := by dsimp [r]; positivity
  let ι := {i : Fin (2 ^ n) × Fin (2 ^ n) // squareParity i = j}
  let H : ι → Set ℂ := fun i => complexIntermediateGridSquare z r i.1
  let J : ι → Set ℂ := fun i => complexOpenEnlargedGridSquare z r i.1
  let S' := squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) r j
  let C := K \ ⋃ i : ι, interior (H i)
  obtain ⟨hCc, _, hcover, hattach, _, V, T, hVo, hVc, hCV, hVcompact,
    hTo, hVT, hTW, hTU, hTS⟩ :=
      dyadic_intermediate_connected_core_geometry z r hr j K W U hKc hK hW hKW hU hKU
        (fun i => (hN n hn).1 i.1)
  let A : Set Ω := {ω | ω ∈ F ∧ (∀ i : Fin (2 ^ n) × Fin (2 ^ n), ∀ x ∈
        complexIntermediateGridSquare z r i, ∀ y ∈ complexIntermediateGridSquare z r i,
          internalMetric (𝔇 (hC ω)) (complexOpenEnlargedGridSquare z r i) x y ≤ ENNReal.ofReal a) ∧
        (2 : ℝ≥0∞) * c < μ ω S'}
  have hpos' : 0 < P A := hpos.trans_le (measure_mono (by
    intro ω hω
    refine ⟨hω.1, ?_, hω.2.2⟩
    intro i x hx y hy
    have hle : internalMetric (𝔇 (hC ω))
        (complexOpenEnlargedGridSquare z r i) x y ≤
        dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω := by
      exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact hle.trans (hω.2.1 i).le))
  refine ⟨ι, S', W, V, T, C, H, J, A, (dyadic_class_closed_and_subset z L hL n j).2,
    (dyadic_class_closed_and_subset z L hL n j).1.measurableSet,
    (fun ω hω => hω.1), hpos', hW, hVo, hVc, ?_, hTo, hVcompact, hVT,
    hTS, hTU, ?_, ?_, hCc, hCV, hbuffer, hcover, hattach, ?_⟩
  · exact subset_closure.trans (hVT.trans hTW)
  · intro i
    exact isOpen_complexOpenEnlargedGridSquare z r i.1
  · intro i
    exact hJ i.1
  · intro ω hω
    refine ⟨?_, ?_⟩
    · have hc : c ≤ (2 : ℝ≥0∞) * c := by
        simp [two_mul]
      exact hc.trans_lt hω.2.2
    · intro i x hx y hy
      exact hω.2.1 i.1 x hx y hy

#print axioms IsWholePlaneGFF.condExp_mass_diameter_pos_of_dyadic_cores
end HarmonicBalls
