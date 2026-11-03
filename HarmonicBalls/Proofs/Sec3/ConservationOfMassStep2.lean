import HarmonicBalls.Proofs.Sec3.PositiveDistribution
import HarmonicBalls.Steps.SecA.ObstacleConservationOfMass

/-!
# Lemma A.5: Step 2 (eq:laplacian-of-v, lines 3797-3803)

`obstacleConservationOfMassStep2_holds`. With `v = w - (-t G + q)`, the functional
`S φ = ∫ w Δφ + ∫ φ dμ` satisfies `∫ v Δφ = S φ - t φ(z)` (`ΔG = -δ_z`, `Δq = -μ`), `S φ ≤ ∫ φ dμ` for `φ ≥ 0`
(`Δw ≤ 0` on `U`), `S φ = ∫ φ dμ` for `φ` supported in `Λ` (`Δw = 0` on `Λ`) and `S φ ≥ 0` for `φ ≥ 0` supported
in `U \ {z}` (Step 1, `Δv ≥ 0` there). Splitting `φ = χ φ + (1 - χ) φ` with a cut-off `χ = 1` near `z` supported
in `Λ`, `S` is a positive distribution on `U`, hence a measure `σ` (`exists_measure_of_isPositiveOnTests`,
Riesz–Markov–Kakutani). Comparison on open sets gives `σ ≤ μ` (outer regularity of `μ`), `σ = μ` on `Λ` (outer
regularity of `σ`) and `σ = 0` on `U \ closure Λ` (where `v = 0`), so `σ = μ|_Λ + σ|_{∂Λ}`; take `ν = σ`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff ENNReal

theorem IsTestFunction.mono_set {V W : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction V φ) (hVW : V ⊆ W) :
    IsTestFunction W φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVW⟩

theorem IsTestFunction.mul_contDiff {V : Set ℂ} {χ φ : ℂ → ℝ} (hχ : IsTestFunction V χ)
    (hφ : ContDiff ℝ ∞ φ) : IsTestFunction V (fun x => χ x * φ x) := by
  have hts : tsupport (fun x => χ x * φ x) ⊆ tsupport χ := tsupport_mul_subset_left
  exact ⟨hχ.1.mul hφ, IsCompact.of_isClosed_subset hχ.2.1 (isClosed_tsupport _) hts, hts.trans hχ.2.2⟩

/-- **Lemma A.5, Step 2** (`ObstacleConservationOfMassStep2`). -/
theorem obstacleConservationOfMassStep2_holds : ObstacleConservationOfMassStep2 := by
  intro U Λ z μ t w G q hU hΛ hΛU hzΛ hμ ht hwLE hwΛ hG hq hvGE hv0
  set v : ℂ → ℝ := fun x => w x - (-t * G x + q x) with hvdef
  have hμint : ∀ φ, IsTestFunction U φ → Integrable φ μ := fun φ hφ =>
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  set S : (ℂ → ℝ) → ℝ := fun φ => (∫ x, w x * Δ φ x) + ∫ x, φ x ∂μ with hSdef
  -- `⟨v, Δφ⟩ = S φ - t φ(z)`
  have hvΔ : ∀ φ, IsTestFunction U φ → ∫ x, v x * Δ φ x = S φ - t * φ z := by
    intro φ hφ
    obtain ⟨-, -, hG'⟩ := hG.2 φ hφ
    obtain ⟨-, -, hq'⟩ := hq.2 φ hφ
    have i1 := integrable_mul_laplacian hwLE.1 hφ
    have i2 := integrable_mul_laplacian hG.1 hφ
    have i3 := integrable_mul_laplacian hq.1 hφ
    have hfun : (fun x => v x * Δ φ x) = fun x => w x * Δ φ x + t * (G x * Δ φ x) - q x * Δ φ x := by
      funext x
      simp only [hvdef]
      ring
    have i12 : Integrable (fun x => w x * Δ φ x + t * (G x * Δ φ x)) := i1.add (i2.const_mul t)
    rw [hfun, integral_sub i12 i3, integral_add i1 (i2.const_mul t), integral_const_mul, hG', hq']
    simp only [integral_zero_measure, integral_dirac, hSdef]
    ring
  have hlin : IsLinearOnTests U S := by
    intro φ ψ hφ hψ a b
    simp only [hSdef]
    rw [integral_mul_laplacian_const_mul_add_const_mul hwLE.1 hφ hψ a b,
      integral_add ((hμint φ hφ).const_mul a) ((hμint ψ hψ).const_mul b), integral_const_mul, integral_const_mul]
    ring
  have hSle : ∀ φ, IsTestFunction U φ → (∀ x, 0 ≤ φ x) → S φ ≤ ∫ x, φ x ∂μ := by
    intro φ hφ hφ0
    have := hwLE.2 φ hφ (fun x => hφ0 x) integrable_zero_measure
    rw [integral_zero_measure] at this
    simp only [hSdef]
    linarith
  have hSΛ : ∀ φ, IsTestFunction Λ φ → S φ = ∫ x, φ x ∂μ := by
    intro φ hφ
    obtain ⟨-, -, h⟩ := hwΛ.2 φ hφ
    simp only [integral_zero_measure, sub_self] at h
    simp only [hSdef, h, zero_add]
  -- a cut-off `χ = 1` near the pole, supported in `Λ`
  obtain ⟨r, hr, hrΛ⟩ := Metric.isOpen_iff.1 hΛ z hzΛ
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen
    (isCompact_closedBall z (r / 2)) isOpen_ball (closedBall_subset_ball (half_lt_self hr))
  have hχΛ : IsTestFunction Λ χ := ⟨hχd, hχc, hχU.trans hrΛ⟩
  -- `S` is a positive distribution on `U`
  have hpos : IsPositiveOnTests U S := by
    intro φ hφ hφ0
    have hψ₁Λ : IsTestFunction Λ (fun x => χ x * φ x) := hχΛ.mul_contDiff hφ.1
    have hψ₁ : IsTestFunction U (fun x => χ x * φ x) := hψ₁Λ.mono_set hΛU
    have hψ₂0 : IsTestFunction U (fun x => 1 * φ x + (-1) * (χ x * φ x)) :=
      hφ.const_mul_add_const_mul hψ₁ 1 (-1)
    have hzψ₂ : z ∉ tsupport (fun x => 1 * φ x + (-1) * (χ x * φ x)) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [ball_mem_nhds z (half_pos hr)] with x hx
      simp only [Pi.zero_apply]
      rw [hχ1 x (ball_subset_closedBall hx)]
      ring
    have hψ₂ : IsTestFunction (U \ {z}) (fun x => 1 * φ x + (-1) * (χ x * φ x)) :=
      ⟨hψ₂0.1, hψ₂0.2.1, fun x hx => ⟨hψ₂0.2.2 hx, fun h => hzψ₂ (h ▸ hx)⟩⟩
    have hsplit : φ = fun x => 1 * (χ x * φ x) + 1 * (1 * φ x + (-1) * (χ x * φ x)) := by
      funext x
      ring
    have hS := hlin _ _ hψ₁ hψ₂0 1 1
    rw [← hsplit] at hS
    have h1 : 0 ≤ S (fun x => χ x * φ x) := by
      rw [hSΛ _ hψ₁Λ]
      exact integral_nonneg fun x => mul_nonneg (hχ01 x).1 (hφ0 x)
    have h2 : 0 ≤ S (fun x => 1 * φ x + (-1) * (χ x * φ x)) := by
      have hnn : ∀ x, 0 ≤ (fun x => 1 * φ x + (-1) * (χ x * φ x)) x := fun x => by
        show (0 : ℝ) ≤ 1 * φ x + (-1) * (χ x * φ x)
        nlinarith [(hχ01 x).2, hφ0 x]
      have hge := (hvGE.2 _ hψ₂ hnn).2
      rw [integral_zero_measure, hvΔ _ hψ₂0] at hge
      have hz0 : 1 * φ z + (-1) * (χ z * φ z) = 0 := by
        rw [hχ1 z (mem_closedBall_self (half_pos hr).le)]
        ring
      rw [hz0, mul_zero, sub_zero] at hge
      exact hge
    rw [hS]
    linarith
  obtain ⟨σ, hσU, hσK, hσφ⟩ := exists_measure_of_isPositiveOnTests hU hlin hpos
  -- `σ ≤ μ` on open subsets of `U`, hence everywhere
  have hC0 : ∀ V, IsOpen V → V ⊆ U → σ V ≤ μ V := fun V hV hVU =>
    measure_le_of_integral_le hV fun φ hφ hφ01 =>
      ⟨(hσφ φ (hφ.mono_set hVU)).1, hμint φ (hφ.mono_set hVU), by
        rw [(hσφ φ (hφ.mono_set hVU)).2]
        exact hSle φ (hφ.mono_set hVU) fun x => (hφ01 x).1⟩
  have hσμ : σ ≤ μ := by
    rw [Measure.le_iff]
    intro A hA
    rw [measure_eq_iInf_isOpen A μ]
    refine le_iInf fun V => le_iInf fun hAV => le_iInf fun hV => ?_
    have hsub : A ⊆ (V ∩ U) ∪ Uᶜ := fun x hx => by
      by_cases h : x ∈ U
      exacts [Or.inl ⟨hAV hx, h⟩, Or.inr h]
    calc σ A ≤ σ ((V ∩ U) ∪ Uᶜ) := measure_mono hsub
      _ ≤ σ (V ∩ U) + σ Uᶜ := measure_union_le _ _
      _ = σ (V ∩ U) := by rw [hσU, add_zero]
      _ ≤ μ (V ∩ U) := hC0 _ (hV.inter hU) inter_subset_right
      _ ≤ μ V := measure_mono inter_subset_left
  have : IsLocallyFiniteMeasure σ := Measure.isLocallyFiniteMeasure_of_le hσμ
  -- `σ = μ` on `Λ`
  have hC0Λ : ∀ W, IsOpen W → W ⊆ Λ → μ W ≤ σ W := fun W hW hWΛ =>
    measure_le_of_integral_le hW fun φ hφ _ =>
      ⟨hμint φ ((hφ.mono_set hWΛ).mono_set hΛU), (hσφ φ ((hφ.mono_set hWΛ).mono_set hΛU)).1, by
        rw [(hσφ φ ((hφ.mono_set hWΛ).mono_set hΛU)).2, hSΛ φ (hφ.mono_set hWΛ)]⟩
  have hΛeq : ∀ A, σ (A ∩ Λ) = μ (A ∩ Λ) := by
    intro A
    refine le_antisymm (Measure.le_iff'.1 hσμ _) ?_
    rw [measure_eq_iInf_isOpen (A ∩ Λ) σ]
    refine le_iInf fun V => le_iInf fun hAV => le_iInf fun hV => ?_
    calc μ (A ∩ Λ) ≤ μ (V ∩ Λ) := measure_mono fun x hx => ⟨hAV hx, hx.2⟩
      _ ≤ σ (V ∩ Λ) := hC0Λ _ (hV.inter hΛ) inter_subset_right
      _ ≤ σ V := measure_mono inter_subset_left
  -- `σ = 0` on `U \ closure Λ`, where `v = 0`
  have hσout : σ (U \ closure Λ) = 0 := by
    refine nonpos_iff_eq_zero.1 ?_
    have h := measure_le_of_integral_le (ν₁ := σ) (ν₂ := 0) (hU.sdiff isClosed_closure) fun φ hφ _ => by
      have hφU : IsTestFunction U φ := hφ.mono_set sdiff_subset
      refine ⟨(hσφ φ hφU).1, integrable_zero_measure, ?_⟩
      rw [(hσφ φ hφU).2, integral_zero_measure]
      have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => (hφ.2.2 h).2 (subset_closure hzΛ)
      have hvφ : (fun x => v x * Δ φ x) = fun _ => 0 := by
        funext x
        by_cases hx : x ∈ tsupport φ
        · have hxW := hφ.2.2 hx
          rw [show v x = 0 from hv0 x ⟨hxW.1, fun h => hxW.2 (subset_closure h)⟩, zero_mul]
        · rw [laplacian_eq_zero_of_notMem_tsupport hx, mul_zero]
      have := hvΔ φ hφU
      rw [hvφ, integral_zero, hφz, mul_zero, sub_zero] at this
      exact this.symm.le
    simpa using h
  -- `σ = μ|_Λ + σ|_{∂Λ}`
  have hσcl : σ (closure Λ)ᶜ = 0 := by
    refine measure_mono_null (t := (U \ closure Λ) ∪ Uᶜ) (fun x hx => ?_) (measure_union_null hσout hσU)
    by_cases h : x ∈ U
    exacts [Or.inl ⟨h, hx⟩, Or.inr h]
  have hdecomp : σ = μ.restrict Λ + σ.restrict (frontier Λ) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.add_apply, Measure.restrict_apply hA, Measure.restrict_apply hA, ← hΛeq A]
    have e1 : (A ∩ closure Λ) ∩ Λ = A ∩ Λ := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, subset_closure h.2⟩, h.2⟩⟩
    have e2 : (A ∩ closure Λ) \ Λ = A ∩ frontier Λ := by
      rw [hΛ.frontier_eq]
      ext x
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    have h3 : σ (A \ closure Λ) = 0 := measure_mono_null (fun x hx => hx.2) hσcl
    rw [← measure_inter_add_sdiff A isClosed_closure.measurableSet (μ := σ), h3, add_zero,
      ← measure_inter_add_sdiff (A ∩ closure Λ) hΛ.measurableSet (μ := σ), e1, e2]
  refine ⟨σ, hσμ, hwLE.1.sub ((hG.1.smul (-t)).add hq.1), fun φ hφ => ?_⟩
  obtain ⟨hσi, hσS⟩ := hσφ φ hφ
  refine ⟨hdecomp ▸ hσi, (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).smul_measure
    ENNReal.ofReal_ne_top, ?_⟩
  rw [hvΔ φ hφ, ← hdecomp, hσS, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ht, smul_eq_mul]

end HarmonicBalls
