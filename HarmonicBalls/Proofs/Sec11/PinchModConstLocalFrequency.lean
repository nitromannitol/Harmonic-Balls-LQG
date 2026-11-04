import HarmonicBalls.Proofs.Sec11.PinchModConstGerm
import HarmonicBalls.Proofs.Sec11.PinchInitialScale

/-! # Local representatives and modulo-constant pinch frequency

The Section 8 Birkhoff theorem used by the imported germ bridge is due to
Leonardo Bonanno. The existence of modulo-constant event representatives is
an explicit hypothesis; full-field locality alone does not provide it.
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory Topology

open Classical in
/-- Local representatives at each dyadic scale yield bounded indicators
measurable in every sufficiently small modulo-constant field neighborhood. -/
theorem exists_modConst_germ_pinchIndicators
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hle : ∀ ε, Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε) ≤ mΩ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q V : Set ℂ) (M : ℝ)
    (hlocal : ∀ n : ℕ, ∃ A : Set Ω,
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC
        (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)))] A ∧
      ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 ↔ ω ∈ A)) :
    ∃ X : ℕ → Ω → ℝ,
      (∀ n, Measurable (X n)) ∧ (∀ n ω, X n ω ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
        U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0) ∧
      (∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
        Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] (X n)) := by
  choose A hA hAeq using hlocal
  let X : ℕ → Ω → ℝ := fun n ω => if ω ∈ A n then 1 else 0
  have hm (n : ℕ) : Measurable (X n) :=
    Measurable.ite ((hle _) _ (hA n)) measurable_const measurable_const
  have hb (n : ℕ) (ω : Ω) : X n ω ∈ Icc (0 : ℝ) 1 := by
    dsimp only [X]
    split_ifs <;> norm_num
  have heq : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0 := by
    filter_upwards [ae_all_iff.mpr hAeq] with ω hω
    intro n
    simp only [X, ← hω n]
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  refine ⟨X, hm, hb, heq, ?_⟩
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, fun n hn => ?_⟩
  have hsub : ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)) ⊆ ball 0 ε :=
    ball_subset_ball (le_of_lt (hK n hn))
  let : MeasurableSpace Ω := Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)
  exact Measurable.ite ((fieldSigmaAlgebraModConst_mono α₀ hC hsub) _ (hA n))
    measurable_const measurable_const

open Classical in
/-- A locally absolutely continuous law has the prescribed block density
when the dyadic events admit modulo-constant local representatives and their
indicator sequence is stationary. The unit-scale bound is explicit. -/
theorem ae_internal_pinchBlockDensity_of_modConst_local_representatives
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P R : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hR : IsWholePlaneGFF R hC hcirc) (α₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hAC : P.trim (hR.fieldSigmaAlgebra_le α₀ (ball 0 r)) ≪
      R.trim (hR.fieldSigmaAlgebra_le α₀ (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q V : Set ℂ) (M : ℝ)
    (hlocal : ∀ n : ℕ, ∃ A : Set Ω,
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC
        (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)))] A ∧
      ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 ↔ ω ∈ A))
    (hstat : P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q V M 1 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  obtain ⟨X, hXm, hbound, hX, hXgerm⟩ :=
    exists_modConst_germ_pinchIndicators P α₀ hC
      (fun ε => (Section6.fieldSigmaAlgebraModConst_le α₀ hC _).trans
        (hR.fieldSigmaAlgebra_le α₀ _)) μ D U T Q V M hlocal
  have hmap (k : ℕ) : P.map (fun ω n => X (n + k) ω) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + k)) 0 then (1 : ℝ) else 0) := by
    apply Measure.map_congr
    filter_upwards [hX] with ω hω
    funext n
    exact hω (n + k)
  have hsX : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω) := by
    calc
      _ = _ := hmap 1
      _ = _ := hstat
      _ = _ := by simpa only [add_zero] using (hmap 0).symm
  obtain ⟨hfirst, htail⟩ := stationary_sequence_first_law_and_tail P X hXm hsX
  have hE (n : ℕ) : P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
      ((2 : ℝ)⁻¹ ^ n) 0} = P (X n ⁻¹' ({1} : Set ℝ)) := by
    apply measure_congr
    filter_upwards [hX] with ω hω
    simp only [mem_preimage, mem_singleton_iff, hω n]
    split_ifs <;> simp_all
  have hmeas : P (X 1 ⁻¹' ({1} : Set ℝ)) = P (X 0 ⁻¹' ({1} : Set ℝ)) := by
    have hh := congrArg (fun Q : Measure ℝ => Q ({1} : Set ℝ)) hfirst
    rwa [Measure.map_apply (hXm 1) (measurableSet_singleton 1),
      Measure.map_apply (hXm 0) (measurableSet_singleton 1)] at hh
  have hδ' : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
      ((2 : ℝ)⁻¹ ^ 1) 0}).toReal := by
    rw [hE 1, hmeas, ← hE 0]
    simpa only [pow_zero] using hδ
  exact ae_internal_pinchBlockDensity_of_modConst_germ P R hR α₀ hr hAC μ D U T Q V M X
    hXm hbound hX hXgerm htail δ hδ'

#print axioms exists_modConst_germ_pinchIndicators
#print axioms ae_internal_pinchBlockDensity_of_modConst_local_representatives

end HarmonicBalls
