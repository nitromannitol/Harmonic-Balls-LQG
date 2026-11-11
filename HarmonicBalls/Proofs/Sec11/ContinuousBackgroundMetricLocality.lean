import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Proofs.Sec11.MeasurableCenteredBaseLocality

/-! # Normalized metric locality after a continuous background shift

The Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A continuous deterministic background preserves countable local
observability of the normalized LQG metric modulo field constants. -/
theorem IsWholePlaneGFF.exists_modConst_countable_internal_backgroundMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (f : ℂ → ℝ) (hf : Continuous f)
    {U : Set ℂ} (hU : IsOpen U) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U ∧ (p n).2 ∈ U) :
    ∃ (G : Ω → ℕ → ℝ≥0∞),
      Measurable[Section6.fieldSigmaAlgebraModConst α hC U] G ∧
      (∀ᵐ ω ∂P, ∀ n, internalMetric
        (fun x y => Real.exp (ξ * (-hC ω ψ)) * 𝔇 (addFunPairing (hC ω) f) x y)
        U (p n).1 (p n).2 = G ω n) := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have ha := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω z => f z + c ω) h
    (fun _ => hf.add continuous_const) (fun _ => measurable_const.add hc)
  obtain ⟨G, hG, hGeq⟩ := ha.locality U hU
  have hGmeas : Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U]
      (fun ω n => G ω (p n).1 (p n).2) := by
    change Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U] _
    rw [← fieldSigmaAlgebra_background_add_random_constant α hC U f hf c]
    rw [fieldSigmaAlgebra_eq, fieldSigmaAlgebra_eq_pairingSigmaAlgebra]
    have heq : (fun ω => fieldPairing 0
        (addFunPairing (hC ω) (fun z => f z + c ω))) =
        (fun ω => addFunPairing (hC ω) (fun z => f z + c ω)) := by
      funext ω φ
      simp [fieldPairing]
    rw [heq]
    let : MeasurableSpace Ω := pairingSigmaAlgebra
      (fun ω => addFunPairing (hC ω) (fun z => f z + c ω)) U
    exact measurable_pi_iff.mpr (fun n => hG (p n).1 (p n).2)
  obtain ⟨H, hH, hHeq⟩ := h.exists_modConst_observable_of_reference_shift ψ hψ hψint
    (fun ω n => G ω (p n).1 (p n).2) hGmeas
  have hs := h.ae_metric_background_add_random_constant 𝔇 h𝔇 f hf c hc
  refine ⟨H, hH, ?_⟩
  filter_upwards [hs, hGeq, hHeq] with ω hs hg hh n
  have heq : 𝔇 (addFunPairing (hC ω) (fun z => f z + c ω)) =
      fun u v => Real.exp (ξ * c ω) * 𝔇 (addFunPairing (hC ω) f) u v := by
    funext u v
    exact hs u v
  rw [← heq, hg (p n).1 (hp n).1 (p n).2 (hp n).2]
  exact (congrFun hh n).symm

/-- After a continuous deterministic background shift, all local internal
metric distances have a simultaneous version measurable modulo constants. -/
theorem IsWholePlaneGFF.exists_modConst_internal_backgroundMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (f : ℂ → ℝ) (hf : Continuous f)
    {U : Set ℂ} (hU : IsOpen U) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * 𝔇 (addFunPairing (hC ω) f) x y) U x y = G ω x y) := by
  classical
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have hne : U.Nonempty := by
    by_contra hn
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hzero : ψ = 0 := by
      funext x
      by_contra hx
      have hmem : x ∈ U := hψ.2.2 (subset_closure hx)
      rw [hUempty] at hmem
      exact hmem
    simp [hzero] at hψint
  have hshift := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω z => f z + c ω) h
    (fun _ => hf.add continuous_const) (fun _ => measurable_const.add hc)
  have heq := h.ae_metric_background_add_random_constant 𝔇 h𝔇 f hf c hc
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => Real.exp (ξ * c ω) * 𝔇 (addFunPairing (hC ω) f) x y) := by
    filter_upwards [hshift.ae_isEuclideanLengthMetric, heq] with ω hs he
    have hf' : 𝔇 (addFunPairing (hC ω) (fun z => f z + c ω)) =
        fun x y => Real.exp (ξ * c ω) * 𝔇 (addFunPairing (hC ω) f) x y := by
      funext x y
      exact he x y
    rw [← hf']
    exact hs
  have hcount := fun (p : ℕ → ℂ × ℂ) hp =>
    h.exists_modConst_countable_internal_backgroundMetric (α := α) 𝔇 h𝔇 f hf hU ψ hψ hψint p hp
  obtain ⟨G, hG, hGeq⟩ := exists_internalMetric_version_of_countable
    (Section6.fieldSigmaAlgebraModConst α hC U) hU hne hmetric hcount
  exact ⟨fun ω => Real.exp (ξ * c ω), G,
    Filter.Eventually.of_forall (fun _ => Real.exp_pos _), hG, hGeq⟩


end HarmonicBalls
