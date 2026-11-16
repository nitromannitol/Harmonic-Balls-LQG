import HarmonicBalls.Proofs.GFF.LQGMeasureLocalWeylScaling

/-!
# Local Weyl scaling for a random function almost surely continuous on an open set

Let `U ⊆ ℂ` be open and let `F` be a random function such that `ω ↦ F ω z` is measurable for every
`z ∈ U` and, almost surely, `F ω` is continuous on `U`. Nothing is assumed about `F ω` on the
exceptional null set, and the event that `F ω` is continuous on `U` is not assumed measurable.

For the LQG measure `μ_h` of a whole-plane field, the local reweighted random measure
`((μ_h)|_U).withDensity (e^{γ F})` is almost everywhere measurable, and almost surely the
circle-average approximations of `h + F`, tested against every continuous compactly supported `φ`
with `tsupport φ ⊆ U`, converge to its integral at all positive radii.

For measurability, `F` is replaced by `0` on a measurable null set containing every sample at
which `F ω` is not continuous on `U`. The modified function is continuous on `U` at every sample
and still measurable in the sample point at every `z ∈ U`, so the measurability statement for
functions continuous at every sample applies to it, and the two local reweighted measures agree
almost surely. The convergence holds on the intersection of the almost sure event of local Weyl
scaling with the almost sure event that `F ω` is continuous on `U`.
-/

open MeasureTheory Filter Topology Set

namespace HarmonicBalls

/-- Let `m` be an almost everywhere measurable random measure on `ℂ`, let `U` be open, and let `G`
be a random function with `ω ↦ G ω z` measurable for every `z ∈ U` and with `G ω` continuous on
`U` almost surely. Then the random measure `ω ↦ ((m ω)|_U).withDensity (G ω)` is almost
everywhere measurable. -/
theorem aemeasurable_restrict_withDensity_ofReal_of_ae_continuousOn {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {m : Ω → Measure ℂ} (hm : AEMeasurable m P)
    {U : Set ℂ} (hU : IsOpen U) {G : Ω → ℂ → ℝ} (hGc : ∀ᵐ ω ∂P, ContinuousOn (G ω) U)
    (hGm : ∀ z ∈ U, Measurable fun ω => G ω z) :
    AEMeasurable (fun ω => ((m ω).restrict U).withDensity fun z =>
      ENNReal.ofReal (G ω z)) P := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hGc)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
  let G' : Ω → ℂ → ℝ := fun ω z => if ω ∈ N then 0 else G ω z
  have hG'c : ∀ ω, ContinuousOn (G' ω) U := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [G', hω, ↓reduceIte]
      exact continuousOn_const
    · simp only [G', hω, ↓reduceIte]
      by_contra hc
      exact hω (hNsub hc)
  have hG'm : ∀ z ∈ U, Measurable fun ω => G' ω z := fun z hz =>
    Measurable.ite hNm measurable_const (hGm z hz)
  refine ⟨fun ω => ((hm.mk m ω).restrict U).withDensity fun z => ENNReal.ofReal (G' ω z),
    measurable_restrict_withDensity_ofReal_of_continuousOn hm.measurable_mk hU hG'c hG'm, ?_⟩
  filter_upwards [hm.ae_eq_mk, hNae] with ω hmω hω
  simp only [G', hω, ↓reduceIte, hmω]

/-- For the LQG measure `μ_h` of a whole-plane field, an open set `U` and a random function `F` with
`ω ↦ F ω z` measurable for every `z ∈ U` and `F ω` continuous on `U` almost surely, the local
reweighted random measure `((μ_h)|_U).withDensity (e^{γ F})` is almost everywhere measurable. No
measurability of `μ` is assumed. -/
theorem IsWholePlaneGFF.aemeasurable_restrict_withDensity_exp_lqgMeasure_of_ae_continuousOn
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) {U : Set ℂ} (hU : IsOpen U)
    {F : Ω → ℂ → ℝ} (hFc : ∀ᵐ ω ∂P, ContinuousOn (F ω) U)
    (hFm : ∀ z ∈ U, Measurable fun ω => F ω z) :
    AEMeasurable (fun ω => ((μ ω).restrict U).withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * F ω z))) P :=
  aemeasurable_restrict_withDensity_ofReal_of_ae_continuousOn (hh.aemeasurable_lqgMeasure hμ) hU
    (hFc.mono fun _ hω => Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hω))
    fun z hz => (measurable_const.mul (hFm z hz)).exp

/-- **Local Weyl scaling for a random shift almost surely continuous on an open set.** For a
whole-plane field `h = h^ℂ - α log |·|` with `0 < γ < 2` and `α < Q`, its LQG measure `μ_h`, an open
set `U` and a random function `F` with `F ω` continuous on `U` almost surely, almost surely the
circle-average approximations of `h + F`, tested against every continuous compactly supported `φ`
with `tsupport φ ⊆ U`, converge at all positive radii to the integral of `φ` against the local
reweighted measure `((μ_h)|_U).withDensity (e^{γ F})`. -/
theorem ae_tendsto_integral_lqgApprox_local_add_ae_continuousOn
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {U : Set ℂ} (hU : IsOpen U) {F : Ω → ℂ → ℝ} (hFc : ∀ᵐ ω ∂P, ContinuousOn (F ω) U) :
    ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Tendsto (fun s : ℝ =>
          ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) (F ω)) s))
        (𝓝[>] 0)
        (𝓝 (∫ z, φ z ∂(((μ ω).restrict U).withDensity fun z =>
          ENNReal.ofReal (Real.exp (γ * F ω z))))) := by
  filter_upwards [ae_tendsto_integral_lqgApprox_local_add_continuousOn hh hγ0 hγ2 hαQ hμ, hFc]
    with ω hω hc
  exact hω U hU (F ω) hc

/-- **Local Weyl scaling and measurability for a random shift almost surely continuous on an open
set.** Let `h = h^ℂ - α log |·|` be a whole-plane field with `0 < γ < 2` and `α < Q`, let `μ` be its
LQG measure, let `U` be open, and let `F` be a random function with `ω ↦ F ω z` measurable for every
`z ∈ U` and `F ω` continuous on `U` almost surely. Then the local reweighted random measure
`((μ_h)|_U).withDensity (e^{γ F})` is almost everywhere measurable, and almost surely the
circle-average approximations of `h + F`, tested against every continuous compactly supported `φ`
with `tsupport φ ⊆ U`, converge to its integral at all positive radii. -/
theorem aemeasurable_and_ae_tendsto_integral_lqgApprox_local_add_ae_continuousOn
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {U : Set ℂ} (hU : IsOpen U) {F : Ω → ℂ → ℝ} (hFc : ∀ᵐ ω ∂P, ContinuousOn (F ω) U)
    (hFm : ∀ z ∈ U, Measurable fun ω => F ω z) :
    AEMeasurable (fun ω => ((μ ω).restrict U).withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * F ω z))) P ∧
      ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun s : ℝ =>
            ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) (F ω)) s))
          (𝓝[>] 0)
          (𝓝 (∫ z, φ z ∂(((μ ω).restrict U).withDensity fun z =>
            ENNReal.ofReal (Real.exp (γ * F ω z))))) :=
  ⟨hh.aemeasurable_restrict_withDensity_exp_lqgMeasure_of_ae_continuousOn hμ hU hFc hFm,
    ae_tendsto_integral_lqgApprox_local_add_ae_continuousOn hh hγ0 hγ2 hαQ hμ hU hFc⟩

end HarmonicBalls
