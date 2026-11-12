import HarmonicBalls.FirstPass.Phase2.LQGMetricAxiomsUniv
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.FirstPass.S11e

/-!
# The field axioms at `α₀ = 0` from the axioms of a γ-LQG metric

For the field `h = h^ℂ` without log singularity (`α₀ = 0`), the axioms I-IV of `LQGMetricFieldAxioms`
(Fact 2.2 of the paper for `h^ℂ`) are the axioms of a γ-LQG metric (`IsLQGMetric`, Gwynne-Miller 2021,
Section 1.2) applied to `h^ℂ` itself: the Weyl scaling of `D_{h^ℂ}` by the zero function is `D_{h^ℂ}`
(`IsEuclideanLengthMetric.weylScaling_zero`), the universe of the sample space is lifted by
`IsLQGMetric.satisfiesLQGMetricAxioms_univ`, and the right-hand side of the coordinate change IV is again a
Weyl scaling by the zero function, of the metric `D_{h^ℂ}(r · + z, r · + z)`, which is a Euclidean length
metric because a homeomorphic image of a Euclidean length metric is one
(`IsEuclideanLengthMetric.comp_homeomorph`).

## Main results

* `HarmonicBalls.IsEuclideanLengthMetric.comp_homeomorph`: for a homeomorphism `e` of `ℂ`,
  `(u, v) ↦ D(e u, e v)` is a Euclidean length metric when `D` is.
* `HarmonicBalls.lqgMetricFieldAxioms_alpha_zero_univ`: `LQGMetricFieldAxioms P γ ξ 0 hC hcirc` on every
  sample space `Ω : Type u`; no input.
* `HarmonicBalls.firstPass_11_12_derivedInputsAlphaZero`: Lemma 11.12 from its geometric input alone.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

namespace FieldAxiomsAlphaZero

theorem addFunPairing_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => (0 : ℝ)) = T := by
  funext φ
  simp [addFunPairing]

theorem nonneg_apply {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

end FieldAxiomsAlphaZero

open FieldAxiomsAlphaZero

/-- The `D ∘ e`-length of a path is the `D`-length of its image under `e`. -/
theorem pathLength_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ) {z w : ℂ} (P : Path z w) :
    pathLength (fun u v => D (e u) (e v)) P = pathLength D (P.map e.continuous) :=
  rfl

/-- The internal metric of `D ∘ e` on the whole plane is the internal metric of `D` between the images. -/
theorem internalMetric_univ_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ) (z w : ℂ) :
    internalMetric (fun u v => D (e u) (e v)) univ z w = internalMetric D univ (e z) (e w) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun _ => ?_
    let P : Path z w :=
      (Q.map e.symm.continuous).cast (e.symm_apply_apply z).symm (e.symm_apply_apply w).symm
    refine iInf_le_of_le P (iInf_le_of_le (fun _ => mem_univ _) (le_of_eq ?_))
    show curveLength (fun u v => D (e u) (e v)) (fun t => e.symm (Q.extend t)) 0 1 =
      curveLength D Q.extend 0 1
    simp only [curveLength, Homeomorph.apply_symm_apply]
  · refine le_iInf fun P => le_iInf fun _ => ?_
    exact iInf_le_of_le (P.map e.continuous) (iInf_le_of_le (fun _ => mem_univ _) le_rfl)

/-- A homeomorphic image of a Euclidean length metric is a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.comp_homeomorph {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (e : ℂ ≃ₜ ℂ) : IsEuclideanLengthMetric fun u v => D (e u) (e v) where
  self_eq_zero z := hD.self_eq_zero (e z)
  eq_of_eq_zero z w h := e.injective (hD.eq_of_eq_zero _ _ h)
  symm z w := hD.symm _ _
  triangle x y z := hD.triangle _ _ _
  isOpen_iff U := by
    rw [← e.symm.isOpen_preimage, hD.isOpen_iff]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, h'⟩ := h (e z) (by simpa using hz)
      exact ⟨ε, hε, fun w hw => by simpa using h' (e w) hw⟩
    · intro h z' hz'
      obtain ⟨ε, hε, h'⟩ := h (e.symm z') hz'
      exact ⟨ε, hε, fun w' hw' => h' (e.symm w') (by simpa using hw')⟩
  ofReal_eq_internalMetric z w := by
    rw [internalMetric_univ_comp_homeomorph, hD.ofReal_eq_internalMetric]

/-- The affine homeomorphism `u ↦ r u + z` of `ℂ`, `r > 0`. -/
noncomputable def affineHomeomorph (r : ℝ) (hr : 0 < r) (z : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')).trans (Homeomorph.addRight z)

theorem affineHomeomorph_apply (r : ℝ) (hr : 0 < r) (z u : ℂ) :
    affineHomeomorph r hr z u = r * u + z :=
  rfl

/-- The field axioms I-IV of Fact 2.2 at `α₀ = 0`, i.e. for the whole-plane GFF `h^ℂ` itself, on a sample space of
any universe: they are the axioms of the γ-LQG metric `𝔇` (`IsLQGMetric`) at the field `h^ℂ`. -/
theorem lqgMetricFieldAxioms_alpha_zero_univ :
    ∀ (γ ξ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ 0 hC hcirc := by
  intro γ ξ Ω _ P hC hcirc hG _ _ _ 𝔇 h𝔇
  have hS : SatisfiesLQGMetricAxioms P γ ξ 𝔇 hC := by
    have h0 := h𝔇.satisfiesLQGMetricAxioms_univ Ω P hC hcirc (fun _ _ => 0) hG
      (fun _ => continuous_const) (fun _ => measurable_const)
    convert h0 using 1
    funext ω
    exact (addFunPairing_zero (hC ω)).symm
  have hfun : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = 0 := by
    funext x
    simp
  intro Dh
  have hE : ∀ ω, IsEuclideanLengthMetric (𝔇 (hC ω)) → ∀ u v,
      Dh ω u v = ENNReal.ofReal (𝔇 (hC ω) u v) := by
    intro ω hL u v
    show weylScaling (𝔇 (hC ω)) ξ (fun x => -0 * Real.log ‖x‖) u v = _
    rw [hfun]
    exact hL.weylScaling_zero ξ u v
  have hT : ∀ ω, IsEuclideanLengthMetric (𝔇 (hC ω)) →
      (fun u v => (Dh ω u v).toReal) = 𝔇 (hC ω) := by
    intro ω hL
    funext u v
    rw [hE ω hL u v, ENNReal.toReal_ofReal (nonneg_apply hL u v)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hS.ae_isEuclideanLengthMetric] with ω hL
    refine ⟨fun u v => ?_, ?_⟩
    · rw [hE ω hL u v]
      exact ENNReal.ofReal_lt_top
    · rw [hT ω hL]
      exact hL
  · intro U hU
    obtain ⟨G, hGm, hGae⟩ := hS.locality U hU
    refine ⟨G, fun z w => ?_, ?_⟩
    · have hσ : fieldSigmaAlgebra 0 hC U = pairingSigmaAlgebra hC U := by
        rw [fieldSigmaAlgebra_eq_pairingSigmaAlgebra]
        congr 1
        funext ω φ
        simp [fieldPairing]
      rw [hσ]
      exact hGm z w
    · filter_upwards [hS.ae_isEuclideanLengthMetric, hGae] with ω hL hG'
      intro z hz w hw
      rw [hT ω hL]
      exact hG' z hz w hw
  · filter_upwards [hS.ae_isEuclideanLengthMetric] with ω hL
    intro f _ u v
    rw [hT ω hL]
    congr 1
    funext x
    simp
  · intro r hr z
    filter_upwards [hS.ae_isEuclideanLengthMetric, hS.coordChange r hr z] with ω hL hIV
    intro u v
    have hL' : IsEuclideanLengthMetric
        (𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r)) := by
      have heq : 𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r) =
          fun u v => 𝔇 (hC ω) (affineHomeomorph r hr z u) (affineHomeomorph r hr z v) := by
        funext u v
        exact (hIV u v).symm
      rw [heq]
      exact hL.comp_homeomorph _
    have hfun' : (fun x : ℂ => -(0 : ℝ) * Real.log ‖(r : ℂ) * x + z‖) = 0 := by
      funext x
      simp
    rw [hE ω hL, hIV u v, hfun', hL'.weylScaling_zero]

/-- Lemma 11.12 (`PinchEventPositiveProbabilityStmt`) from its geometric input `PinchThirdEventPositiveStmt`
alone: the field axioms at `α₀ = 0` bound by `firstPass_11_12` are `lqgMetricFieldAxioms_alpha_zero_univ`. -/
theorem firstPass_11_12_derivedInputsAlphaZero (h : PinchThirdEventPositiveStmt.{u}) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12 lqgMetricFieldAxioms_alpha_zero_univ h

end HarmonicBalls
