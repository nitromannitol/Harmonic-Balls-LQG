import HarmonicBalls.FirstPass.Phase2.SingularMetricDecoderDerived
import HarmonicBalls.FirstPass.Phase2.AxiomsUnivDerived
import HarmonicBalls.FirstPass.LPBridge.M5a
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Phase2.EventSampleRepresentationProof

/-!
# Almost sure measurability of the internal singular LQG metric, from the field axioms

For a γ-LQG metric `𝔇`, a whole-plane GFF `h^ℂ`, a continuous `f` and an open set `W`, the internal metric on `W` of the
singular metric `E = e^{-ξ α₀ log |·|} · 𝔇(h^ℂ + f)` of `h^ℂ + f - α₀ log |·|` is almost surely a measurable functional
of the distribution `h^ℂ + f` (`LQGInternalMetricWeylAeMeasurableFrozen`). The functional is the decoder
`singularMetricDecoder`, built from the metrics of the log-cutoff fields `h^ℂ + f - α₀ log max(|·|, e^{-k})`.

The one analytic input is the truncation limit of the singular Weyl scaling: for a Euclidean length metric `D`, a
continuous `F`, and radii `r_k > 0` decreasing to `0`, the Weyl scalings by `F - α₀ log max(|·|, r_k)` converge to the
Weyl scaling by `F - α₀ log |·|` at every pair of points when the latter is continuous at `0`. Its statement is
`WeylLogTruncationStatement` below, in the library's definitions; the library proves it as
`LatticeProb.LQG.IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff`.

* `ae_tendsto_singularCutoff_of_truncation`: almost surely the cutoff metrics `𝔇(h^ℂ + f - α₀ log max(|·|, e^{-k}))`
  converge to `E` at every pair of points (axioms I and III for the field `h^ℂ + f`, and the regularity of `E` from
  `ae_weylScaling_singularShift_regular`);
* `lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation`: the frozen statement, from the field axioms of the
  singular metric (`LQGMetricFieldAxiomsUnivFrozen`) and the truncation limit;
* `cameronMartinEventTransfer_of_fieldAxioms_of_truncation`: the Cameron-Martin event transfer
  (`CameronMartinEventTransferFrozen`) from the same two inputs, through
  `CMEventTransfer.cameronMartinEventTransfer_derived` and the proved Weyl scaling composition
  `weylScalingCompositionFrozen_holds`.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Truncation limit of the singular Weyl scaling, stated in the library's definitions exactly as
`LatticeProb.LQG.IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff`. -/
abbrev WeylLogTruncationStatement : Prop :=
  ∀ (D : ℂ → ℂ → ℝ), LatticeProb.LQG.IsEuclideanLengthMetric D → ∀ (ξ α₀ : ℝ) (F : ℂ → ℝ), Continuous F →
    ∀ (r : ℕ → ℝ), (∀ k, 0 < r k) → Antitone r → Tendsto r atTop (𝓝 0) →
    Tendsto (fun x => LatticeProb.LQG.weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) x 0) (𝓝 0) (𝓝 0) →
    ∀ u v : ℂ,
      Tendsto (fun k => LatticeProb.LQG.weylScaling D ξ (fun z => F z + -α₀ * Real.log (max ‖z‖ (r k))) u v) atTop
        (𝓝 (LatticeProb.LQG.weylScaling D ξ (fun z => F z + -α₀ * Real.log ‖z‖) u v))

/-- The radii `e^{-k}` decrease to `0`. -/
theorem antitone_exp_neg_natCast : Antitone fun k : ℕ => Real.exp (-(k : ℝ)) :=
  fun _ _ hab => Real.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))

theorem tendsto_exp_neg_natCast : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- Convergence of the cutoff metrics. Under the field axioms of the singular metric and the truncation limit, almost
surely, for every pair of points `a, b`, the metrics of the cutoff fields `h^ℂ + f - α₀ log max(|·|, e^{-k})` converge
to the singular metric `E = e^{-ξ α₀ log |·|} · 𝔇(h^ℂ + f)`. Route: by axiom III for the field `h^ℂ + f`
(`lqgMetricSatisfiesAxiomsUniv_derived`), the cutoff metric is the Weyl scaling of `D = 𝔇(h^ℂ + f)` by the continuous
cutoff weight; `D` is a Euclidean length metric by axiom I, and `E(·, 0)` is continuous at `0`
(`ae_weylScaling_singularShift_regular`), so the truncation limit applies with `F = 0` and `r_k = e^{-k}`. -/
theorem ae_tendsto_singularCutoff_of_truncation (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hTr : WeylLogTruncationStatement) {γ ξ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ)
    (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {f : ℂ → ℝ}
    (hf : Continuous f) :
    ∀ᵐ ω ∂P, ∀ a b, Tendsto
      (fun k : ℕ => ENNReal.ofReal (𝔇 (addFunPairing (addFunPairing (hC ω) f) (logCutoffWeight α₀ k)) a b)) atTop
      (𝓝 (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) a b)) := by
  have hSat := lqgMetricSatisfiesAxiomsUniv_derived γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ => f) hW (fun _ => hf)
    (fun _ => measurable_const)
  filter_upwards [hSat.ae_isEuclideanLengthMetric, hSat.ae_weylScaling,
    ae_weylScaling_singularShift_regular hAx hW hγ0 hγ2 hα h𝔇 hf] with ω hI hIII hreg a b
  have hfun : (fun k : ℕ => ENNReal.ofReal (𝔇 (addFunPairing (addFunPairing (hC ω) f) (logCutoffWeight α₀ k)) a b)) =
      fun k => weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (logCutoffWeight α₀ k) a b :=
    funext fun k => hIII _ (continuous_logCutoffWeight α₀ k) a b
  rw [hfun]
  have hc : Tendsto (fun x => LatticeProb.LQG.weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ
      (fun z => (fun _ : ℂ => (0 : ℝ)) z + -α₀ * Real.log ‖z‖) x 0) (𝓝 0) (𝓝 0) := by
    simp only [zero_add]
    exact hreg.2.2
  have h := hTr _ ((LPBridge.isEuclideanLengthMetric_iff _).1 hI) ξ α₀ (fun _ => 0) continuous_const
    (fun k : ℕ => Real.exp (-(k : ℝ))) (fun _ => Real.exp_pos _) antitone_exp_neg_natCast tendsto_exp_neg_natCast hc a b
  simp only [zero_add] at h
  exact h

/-- **Derived.** Almost sure measurability of the internal metric of the singular LQG metric
(`LQGInternalMetricWeylAeMeasurableFrozen`), from the field axioms of the singular metric
(`LQGMetricFieldAxiomsUnivFrozen`) and the truncation limit of the singular Weyl scaling. The functional is
`singularMetricDecoder` with a countable dense vertex set `S` and a countable set `C ⊆ Wᶜ` dense in `Wᶜ`; it is
measurable for the σ-algebra of pairings (`measurable_singularMetricDecoder`), and almost surely it equals the internal
metric of the singular metric of `h^ℂ + f` on `W` (`singularMetricDecoder_eq`, with the convergence
`ae_tendsto_singularCutoff_of_truncation` and the regularity `ae_weylScaling_singularShift_regular`). -/
theorem lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hTr : WeylLogTruncationStatement) : LQGInternalMetricWeylAeMeasurableFrozen.{u} := by
  intro γ ξ α₀ Ω _ P _ hC hcirc 𝔇 hW hγ0 hγ2 hα h𝔇 W hWo q q'
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  obtain ⟨C, hCW, hCc, hWC⟩ := exists_countable_dense_subset_compl W
  have : Countable S := hSc.to_subtype
  refine ⟨singularMetricDecoder 𝔇 α₀ S C W q q', measurable_singularMetricDecoder h𝔇 α₀ hCc W q q',
    fun f hf => ?_⟩
  filter_upwards [ae_tendsto_singularCutoff_of_truncation hAx hTr hW hγ0 hγ2 hα h𝔇 hf,
    ae_weylScaling_singularShift_regular hAx hW hγ0 hγ2 hα h𝔇 hf] with ω hlim hreg
  exact singularMetricDecoder_eq hSd hWo hCW hWC hreg.2.1 hlim q q'

/-- **Derived.** The Cameron-Martin event transfer (`CameronMartinEventTransferFrozen`) from the field axioms of the
singular metric and the truncation limit of the singular Weyl scaling:
`CMEventTransfer.cameronMartinEventTransfer_derived` with the proved Weyl scaling composition
(`weylScalingCompositionFrozen_holds`) and the internal-metric measurability
`lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation`. -/
theorem cameronMartinEventTransfer_of_fieldAxioms_of_truncation (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hTr : WeylLogTruncationStatement) : CameronMartinEventTransferFrozen.{u} :=
  CMEventTransfer.cameronMartinEventTransfer_derived hAx weylScalingCompositionFrozen_holds
    (lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation hAx hTr)

end HarmonicBalls
