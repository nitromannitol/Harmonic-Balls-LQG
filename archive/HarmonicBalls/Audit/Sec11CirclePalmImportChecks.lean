import HarmonicBalls
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.CirclePotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepMDMS
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderGFFIdentification

/-! # Combined-import check: StepM export, named decoder identification, circle potentials

Task `sec11-circle-palm-helper-import-integration`. This file imports together `HarmonicBalls`, the Section 8 circle
potential (also reached through `PalmStepMDMS` and `PalmDMSConstant`), the Section 11 circle potential, the StepM export
`stepM_of_dms` (`PalmStepMDMS`) and the named decoder identification `circleCompatDecoder_gff_identification`
(`CircleDecoderGFFIdentification`). Each typed theorem below restates the public type of one of these declarations
verbatim and is proved by that declaration, so the combined environment is checked against the stated types. No
hypothesis is added or removed: the StepM export stays conditional on the DMS input `DMSLemmaA10WholePlaneUnnormalized`
(a staged Proposed input, pending operator source-check), and the decoder identification keeps its hypotheses
`IsLiteralMollifier rho`, `Countable I`, `DenseRange q` and `IsWholePlaneGFF`. No numbered result is claimed.

Credit. The import closure of this file contains Leonardo Bonanno's Lattice-Probability formalization: 12
`LatticeProb` modules, among them `LatticeProb.Prob.Birkhoff`, reached through `HarmonicBalls.Proofs.Sec8.CircleLogPotential`.
It is used exclusively through the pinned Lattice-Probability port, `nitromannitol/Lattice-Probability` at revision
`3912597a70dcc6c9b73042abd884a26989341c8d` (`lake-manifest.json`). This file contains no Lattice-Probability code. -/

open MeasureTheory Filter Topology

namespace HarmonicBalls.Audit.Sec11CirclePalm

/-- Typed reference to the Section 8 circle potential (`Proofs/Sec8/CircleLogPotential.lean`): the centre and the point
are the explicit arguments `(z x)`. -/
theorem circleAverage_log_norm_sub_eq_log_max_sec8 {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z r =
      Real.log (max r ‖z - x‖) :=
  HarmonicBalls.circleAverage_log_norm_sub_eq_log_max hr z x

/-- Typed reference to the Section 11 circle potential (`Proofs/Sec11/ClosureScales/CirclePotential.lean`): the centre
and the point are the implicit arguments `{c a}`. -/
theorem circleAverage_log_norm_sub_eq_log_max_sec11 {c a : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y - a‖) c r = Real.log (max r ‖a - c‖) :=
  HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max hr

/-- Typed reference to the StepM export `stepM_of_dms` (`Proofs/Sec11/ClosureScales/PalmStepMDMS.lean`), conditional on
the DMS input `hU`. -/
theorem stepM_of_dms_typed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ) :
    StepM P γ hC hcirc μ :=
  HarmonicBalls.stepM_of_dms hU

/-- Typed reference to the named decoder identification (`Proofs/Sec11/ClosureScales/CircleDecoderGFFIdentification.lean`),
statement copied verbatim from that file. -/
theorem circleCompatDecoder_gff_identification_typed (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    [Countable I] (q : I → CircleDomain) (hq : DenseRange q) :
    (∀ (i : I) (n : ℕ), 0 < countableCircleScale hρ q i n) ∧
    (∀ i : I, StrictAnti (countableCircleScale hρ q i)) ∧
    (∀ i : I, Tendsto (countableCircleScale hρ q i) atTop (𝓝[>] 0)) ∧
    (∀ (u : ℂ → ℝ) (hu : Continuous u) (i : I) (n : ℕ),
      Integrable (fun v : ℂ => u v * circleCompatPsi rho q (countableCircleScale hρ q) i n v)) ∧
    (∀ (γ : ℝ) (z : ℂ) (i : I) (n : ℕ),
      Integrable (fun v : ℂ => dmsShift γ z v * circleCompatPsi rho q (countableCircleScale hρ q) i n v)) ∧
    @Measurable ((ℂ → ℝ) → ℝ) (C(CircleDomain, ℝ)) pairingMeasSpace _
      (circleCompatDecoder rho q (countableCircleScale hρ q)) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ},
      IsWholePlaneGFF P hC hcirc →
      Measurable (fun ω => circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω)) ∧
      ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S,
        (∀ p : CircleDomain,
          circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω) p = hcirc ω p.val.1 p.val.2) ∧
        (∀ (u : ℂ → ℝ) (hu : Continuous u),
          circleCompatDecoder rho q (countableCircleScale hρ q) (fun φ => hC ω φ + ∫ v : ℂ, u v * φ v) =
            circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω) + circleAverageFun u hu) ∧
        (∀ (γ : ℝ) (z : ℂ),
          circleCompatDecoder rho q (countableCircleScale hρ q)
              (fun φ => hC ω φ + ∫ v : ℂ, dmsShift γ z v * φ v) =
            circleDMSShiftFun γ z (circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω))) ∧
        (∀ (γ : ℝ) (z : ℂ), ‖z‖ ≤ 1 →
          circleCompatDecoder rho q (countableCircleScale hρ q)
              (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) =
            circleDMSShiftFun γ z (circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω))) :=
  HarmonicBalls.circleCompatDecoder_gff_identification rho hρ q hq

end HarmonicBalls.Audit.Sec11CirclePalm
