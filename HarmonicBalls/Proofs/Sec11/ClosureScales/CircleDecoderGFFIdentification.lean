import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec11.ClosureScales.CountableMollifiedCircleConvergence
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderAdditionCompatibility
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmPairingMeasurable

/-!
# Identification of the named circle-limit decoder on a whole-plane GFF

On the preceding conull event the
named decoder returns the circle averages on every circle of `CircleDomain`, and it is compatible with every continuous
addition and with every DMS insertion `dmsShift γ z`.

Setting, fixed before any probability space: a literal mollifier `rho` (`IsLiteralMollifier rho`), a countable index
type `I` and a dense family `q : I → CircleDomain`. The scales are `countableCircleScale hρ q` and the decoder is
`circleCompatDecoder rho q (countableCircleScale hρ q)`.

Imports. `PalmDMSConstant` is not imported, to keep this import closure light. The Section 11 helper is
`HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max`, not the Section 8 declaration
`HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (`Proofs/Sec8/CircleLogPotential.lean`), so the two names do not
clash. Its unit-circle lemma is repeated privately
below (`circleAverage_dmsShift_unit_sec11`) against the `CirclePotential` version. The import closure contains no
`LatticeProb` module, so no Lattice-Probability credit is consumed here. The definitions `dmsShift`, `dmsConstant` and
`dmsShiftedPairing` of `Proposed.DuplantierMillerSheffield` are used as definitions only.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- The unit-circle average of the DMS shift vanishes for `‖z‖ ≤ 1`. This is `PalmDMSConstant.circleAverage_dmsShift_unit`
with the argument order of `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max`; it is private so
that this file need not import `PalmDMSConstant`. -/
private theorem circleAverage_dmsShift_unit_sec11 (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.circleAverage (dmsShift γ z) 0 1 = 0 := by
  have h1 : Real.circleAverage (dmsShift γ z) 0 1 =
      Real.circleAverage (fun x => (-γ) • Real.log ‖x - z‖) 0 1 := by
    refine Real.circleAverage_congr_sphere ?_
    intro x hx
    have hx1 : ‖x‖ = 1 := by
      have h := Metric.mem_sphere.1 hx
      rw [dist_zero_right, abs_one] at h
      exact h
    simp only [dmsShift, hx1, max_self, Real.log_one, mul_zero, add_zero, smul_eq_mul]
  have h2 : Real.circleAverage (fun x => (-γ) • Real.log ‖x - z‖) 0 1 =
      (-γ) • Real.circleAverage (fun x => Real.log ‖x - z‖) 0 1 :=
    Real.circleAverage_fun_smul
  have hmax : max (1 : ℝ) ‖z - 0‖ = 1 := by
    rw [sub_zero]
    exact max_eq_left hz
  rw [h1, h2, HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max one_pos, hmax,
    Real.log_one, smul_zero]

/-- **Identification of the named decoder on a whole-plane GFF**.

Let `rho` be a literal mollifier, `I` a countable index type, `q : I → CircleDomain` dense, and
`D = circleCompatDecoder rho q (countableCircleScale hρ q)`. Deterministically, the scales are positive, strictly
antitone and tend to `0` from the right, and the decoder test functions are integrable against every continuous `u`
and against every `dmsShift γ z`. For every whole-plane GFF `(P, hC, hcirc)`, the map `ω ↦ D (hC ω)` is measurable,
and there is one measurable set `S` with `P Sᶜ = 0` such that, for every `ω ∈ S`:
(1) `D (hC ω) p = hcirc ω p.1 p.2` for every `p : CircleDomain` (the raw circle field, on its domain `CircleDomain` only);
(2) for every continuous `u`, `D (hC ω + ∫ u φ) = D (hC ω) + circleAverageFun u hu`;
(3) for every `γ` and `z`, `D (hC ω + ∫ dmsShift γ z φ) = circleDMSShiftFun γ z (D (hC ω))`;
(4) for every `γ` and every `z` with `‖z‖ ≤ 1`, `D (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = circleDMSShiftFun γ z (D (hC ω))`. -/
theorem circleCompatDecoder_gff_identification (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
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
            circleDMSShiftFun γ z (circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω))) := by
  have hpos : ∀ (i : I) (n : ℕ), 0 < countableCircleScale hρ q i n :=
    fun i n => countableCircleScale_pos hρ q i n
  have hDspec := circleCompatDecoder_spec rho hρ q hq (countableCircleScale hρ q) hpos
  refine ⟨(countableCircleScale_spec hρ q).1, (countableCircleScale_spec hρ q).2.1,
    (countableCircleScale_spec hρ q).2.2,
    fun u hu i n => integrable_circleCompat_mul rho hρ q (countableCircleScale hρ q) hpos hu i n,
    fun γ z i n => integrable_circleCompat_dms rho hρ q (countableCircleScale hρ q) hpos γ z i n,
    hDspec.1, ?_⟩
  intro Ω _ P hC hcirc hgff
  have hCm : @Measurable Ω ((ℂ → ℝ) → ℝ) _ pairingMeasSpace hC :=
    measurable_pairing_of_eval hC hgff.measurable_pairing
  refine ⟨hDspec.1.comp hCm, ?_⟩
  obtain ⟨-, S₀, hmeasS₀, hnullS₀, hconv⟩ := countableCircleScale_ae_convergence hρ q hgff
  obtain ⟨t₁, hsub₁, hmeas₁, hnull₁⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hgff.ae_continuousOn_circle)
  obtain ⟨t₂, hsub₂, hmeas₂, hnull₂⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hgff.ae_circleAverage_one_zero)
  refine ⟨S₀ ∩ t₁ᶜ ∩ t₂ᶜ, (hmeasS₀.inter hmeas₁.compl).inter hmeas₂.compl, ?_, ?_⟩
  · simp only [Set.compl_inter, compl_compl]
    exact measure_union_null (measure_union_null hnullS₀ hnull₁) hnull₂
  · rintro ω ⟨⟨hω₀, hω₁⟩, hω₂⟩
    have hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
      by_contra hn
      exact hω₁ (hsub₁ hn)
    have h10 : hcirc ω 1 0 = 0 := by
      by_contra hn
      exact hω₂ (hsub₂ hn)
    obtain ⟨F, hF⟩ : ∃ F : C(CircleDomain, ℝ), ∀ p : CircleDomain, F p = hcirc ω p.val.1 p.val.2 :=
      ⟨⟨fun p => hcirc ω p.val.1 p.val.2,
        hcont.comp_continuous continuous_subtype_val
          fun p => Set.mk_mem_prod (Set.mem_Ioi.2 p.2) (Set.mem_univ _)⟩, fun p => rfl⟩
    have hT : ∀ i, Tendsto (fun n => hC ω (circleCompatPsi rho q (countableCircleScale hρ q) i n))
        atTop (𝓝 (F (q i))) := fun i => by
      rw [hF]
      exact hconv ω hω₀ i
    have hDF : circleCompatDecoder rho q (countableCircleScale hρ q) (hC ω) = F :=
      circleCompatDecoder_valid rho hq (countableCircleScale hρ q) hT
    obtain ⟨-, hadd, hdms⟩ := circleCompat_addition rho hρ q hq (countableCircleScale hρ q) hpos
      (countableCircleScale_spec hρ q).2.2 (hC ω) F hT
    refine ⟨fun p => ?_, fun u hu => ?_, fun γ z => ?_, fun γ z hz => ?_⟩
    · rw [hDF, hF]
    · rw [hDF]
      exact (hadd u hu).2
    · rw [hDF]
      exact (hdms γ z).2
    · have hc : dmsConstant γ z (hcirc ω 1 0) = 0 := by
        simp [dmsConstant, h10, circleAverage_dmsShift_unit_sec11 γ hz]
      have hpair : dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) =
          fun φ => hC ω φ + ∫ v : ℂ, dmsShift γ z v * φ v := by
        funext φ
        simp only [dmsShiftedPairing, hc, zero_mul, add_zero]
      rw [hpair, hDF]
      exact (hdms γ z).2

end HarmonicBalls
