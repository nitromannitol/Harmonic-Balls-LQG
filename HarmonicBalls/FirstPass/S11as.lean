import HarmonicBalls.FirstPass.S11aq
import HarmonicBalls.FirstPass.S11al
import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11ah.Cutoff

/-!
# Rooted covariance of the certificate event: reduction of `hCov` to a local rescaling identity (fp-S11as)

Deterministic half of the covariance clause `hCov` of n1 (`HarmonicBalls/FirstPass/S11ai/RootedInstance.lean`).
The physical rooted pair `(μR z ω, dR z ω)` at scale `2^{-n}` about `z` is compared with the canonical pair
`(μC n, dC n)` (`μC n = Dμ (dilOp^[n] L)`, `dC n = Dd (dilOp^[n] L)`) at unit scale about `0`, through the affine map
`w ↦ z + 2^{-n} w`. Three deterministic facts are used:
* translation covariance `FirstPassS11aq.certificateEvent_translate_iff` (centre `z` moved to `0`);
* locality of the certificate event in the mass (`FirstPassS11aq.certificateEvent_measure_congr`) and in the metric
  (`FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall`, which needs `CertificateContainments`), both on
  `closedBall 0 (7 r)`;
* dilation covariance `HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff`, whose mass constant `a` and
  metric constant `b` cancel in every strict inequality (Armitage–Gardiner homogeneity of the certificate).

NOT PROVED HERE (field-level input, reported as the blocker): the local rescaling identity `RootedLocalRescaling`, i.e.
that on `closedBall 0 (7 · 2^{-n})` (translated frame) the physical rooted mass and metric are positive multiples of the
rescaled decoded canonical mass and metric. Its sources are the LQG coordinate-change rules (`LQGMeasureCoordChange`,
`LQGMetricFieldAxioms` clause IV, at singularity parameter `γ`), Cameron–Martin reweighting, and locality of the LQG mass
and metric for two different fields that agree on a ball. The identity is claimed only for `cutRadius n < b`, the radius
on which the physical field `h(z + ·) - α₀ log|z + ·| - γ log|·|` agrees with the canonical field `G_u` of the admissible
shift `(b, u)`; for larger `n` the two fields differ and the identity is not supported.
-/

namespace FirstPassS11as

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls FirstPassS11i

/-- **Deterministic reduction (translation, locality, dilation).** If, in the translated frame `w ↦ w - z`, the physical
pair agrees on `closedBall 0 (7 r)` with the pair `(a • μC.map (· / R), b · dC (R ·, R ·))`, then the certificate event
of the physical pair at `(z, r)` is the certificate event of the canonical pair at `(0, R r)`. -/
theorem certificateEvent_local_rescale_iff (μR μC : Measure ℂ) (dR dC : ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M r R a b : ℝ) (z : ℂ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hr : 0 < r) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hμ : (μR.map (fun w : ℂ => w - z)).restrict (closedBall 0 (7 * r)) =
      (ENNReal.ofReal a • μC.map (fun w : ℂ => w / (R : ℂ))).restrict (closedBall 0 (7 * r)))
    (hD : EqOn (Function.uncurry (fun x y : ℂ => dR (x + z) (y + z)))
      (Function.uncurry (fun x y : ℂ => b * dC ((R : ℂ) * x) ((R : ℂ) * y)))
      (closedBall 0 (7 * r) ×ˢ closedBall 0 (7 * r))) :
    CertificateEvent μR dR Ostar U V W T Q' Q η M r z ↔
      CertificateEvent μC dC Ostar U V W T Q' Q η M (R * r) 0 := by
  have hT := FirstPassS11aq.certificateEvent_translate_iff μR dR Ostar U V W T Q' Q η M r 0 z
  rw [zero_add] at hT
  refine Iff.trans hT.symm ?_
  refine Iff.trans (FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (U := U) hC hr hD) ?_
  refine Iff.trans (FirstPassS11aq.certificateEvent_measure_congr
    (fun x y : ℂ => b * dC ((R : ℂ) * x) ((R : ℂ) * y)) Ostar U V W T Q' Q η M r 0 hr hU hμ) ?_
  have hdil := HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff μC dC Ostar U V W T Q' Q η M r 0
    hR ha hb
  rw [mul_zero] at hdil
  exact hdil

/-- **Local rescaling identity at root `z`, scale `2^{-n}` (field-level input; NOT PROVED in this file).**
In the translated frame, the physical mass and metric agree on `closedBall 0 (7 · certScale n)` with the rescaled
decoded canonical mass and metric, up to positive constants `a` (mass) and `b` (metric). The mass constant is the
normalising constant of the LQG coordinate-change rule; any constant is allowed because the certificate event is
homogeneous. -/
def RootedLocalRescaling (μR μC : Measure ℂ) (dR dC : ℂ → ℂ → ℝ) (z : ℂ) (n : ℕ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    (μR.map (fun w : ℂ => w - z)).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
      (ENNReal.ofReal a • μC.map (fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ))).restrict
        (closedBall 0 (7 * FirstPassS11ah.certScale n)) ∧
    EqOn (Function.uncurry (fun x y : ℂ => dR (x + z) (y + z)))
      (Function.uncurry (fun x y : ℂ =>
        b * dC ((((2 : ℝ) ^ n : ℝ) : ℂ) * x) ((((2 : ℝ) ^ n : ℝ) : ℂ) * y)))
      (closedBall 0 (7 * FirstPassS11ah.certScale n) ×ˢ closedBall 0 (7 * FirstPassS11ah.certScale n))

/-- `2^n · 2^{-n} = 1`: the dilation factor of scale `2^{-n}` is `2^n`. -/
theorem two_pow_mul_certScale (n : ℕ) : (2 : ℝ) ^ n * FirstPassS11ah.certScale n = 1 := by
  unfold FirstPassS11ah.certScale
  rw [← mul_pow]
  norm_num

/-- **hCov at one scale, from the local rescaling identity.** The physical certificate event at `(z, 2^{-n})` agrees with
the canonical certificate event at unit scale about `0`. -/
theorem certificateEvent_of_rootedLocalRescaling (μR μC : Measure ℂ) (dR dC : ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (z : ℂ) (n : ℕ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hloc : RootedLocalRescaling μR μC dR dC z n) :
    CertificateEvent μR dR Ostar U V W T Q' Q η M (FirstPassS11ah.certScale n) z ↔
      CertificateEvent μC dC Ostar U V W T Q' Q η M 1 0 := by
  obtain ⟨a, b, ha, hb, hμ, hD⟩ := hloc
  have hpos : 0 < FirstPassS11ah.certScale n := FirstPassS11ah.certScale_pos n
  have hR : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key := certificateEvent_local_rescale_iff μR μC dR dC Ostar U V W T Q' Q η M
    (FirstPassS11ah.certScale n) ((2 : ℝ) ^ n) a b z hC hU hpos hR ha hb hμ hD
  rw [two_pow_mul_certScale n] at key
  exact key

/-- The cutoff radius `cutRadius n = 7 · 2^{-n}` is eventually below any positive `b`. -/
theorem eventually_cutRadius_lt {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, FirstPassS11ah.cutRadius n < b := by
  have ht : Tendsto (fun n : ℕ => FirstPassS11ah.cutRadius n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 := h1.const_mul 7
    rw [mul_zero] at h2
    unfold FirstPassS11ah.cutRadius FirstPassS11ah.certScale
    exact h2
  exact ht.eventually (gt_mem_nhds hb)

/-- **hCov, eventual form, from the local rescaling identity.** For fixed root `z`, fixed admissible shift with radius `b`,
and the canonical pairs `μC n`, `dC n` (`μC n = Dμ (dilOp^[n] L)`, `dC n = Dd (dilOp^[n] L)`), the physical and canonical
certificate events agree for all sufficiently large `n`. This is the form `ae_termwise_of_identification` needs
(its conclusion is `∃ n₀, ∀ n ≥ n₀`); the identity is NOT claimed for every `n` in the cutoff range. -/
theorem rootedCovariance_eventually (μR : Measure ℂ) (dR : ℂ → ℂ → ℝ) (μC : ℕ → Measure ℂ)
    (dC : ℕ → ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (z : ℂ) {b : ℝ} (hb : 0 < b)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hloc : ∀ n : ℕ, FirstPassS11ah.cutRadius n < b → RootedLocalRescaling μR (μC n) dR (dC n) z n) :
    ∀ᶠ n : ℕ in atTop,
      (CertificateEvent μR dR Ostar U V W T Q' Q η M (FirstPassS11ah.certScale n) z ↔
        CertificateEvent (μC n) (dC n) Ostar U V W T Q' Q η M 1 0) := by
  filter_upwards [eventually_cutRadius_lt hb] with n hn
  exact certificateEvent_of_rootedLocalRescaling μR (μC n) dR (dC n) Ostar U V W T Q' Q η M z n hC hU (hloc n hn)

end FirstPassS11as
