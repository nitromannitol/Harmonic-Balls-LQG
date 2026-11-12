import HarmonicBalls.FirstPass.S11s.Transfer
import HarmonicBalls.FirstPass.S11s.Covariance
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.FirstPass.S11v.DilOpCoord
import HarmonicBalls.FirstPass.S11v.Decoders
import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11af
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived

/-!
# Step 8 of Lemma 11.13: the certificate frequency at the origin at insertion `γ`

Let `E` be a coding event on the field modulo constants in `B_7(0)` that agrees almost surely with the certificate
event at radius `1` about `0`, in every whole-plane model of the insertion-`γ` field `h^γ = h^ℂ - γ log|·|` with its LQG
measure and any LQG metric (the almost sure equivalence of the Lemma 11.12 construction,
`pinchLocalCertificate_canonical_of_inputs`, `S11i/Step8CalibrationCanonical.lean`). Then in every such model, almost
surely, the frequency of the radii `2^{-n}`, `n ∈ [N+1, 2N]`, at which the certificate event about `0` occurs tends to
`P[h^γ|_{B_7} ∈ E]` (paper, Lemma 11.13, Step 8, the frequency of eq. (16) at the root).

Route. The half-scale pullback of an insertion-`γ` model is again an insertion-`γ` model (`isWholePlaneGFF_affinePullback`,
`ae_isLQGMeasureOfField_affinePullback`, `ae_isLQGMetricOfField_affinePullback`), its canonical field is coordinatewise
almost surely the dilation `dilOp` of the canonical field (`ae_dilOp_alphaCanon_apply_eq`), and its certificate at radius
`r` about `0` is the certificate of the model at radius `r/2` (`certificateEvent_dilate_iff`). By induction on `n`, the
certificate at radius `2^{-n}` is almost surely the event `dilOp^[n] (alphaCanon γ hC ω) ∈ S`, with `S` the preimage of `E`
under the restriction to `B_7(0)`. Birkhoff's theorem for the ergodic dilation (`ae_alpha_canonical_window_frequency`)
gives the frequency. No uniqueness of the LQG metric is used: the equivalence with `E` holds for every metric.
-/

namespace HarmonicBalls.FirstPassPhase2Step8OriginFrequency

open MeasureTheory Filter Topology Set Metric

/-- Restriction of a canonical field (pairings with the mean-zero test functions on `ℂ`) to the mean-zero test
functions supported in `U`. -/
def canonRestrict (U : Set ℂ) (L : ModConstTestPairings (univ : Set ℂ)) : ModConstTestPairings U :=
  fun φ => L ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩

theorem measurable_canonRestrict (U : Set ℂ) : Measurable (canonRestrict U) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The restriction of the canonical field of `h^α` is the field of `h^α` modulo constants in `U`. -/
theorem canonRestrict_alphaCanon {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (ω : Ω) :
    canonRestrict U (alphaCanon α hC ω) = localModConstField α hC U ω :=
  rfl

/-- **Certificate at radius `2^{-n}` as a dilation event.** If the canonical field of `h^γ` lies in `S` exactly when the
certificate event at radius `1` about `0` occurs, almost surely in every insertion-`γ` model, then for every `n`, almost
surely in every insertion-`γ` model, `dilOp^[n]` of the canonical field lies in `S` exactly when the certificate event at
radius `2^{-n}` about `0` occurs. -/
theorem ae_iterate_mem_iff_certificate {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {S : Set (ModConstTestPairings (univ : Set ℂ))} (hS : MeasurableSet S)
    (h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (alphaCanon γ hC ω ∈ S ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0)) (n : ℕ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (dilOp^[n] (alphaCanon γ hC ω) ∈ S ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0) := by
  induction n with
  | zero =>
    intro Ω _ P hC hcirc μ D hG hμ hD
    simpa using h0 Ω P hC hcirc μ D hG hμ hD
  | succ n ih =>
    intro Ω _ P hC hcirc μ D hG hμ hD
    have hG' := isWholePlaneGFF_affinePullback hG (wholePlaneGFFAffineInvariance_derived P hC hcirc)
    have hμ' := ae_isLQGMeasureOfField_affinePullback P hγ hG hμ
    have hD' := ae_isLQGMetricOfField_affinePullback P hG hD
    have hih := ih Ω P _ _ _ _ hG' hμ' hD'
    have hco := coordAe_mem_iff (P := P) (X := fun ω => dilOp (alphaCanon γ hC ω))
      (Y := fun ω => alphaCanon γ (fun ω' => normDilatePairing (hC ω') (hcirc ω' (1 / 2) 0) (1 / 2)) ω)
      (fun i => ae_dilOp_alphaCanon_apply_eq hG γ (fun ω => hcirc ω (1 / 2) 0) i)
      ((measurable_dilOp.iterate n) hS)
    have hr : (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n + 1) := by
      rw [pow_succ]
      ring
    filter_upwards [hih, hco] with ω h1 h2
    rw [Function.iterate_succ_apply]
    refine (h2.trans h1).trans ((FirstPassS11iCertDilate.certificateEvent_dilate_iff (μ ω) (D ω) Ostar U V W T Q' Q
      η M ((2 : ℝ)⁻¹ ^ n) 0 (by norm_num : (0 : ℝ) < 1 / 2) (Real.exp_pos _) (Real.exp_pos _)).trans ?_)
    rw [mul_zero, hr]

/-- **Certificate frequency at the origin at insertion `γ` (Lemma 11.13, Step 8).** Let `E` be a measurable coding
event that agrees almost surely with the certificate event at radius `1` about `0` in every insertion-`γ` model, for
every LQG metric. Then in every insertion-`γ` model, almost surely, the window frequency of the certificate events at
the radii `2^{-n}` about `0` tends to the probability of `E`. -/
theorem ae_tendsto_certificate_origin_frequency {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ γ hC D) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℕ) : ℝ)
        / (N : ℝ)) atTop (𝓝 (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal) := by
  classical
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  set S : Set (ModConstTestPairings (univ : Set ℂ)) := canonRestrict (ball (0 : ℂ) 7) ⁻¹' E with hSdef
  have hS : MeasurableSet S := measurable_canonRestrict _ hE
  have hall := ae_iterate_mem_iff_certificate (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T) (Q' := Q')
    (Q := Q) (η := η) (M := M) hγ hS (fun Ω _ P hC hcirc μ D hG hμ hD => hEq Ω P hC hcirc μ D hG hμ hD)
  have hn := ae_all_iff.2 fun n => hall n Ω P hC hcirc μ D hG hμ hD
  have hfreq := ae_alpha_canonical_window_frequency hG birkhoffPointwiseErgodic_derived γ hS
  have hset : {ω | alphaCanon γ hC ω ∈ S} = {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} := rfl
  rw [hset] at hfreq
  filter_upwards [hfreq, hn] with ω hω hnω
  refine hω.congr fun N => ?_
  congr 1
  have hfin : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter (fun n => dilOp^[n] (alphaCanon γ hC ω) ∈ S)) := by
    ext n
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, hnω n, and_assoc]
  rw [hfin, Set.ncard_coe_finset]
  simp only [Set.indicator_apply, Finset.sum_boole]

end HarmonicBalls.FirstPassPhase2Step8OriginFrequency
