import HarmonicBalls.FirstPass.S11ab
import HarmonicBalls.FirstPass.S11ag
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11aj.Mixture

/-! # Shifted clause of the metric and pair event certificates (fp-S11aj)

The shifted clause `hshift` of `metric_event_transfer_of_rule` (`FirstPass/S11ab.lean`) and its pair version for
`MetricMeasureEventCertificateStmt` (`FirstPass/S11ag.lean`), for the shifted field `h^C + f` of a smooth compactly
supported `f` with zero unit-circle average. Route (Lh answer `notes/fp-gaps/CHATGPT-lh-R4-R5.md`, §R4 and its pair
follow-up): a Cameron-Martin reweighting `P'` of the GFF (named hypothesis `CameronMartinGFFReweighting`), and a two-copy
model on `Ω ⊕ Ω` with the mixture `½ P.map inl + ½ P'.map inr` (`FirstPass/S11aj/Mixture.lean`), to which the universally
quantified certificate is applied once. The frozen null-set input `CameronMartinGFFMutualAbsCont` transfers the
measurable discrepancy set from the base copy to the shifted copy.
-/

namespace HarmonicBalls.S11aj

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- Named input, not an External or Proposed Prop; a form the Cameron-Martin reweighting must supply (pending operator
staging). The Cameron-Martin theorem for the whole-plane GFF (Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2,
Proposition 2.9, printed p. 49, Gaussian tilting): for every whole-plane GFF `(P, hC, hcirc)` and every smooth compactly
supported `f` with zero unit-circle average, there is a measure `P'` equivalent to `P` under which the shifted pairings
`addFunPairing (hC ω) f` and the shifted circle averages `hcirc ω r z + Av_{∂B_r(z)} f` form a whole-plane GFF.

Why this is a named hypothesis and not a consequence of `CameronMartinGFFMutualAbsCont` (`Frozen/S11d.lean:74`): that
frozen input gives only equality of null sets for events of `distributionMeasurableSpace`, i.e. for pairings. A
Radon-Nikodym density `dP'/dP` that makes the circle averages GFF-distributed needs equivalence of the joint laws of
`(hC, hcirc)` and `(hC + f, hcirc + Av f)`, and the circle averages are not `distributionMeasurableSpace`-measurable
functions of `hC` (no input supplies that). -/
def CameronMartinGFFReweighting : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → Real.circleAverage f 0 1 = 0 →
    ∃ P' : Measure Ω, P' ≪ P ∧ P ≪ P' ∧
      IsWholePlaneGFF P' (fun ω => addFunPairing (hC ω) f)
        (fun ω r z => hcirc ω r z + Real.circleAverage f z r)

/-- Transfer of the shifted event from the copy `P'` to `P`. If the measurable set `B` agrees `P`-a.s. with the set `B0`
of the two-copy certificate, then the frozen null-set equivalence `CameronMartinGFFMutualAbsCont` (for the discrepancy set
`symmDiff B B0`, a `distributionMeasurableSpace`-set) transfers the agreement to the shifted field `addFunPairing (hC ω) f`
under `P`; the `P'`-a.s. identity for `B0` then passes to `P` through `P ≪ P'`. -/
theorem shift_transfer {Ω : Type u} [MeasurableSpace Ω] {P P' : Measure Ω} [IsProbabilityMeasure P]
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hf0 : Real.circleAverage f 0 1 = 0) (hPP' : P ≪ P') {B B0 : Set ((ℂ → ℝ) → ℝ)}
    (hB : MeasurableSet[distributionMeasurableSpace] B) (hB0 : MeasurableSet[distributionMeasurableSpace] B0)
    (hL : ∀ᵐ ω ∂P, hC ω ∈ B ↔ hC ω ∈ B0) {Q : Ω → Prop}
    (hR : ∀ᵐ ω ∂P', addFunPairing (hC ω) f ∈ B0 ↔ Q ω) :
    ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B ↔ Q ω := by
  have hS : MeasurableSet[distributionMeasurableSpace] (symmDiff B B0) := hB.symmDiff hB0
  have hNull : P ((fun ω => hC ω) ⁻¹' (symmDiff B B0)) = 0 := by
    have hae : ∀ᵐ ω ∂P, ω ∉ (fun ω => hC ω) ⁻¹' (symmDiff B B0) := by
      filter_upwards [hL] with ω h1 hmem
      simp only [Set.mem_preimage, Set.mem_symmDiff] at hmem
      tauto
    simpa using ae_iff.1 hae
  have hN2 : P ((fun ω => addFunPairing (hC ω) f) ⁻¹' (symmDiff B B0)) = 0 :=
    (hCMAbs Ω P hC hcirc f hGFF hf hfc hf0 (symmDiff B B0) hS).1 hNull
  have hae2 : ∀ᵐ ω ∂P, ω ∉ (fun ω => addFunPairing (hC ω) f) ⁻¹' (symmDiff B B0) := by
    rw [ae_iff]
    simpa using hN2
  have hHB : ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B ↔ addFunPairing (hC ω) f ∈ B0 := by
    filter_upwards [hae2] with ω h
    simp only [Set.mem_preimage, Set.mem_symmDiff] at h
    tauto
  have hRP : ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B0 ↔ Q ω := hPP'.ae_le hR
  filter_upwards [hHB, hRP] with ω h1 h2
  exact h1.trans h2

/-- Shifted clause of the metric event, two-sided form: for the base metric `D` and the shifted metric `Dsh`, both
realised through the same metric assignment `𝔇` (`hDb`, `hDs`), a measurable set `B` certifying the base event certifies
the shifted event, `hC ω + f ∈ B ↔ Φ (Dsh ω)` almost surely. The proof is the two-copy argument: the certificate
`hrule` is applied once to the mixture model on `Ω ⊕ Ω`. -/
theorem metric_event_shift_iff (hCM : CameronMartinGFFReweighting.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) {γ ξ : ℝ} {Φ : (ℂ → ℂ → ℝ) → Prop}
    (hrule : MetricEventCertificateStmt.{u} γ ξ Φ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) (hα : α < lqgQ γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (D : Ω → ℂ → ℂ → ℝ)
    (hDb : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y ∧
      ENNReal.ofReal (D ω x y) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hf0 : Real.circleAverage f 0 1 = 0)
    (Dsh : Ω → ℂ → ℂ → ℝ)
    (hDs : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ Φ (D ω)) → ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B ↔ Φ (Dsh ω) := by
  intro B hB hBiff
  obtain ⟨P', hP'P, hPP', hGFF'⟩ := hCM Ω P hC hcirc hGFF f hf hfc hf0
  have : IsProbabilityMeasure P' := hGFF'.isGaussianProcess.isProbabilityMeasure
  have := isProbabilityMeasure_mixMeasure P P'
  have hDs' : ∀ᵐ ω ∂P', ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y :=
    hP'P.ae_le hDs
  have hDmix : ∀ᵐ x ∂mixMeasure P P', ∀ u v, 0 ≤ Sum.elim D Dsh x u v ∧
      ENNReal.ofReal (Sum.elim D Dsh x u v) = weylScaling (𝔇 (Sum.elim hC (fun ω => addFunPairing (hC ω) f) x))
        ξ (fun z => -α * Real.log ‖z‖) u v :=
    (ae_mix_iff _).2 ⟨hDb, hDs'⟩
  have hLQGc : IsLQGMetricOfField (mixMeasure P P') γ ξ α
      (Sum.elim hC (fun ω => addFunPairing (hC ω) f)) (Sum.elim D Dsh) := by
    unfold IsLQGMetricOfField
    exact ⟨𝔇, h𝔇, hDmix⟩
  obtain ⟨B0, hB0, hiff0⟩ := hrule α hα (Ω ⊕ Ω) (mixMeasure P P')
    (Sum.elim hC (fun ω => addFunPairing (hC ω) f))
    (Sum.elim hcirc (fun ω r z => hcirc ω r z + Real.circleAverage f z r))
    (Sum.elim D Dsh) (isWholePlaneGFF_mixMeasure hGFF hGFF') hLQGc
  have hL : ∀ᵐ ω ∂P, hC ω ∈ B ↔ hC ω ∈ B0 := by
    filter_upwards [hBiff, ((ae_mix_iff _).1 hiff0).1] with ω h1 h2
    exact h1.trans h2.symm
  have hR : ∀ᵐ ω ∂P', addFunPairing (hC ω) f ∈ B0 ↔ Φ (Dsh ω) := ((ae_mix_iff _).1 hiff0).2
  exact shift_transfer hCMAbs hGFF hf hfc hf0 hPP' hB hB0 hL hR

/-- Shifted clause of the metric event, in the one-sided form of `hshift` (`FirstPass/S11ab.lean`). -/
theorem metric_event_shift (hCM : CameronMartinGFFReweighting.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) {γ ξ : ℝ} {Φ : (ℂ → ℂ → ℝ) → Prop}
    (hrule : MetricEventCertificateStmt.{u} γ ξ Φ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) (hα : α < lqgQ γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (D : Ω → ℂ → ℂ → ℝ)
    (hDb : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y ∧
      ENNReal.ofReal (D ω x y) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hf0 : Real.circleAverage f 0 1 = 0)
    (Dsh : Ω → ℂ → ℂ → ℝ)
    (hDs : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ Φ (D ω)) → ∀ᵐ ω ∂P, Φ (Dsh ω) → addFunPairing (hC ω) f ∈ B :=
  fun B hB hBiff =>
    (metric_event_shift_iff hCM hCMAbs hrule P hC hcirc hGFF α hα 𝔇 h𝔇 D hDb f hf hfc hf0 Dsh hDs B hB hBiff).mono
      fun _ h hΦ => h.mpr hΦ

/-- The metric transfer lemma `metric_event_transfer_of_rule` with its shifted clause `hshift` discharged by
`metric_event_shift` (the metric `D` is `IsLQGMetricOfField` with the witness `𝔇`). -/
theorem metric_event_transfer_shifted (hCM : CameronMartinGFFReweighting.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) {γ ξ : ℝ} {Φ : (ℂ → ℂ → ℝ) → Prop}
    (hrule : MetricEventCertificateStmt.{u} γ ξ Φ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) (hα : α < lqgQ γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (D : Ω → ℂ → ℂ → ℝ)
    (hDb : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y ∧
      ENNReal.ofReal (D ω x y) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hf0 : Real.circleAverage f 0 1 = 0)
    (Dsh : Ω → ℂ → ℂ → ℝ)
    (hDs : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (hpos : 0 < P {ω | Φ (Dsh ω)}) : ∃ A ⊆ {ω | Φ (D ω)}, MeasurableSet A ∧ 0 < P A := by
  have hD : IsLQGMetricOfField P γ ξ α hC D := by
    unfold IsLQGMetricOfField
    exact ⟨𝔇, h𝔇, hDb⟩
  exact metric_event_transfer_of_rule hCMAbs hrule P hC hcirc hGFF α hα D hD f hf hfc hf0 Dsh
    (metric_event_shift hCM hCMAbs hrule P hC hcirc hGFF α hα 𝔇 h𝔇 D hDb f hf hfc hf0 Dsh hDs) hpos

/-- Shifted clause of the pair event (`MetricMeasureEventCertificateStmt`), two-sided form: the base pair `(D, μ)` and
the shifted pair `(Dsh, μsh)` are realised through the same `𝔇` and the measure hypotheses `hμbase`, `hμshift`
(`IsLQGMeasureOfField` for the shifted circle averages, `FirstPass/S11aj` follow-up of the Lh answer). -/
theorem metricMeasure_event_shift_iff (hCM : CameronMartinGFFReweighting.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) {γ ξ : ℝ} {Φ : (ℂ → ℂ → ℝ) → Measure ℂ → Prop}
    (hrule : S11ag.MetricMeasureEventCertificateStmt.{u} γ ξ Φ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (α : ℝ) (hα : α < lqgQ γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (D : Ω → ℂ → ℂ → ℝ)
    (hDb : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y ∧
      ENNReal.ofReal (D ω x y) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hf0 : Real.circleAverage f 0 1 = 0)
    (Dsh : Ω → ℂ → ℂ → ℝ)
    (hDs : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y)
    (μ μsh : Ω → Measure ℂ) (hμbase : IsLQGMeasureOfField P γ α hcirc μ)
    (hμshift : IsLQGMeasureOfField P γ α (fun ω => addCircleAverage (hcirc ω) f) μsh) :
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ Φ (D ω) (μ ω)) → ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B ↔ Φ (Dsh ω) (μsh ω) := by
  intro B hB hBiff
  obtain ⟨P', hP'P, hPP', hGFF'⟩ := hCM Ω P hC hcirc hGFF f hf hfc hf0
  have : IsProbabilityMeasure P' := hGFF'.isGaussianProcess.isProbabilityMeasure
  have := isProbabilityMeasure_mixMeasure P P'
  have hDs' : ∀ᵐ ω ∂P', ∀ x y, 0 ≤ Dsh ω x y ∧
      ENNReal.ofReal (Dsh ω x y) = weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α * Real.log ‖z‖) x y :=
    hP'P.ae_le hDs
  have hDmix : ∀ᵐ x ∂mixMeasure P P', ∀ u v, 0 ≤ Sum.elim D Dsh x u v ∧
      ENNReal.ofReal (Sum.elim D Dsh x u v) = weylScaling (𝔇 (Sum.elim hC (fun ω => addFunPairing (hC ω) f) x))
        ξ (fun z => -α * Real.log ‖z‖) u v :=
    (ae_mix_iff _).2 ⟨hDb, hDs'⟩
  have hLQGc : IsLQGMetricOfField (mixMeasure P P') γ ξ α
      (Sum.elim hC (fun ω => addFunPairing (hC ω) f)) (Sum.elim D Dsh) := by
    unfold IsLQGMetricOfField
    exact ⟨𝔇, h𝔇, hDmix⟩
  have hμs' : ∀ᵐ ω ∂P', IsLQGLimit γ (fieldCircleAverage α (addCircleAverage (hcirc ω) f)) (μsh ω) :=
    hP'P.ae_le hμshift
  have hMmix : IsLQGMeasureOfField (mixMeasure P P') γ α
      (Sum.elim hcirc (fun ω => addCircleAverage (hcirc ω) f)) (Sum.elim μ μsh) :=
    (ae_mix_iff _).2 ⟨hμbase, hμs'⟩
  obtain ⟨B0, hB0, hiff0⟩ := hrule α hα (Ω ⊕ Ω) (mixMeasure P P')
    (Sum.elim hC (fun ω => addFunPairing (hC ω) f))
    (Sum.elim hcirc (fun ω => addCircleAverage (hcirc ω) f))
    (Sum.elim D Dsh) (Sum.elim μ μsh) (isWholePlaneGFF_mixMeasure hGFF hGFF') hLQGc hMmix
  have hL : ∀ᵐ ω ∂P, hC ω ∈ B ↔ hC ω ∈ B0 := by
    filter_upwards [hBiff, ((ae_mix_iff _).1 hiff0).1] with ω h1 h2
    exact h1.trans h2.symm
  have hR : ∀ᵐ ω ∂P', addFunPairing (hC ω) f ∈ B0 ↔ Φ (Dsh ω) (μsh ω) := ((ae_mix_iff _).1 hiff0).2
  exact shift_transfer hCMAbs hGFF hf hfc hf0 hPP' hB hB0 hL hR

end HarmonicBalls.S11aj
