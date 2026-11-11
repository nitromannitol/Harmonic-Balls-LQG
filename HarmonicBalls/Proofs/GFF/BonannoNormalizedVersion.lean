import HarmonicBalls.Proofs.GFF.FullTestDistributionVersion

/-! # The normalized distribution-valued GFF

The distribution reconstruction and the canonical normalized GFF are due to
Leonardo Bonanno. Exceptional sets for circle averages may depend on the
radius and center. -/

noncomputable section
open MeasureTheory Filter ProbabilityTheory
namespace HarmonicBalls

/-- The measurable reconstruction of the full test-function process. -/
def reconstructedGFF {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) : LQGMetric.DistC :=
  fullTestDistributionVersion (fun φ => hC ω φ)

theorem IsWholePlaneGFF.measurable_reconstructedGFF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) : Measurable (reconstructedGFF hC) := by
  apply measurable_fullTestDistributionVersion.comp
  exact measurable_pi_iff.mpr fun φ => hh.measurable_pairing φ
    ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩

/-- The reconstructed field has the law of any normalized Bonanno GFF. -/
theorem IsWholePlaneGFF.map_reconstructedGFF_eq
    {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {T : Ω' → LQGMetric.DistC}
    (hT : LQGMetric.IsNormalizedWPGFF T P') : P.map (reconstructedGFF hC) = P'.map T := by
  obtain ⟨hC', hcirc', hh', heq, _⟩ := normalizedGFF_exists_projectGFF hT
  let X : Ω → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC ω) (hcirc ω)
  let X' : Ω' → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC' ω) (hcirc' ω)
  let R : (GFFObservable.Admissible → ℝ) → LQGMetric.DistC := fun f =>
    fullTestDistributionVersion (fun φ => f (testObservable φ))
  have hR : Measurable R := measurable_fullTestDistributionVersion.comp
    (measurable_pi_iff.mpr fun φ => measurable_pi_apply (testObservable φ))
  have he : R ∘ X' = T := by
    funext ω
    change fullTestDistributionVersion (fun φ => hC' ω φ) = T ω
    simp only [heq, fullTestDistributionVersion_pairings]
  calc
    P.map (reconstructedGFF hC) = (P.map X).map R :=
      (Measure.map_map hR hh.measurable_admissibleObservationProcess).symm
    _ = (P'.map X').map R := by rw [hh.map_admissibleObservationProcess_eq hh']
    _ = P'.map T := by rw [Measure.map_map hR hh'.measurable_admissibleObservationProcess, he]

/-- The reconstructed field satisfies Bonanno's normalized whole-plane GFF predicate. -/
theorem IsWholePlaneGFF.reconstructedGFF_normalized
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    LQGMetric.IsNormalizedWPGFF (reconstructedGFF hC) P := by
  obtain ⟨Ω', mΩ', P', hP', T, hT⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  have hm := hh.measurable_reconstructedGFF
  have hlaw := hh.map_reconstructedGFF_eq hT
  obtain ⟨K, _, hv, _⟩ := hh.exists_fullTest_distribution_version
  have hv' : ∀ φ : LQGMetric.TestC,
      (fun ω => reconstructedGFF hC ω φ) =ᵐ[P] (fun ω => hC ω φ) := by
    intro φ
    filter_upwards [ae_fullTestDistributionVersion_eq_of_version K hv, hv φ] with ω h₁ h₂
    exact congrFun (congrArg DFunLike.coe h₁) φ |>.trans h₂
  refine ⟨⟨hm, ?_, ?_, ?_⟩, ?_⟩
  · have hg := hh.isGaussianProcess.comp_right (fun φ : LQGMetric.TestC0 => testObservable φ.1)
    exact hg.congr (fun φ => (hv' φ.1).symm)
  · intro φ
    have heval := LQGMetric.measurable_distOn_apply φ.1
    calc
      ∫ ω, reconstructedGFF hC ω φ.1 ∂P = ∫ t, t φ.1 ∂(P.map (reconstructedGFF hC)) :=
        (integral_map hm.aemeasurable heval.aestronglyMeasurable).symm
      _ = ∫ t, t φ.1 ∂(P'.map T) := by rw [hlaw]
      _ = ∫ ω, T ω φ.1 ∂P' := integral_map hT.1.measurable.aemeasurable heval.aestronglyMeasurable
      _ = 0 := hT.1.centered φ
  · intro φ ψ
    have hφ := LQGMetric.measurable_distOn_apply φ.1
    have hψ := LQGMetric.measurable_distOn_apply ψ.1
    calc
      cov[fun ω => reconstructedGFF hC ω φ.1, fun ω => reconstructedGFF hC ω ψ.1; P] =
          cov[fun t : LQGMetric.DistC => t φ.1, fun t : LQGMetric.DistC => t ψ.1;
            P.map (reconstructedGFF hC)] :=
        (covariance_map_fun hφ.aestronglyMeasurable hψ.aestronglyMeasurable hm.aemeasurable).symm
      _ = cov[fun t : LQGMetric.DistC => t φ.1, fun t : LQGMetric.DistC => t ψ.1; P'.map T] := by rw [hlaw]
      _ = cov[fun ω => T ω φ.1, fun ω => T ω ψ.1; P'] :=
        covariance_map_fun hφ.aestronglyMeasurable hψ.aestronglyMeasurable hT.1.measurable.aemeasurable
      _ = LQGMetric.logCov φ.1 ψ.1 := hT.1.covariance_eq φ ψ
  · have hs : MeasurableSet {t : LQGMetric.DistC | LQGMetric.circleAvg t 1 0 = 0} :=
      measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const
    apply (ae_map_iff hm.aemeasurable hs).1
    rw [hlaw]
    exact (ae_map_iff hT.1.measurable.aemeasurable hs).2 hT.2

/-- Each positive-radius raw circle average agrees almost surely with the
circle average of the reconstructed distribution. -/
theorem IsWholePlaneGFF.ae_circleAvg_reconstructedGFF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, hcirc ω r z = LQGMetric.circleAvg (reconstructedGFF hC ω) r z := by
  obtain ⟨Ω', mΩ', P', hP', T, hT⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  obtain ⟨hC', hcirc', hh', heq, hcircle⟩ := normalizedGFF_exists_projectGFF hT
  let X : Ω → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC ω) (hcirc ω)
  let X' : Ω' → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC' ω) (hcirc' ω)
  let R : (GFFObservable.Admissible → ℝ) → LQGMetric.DistC := fun f =>
    fullTestDistributionVersion (fun φ => f (testObservable φ))
  let o : GFFObservable.Admissible := ⟨.circle r z, hr⟩
  have hR : Measurable R := measurable_fullTestDistributionVersion.comp
    (measurable_pi_iff.mpr fun φ => measurable_pi_apply (testObservable φ))
  let S : Set (GFFObservable.Admissible → ℝ) :=
    {f | f o = LQGMetric.circleAvg (R f) r z}
  have hS : MeasurableSet S := measurableSet_eq_fun (measurable_pi_apply o)
    ((LQGMetric.measurable_circleAvg_left r z).comp hR)
  have href : ∀ᵐ ω ∂P', X' ω ∈ S := by
    filter_upwards [hcircle r hr z, hT.2] with ω hc hn
    change hcirc' ω r z = LQGMetric.circleAvg
      (fullTestDistributionVersion (fun φ => hC' ω φ)) r z
    simp only [heq, fullTestDistributionVersion_pairings]
    simpa only [LQGMetric.CircleAvg.cInc, hn, sub_zero] using hc
  have hin : ∀ᵐ f ∂P.map X, f ∈ S := by
    rw [hh.map_admissibleObservationProcess_eq hh']
    exact (ae_map_iff hh'.measurable_admissibleObservationProcess.aemeasurable hS).2 href
  exact (ae_map_iff hh.measurable_admissibleObservationProcess.aemeasurable hS).1 hin

/-- The reconstructed field has exactly zero unit-circle average almost surely. -/
theorem IsWholePlaneGFF.ae_circleAvg_one_zero_reconstructedGFF
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg (reconstructedGFF hC ω) 1 0 = 0 :=
  hh.reconstructedGFF_normalized.2

end HarmonicBalls
