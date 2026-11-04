import HarmonicBalls.Proofs.Sec5.ExactContainmentHorizon
import HarmonicBalls.Proofs.Sec5.ContainmentEventNullMeasurable

/-! # Uniform containment at arbitrary time horizons -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- The all-centre containment event is null measurable under the LQG
measure law for every real time horizon. -/
theorem IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentUntil_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (T : ℝ) : NullMeasurableSet (unitClusterContainmentUntil T) (Measure.map μ P) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ zero_lt_one
  obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder zero_lt_one
  obtain ⟨S, hSa, hSeq⟩ := exists_analyticSet_unitClusterContainmentUntil_compl Q hQeq T
  have hnull : NullMeasurableSet (Q ⁻¹' S) (Measure.map μ P) :=
    (AnalyticSet.nullMeasurableSet_of_finite (Measure.map Q (Measure.map μ P)) hSa).preimage
      (hQ.quasiMeasurePreserving _)
  have heq : Q ⁻¹' S =ᵐ[Measure.map μ P] (unitClusterContainmentUntil T)ᶜ := by
    filter_upwards [hGae] with ν hν
    exact propext (hSeq ν (hGgood ν hν).1 (hGgood ν hν).2)
  simpa only [compl_compl] using (hnull.congr heq).compl

/-- The arbitrary-horizon event is null measurable on the original
probability space. -/
theorem IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentUntil
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (T : ℝ) : NullMeasurableSet (μ ⁻¹' unitClusterContainmentUntil T) P := by
  have hm := hGFF.aemeasurable_lqgMeasure hμ
  have hn := hGFF.nullMeasurableSet_unitClusterContainmentUntil_measureLaw hI2 hγ hγ2 hα hμ T
  have hmap : Measure.map μ P = Measure.map (hm.mk μ) P := Measure.map_congr hm.ae_eq_mk
  rw [hmap] at hn
  apply (hn.preimage (hm.measurable_mk.quasiMeasurePreserving P)).congr
  filter_upwards [hm.ae_eq_mk] with ω hω
  simp only [mem_preimage, ← hω]

/-- Failure probabilities tend to zero as the positive time horizon tends to
zero, uniformly over all positive scaling factors. The two field scaling
inputs are proposed and await source review. -/
theorem uniformScale_containmentFailure_smallTime
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∃ b : ℝ → ℝ≥0∞,
      (∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ, 0 < T → T ≤ δ → b T < ε) ∧
      (∀ T k : ℝ, 0 < k →
        P ({ω | normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω) ∈
          unitClusterContainmentUntil T}ᶜ) = b T) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let L := Measure.map μ P
  let B : ℕ → Set (Measure ℂ) := fun m => (unitClusterContainmentEvent m)ᶜ
  let b : ℝ → ℝ≥0∞ := fun T => L (unitClusterContainmentUntil T)ᶜ
  have hanti : Antitone B := by
    intro i j hij ν hν
    change ν ∉ unitClusterContainmentEvent j at hν
    change ν ∉ unitClusterContainmentEvent i
    intro hi
    apply hν
    intro z hz t ht
    exact hi z hz t ⟨ht.1, lt_of_lt_of_le ht.2
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)⟩
  have hgood : ∀ᵐ ω ∂P, ∃ m, μ ω ∈ unitClusterContainmentEvent m := by
    have hs := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
    filter_upwards [hs.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    refine ⟨m, ?_⟩
    intro z hz t ht x hx
    have hnear := hm t ⟨ht.1, ht.2.le⟩ z hz hx
    simp only [mem_ball, dist_zero_right] at hz ⊢
    have htri := dist_triangle x z (0 : ℂ)
    simp only [dist_zero_right] at htri
    simp only [mem_ball] at hnear
    norm_num at hnear hz ⊢
    linarith
  have hsmall : (⨅ m, L (B m)) = 0 := by
    rw [← hanti.measure_iInter (fun m =>
      (hGFF.nullMeasurableSet_unitClusterContainmentEvent_measureLaw hI2 hγ hγ2 hα hμ m).compl)
      ⟨0, measure_ne_top L _⟩]
    rw [Measure.map_apply₀ (hGFF.aemeasurable_lqgMeasure hμ)
      (NullMeasurableSet.iInter fun m =>
        (hGFF.nullMeasurableSet_unitClusterContainmentEvent_measureLaw hI2 hγ hγ2 hα hμ m).compl)]
    apply measure_mono_null _ (ae_iff.1 hgood)
    intro ω hω
    simp only [mem_preimage, mem_iInter, mem_compl_iff] at hω
    simp only [mem_ofPred_eq, not_exists]
    exact hω
  refine ⟨b, ?_, ?_⟩
  · intro ε hε
    have hlt : (⨅ m, L (B m)) < ε := by rw [hsmall]; exact hε
    obtain ⟨m, hm⟩ := iInf_lt_iff.mp hlt
    refine ⟨(2 : ℝ)⁻¹ ^ m, by positivity, ?_⟩
    intro T _ hT
    apply lt_of_le_of_lt _ hm
    apply measure_mono
    intro ν hν
    change ν ∉ unitClusterContainmentUntil T at hν
    change ν ∉ unitClusterContainmentEvent m
    intro hcontain
    apply hν
    intro z hz t ht
    exact hcontain z hz t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  · intro T k hk
    have hd := hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk
    have hn := (hGFF.nullMeasurableSet_unitClusterContainmentUntil_measureLaw
      hI2 hγ hγ2 hα hμ T).compl
    change P ((fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) ⁻¹'
      (unitClusterContainmentUntil T)ᶜ) = L (unitClusterContainmentUntil T)ᶜ
    calc
      _ = (Measure.map (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) P)
          (unitClusterContainmentUntil T)ᶜ := (Measure.map_apply₀ hd.aemeasurable_snd (by
            rw [← hd.map_eq]
            exact hn)).symm
      _ = L (unitClusterContainmentUntil T)ᶜ := by rw [← hd.map_eq]

#print axioms IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentUntil_measureLaw
#print axioms IsWholePlaneGFF.nullMeasurableSet_unitClusterContainmentUntil
#print axioms uniformScale_containmentFailure_smallTime

end HarmonicBalls
