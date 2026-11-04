import HarmonicBalls.Proofs.Sec5.CofinalUniformFailure
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-! # The law of the uniform containment event -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory Filter
open scoped ENNReal

/-- The unit-scale event that all clusters with centres in the half-ball
stay inside the unit ball until the `m`th reciprocal dyadic time. -/
def unitClusterContainmentEvent (m : ℕ) : Set (Measure ℂ) :=
  {ν | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m),
    closure (cluster ν 1 z t) ⊆ ball 0 1}

/-- Measurability of the countable collection of containment events is
sufficient for the uniform outer-probability bounds at all dyadic radii. -/
theorem uniformDyadicFailureBounds_of_unitContainmentMeasurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hmeas : ∀ m, NullMeasurableSet (unitClusterContainmentEvent m) (Measure.map μ P)) :
    ∃ b : ℕ → ℝ≥0∞, (⨅ m, b m) = 0 ∧ ∀ m n,
      P (normalizedDyadicContainmentEvent γ α₀ hcirc μ m n)ᶜ ≤ b m := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let L := Measure.map μ P
  have hμmeas : AEMeasurable μ P := h.aemeasurable_lqgMeasure hμ
  let B : ℕ → Set (Measure ℂ) := fun m => (unitClusterContainmentEvent m)ᶜ
  let b : ℕ → ℝ≥0∞ := fun m => L (B m)
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
    have hs := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ (1 / 2) (by norm_num)
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
  have hsmall : (⨅ m, b m) = 0 := by
    change (⨅ m, L (B m)) = 0
    rw [← hanti.measure_iInter (fun m => (hmeas m).compl) ⟨0, measure_ne_top L _⟩]
    rw [Measure.map_apply₀ hμmeas (NullMeasurableSet.iInter fun m => (hmeas m).compl)]
    apply measure_mono_null _ (ae_iff.1 hgood)
    intro ω hω
    simp only [mem_preimage, mem_iInter, mem_compl_iff] at hω
    simp only [mem_ofPred_eq, not_exists]
    exact hω
  refine ⟨b, hsmall, ?_⟩
  intro m n
  have hd := h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (k := (2 : ℝ) ^ n) (by positivity)
  change P ((fun ω => normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) ⁻¹'
    (B m)) ≤ L (B m)
  calc
    _ ≤ (Measure.map
      (fun ω => normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) P) (B m) :=
        Measure.le_map_apply hd.aemeasurable_snd (B m)
    _ = L (B m) := by rw [← hd.map_eq]

/-- The cofinal interval step follows from the earlier numbered results and
null measurability of only the countable unit-containment events. The two
field scaling inputs remain explicit. -/
theorem cofinalRegularizedClusterIntervals_of_unitContainmentMeasurable
    (h32 : ClusterOpenLaplacianStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h54 : RegularizedClusterHarmonicBallsStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hmeas : ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ m, NullMeasurableSet (unitClusterContainmentEvent m) (Measure.map μ P)) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_uniformFailure h32 h53 h54 hAff hCC
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  exact uniformDyadicFailureBounds_of_unitContainmentMeasurable h (hAff P hC hcirc)
    (hCC P γ α₀ hC hcirc) hγ hγ2 hα hμ h71
    (hmeas γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ)

end HarmonicBalls
