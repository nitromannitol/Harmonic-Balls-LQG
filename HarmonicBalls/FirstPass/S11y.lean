import HarmonicBalls.FirstPass.S11k
import HarmonicBalls.FirstPass.S11k.BundleParts
import HarmonicBalls.FirstPass.S11k.ExteriorDistances
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11e.CondPos
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity

/-!
# First pass, Lemma 11.12: the positivity pieces E2 and E3 in the local notation (fp-S11y, owner z3)

Local events (`FirstPass/S11h/LocalEvents.lean`, z4's notation): `pinchFirstEventLocal` (E1),
`pinchSecondEventLocal μ D U V δ M` (E2(M): `d₁ = diam^δ(V̄) < a₁ = D(∂B_δ, ∂B_{2δ})` and `M S < μ(U)`),
`pinchThirdEventLocal` (E3). Paper lem:E2 (corrected lines 3700-3727), route ChatGPT z4 note section 6.3.

`pinchLocal_E2_positive` (this file): given an OUTSIDE-measurable event `F` (measurable for the zero-mean exterior
sigma-algebra `comap (localModConstPairings α₀ hC (closure W)ᶜ)`) of positive probability on which E1 holds, there is a
measurable `A ⊆ F` of positive probability on which E1 and E2(M) hold, for every `M > 0`.

Inputs (explicit): the conditional mass-diameter step (`pinchSecondConditionalMass_of_frozen`, from Draft Prop 11.9 and
three frozen inputs), `PinchSecondAnnulusStep` (N2, `FirstPass/S11k/BundleParts.lean:40`), and the item-I/II metric axioms
`LQGMetricFieldAxiomsUnivFrozen`. Proof: choose thresholds `c₁ = 1/(n+1)`, `c₂ = n+1` with
`P(F ∩ {a₁ ≥ c₁, M S ≤ c₂}) > 0` (exhaustion, since `a₁ > 0` and `M S < ∞` a.s.), then the conditional mass set `H`
with `0 < P[1_H | outside]` a.s., and `measure_inter_pos_of_condExp_indicator_pos`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace S11y

/-- Positivity of E2 in the local notation (paper lem:E2). The output set `A` is measurable for the full sigma-algebra
(not yet for the sigma-algebra of the field on `B₇(0)`; see the handoff note). -/
theorem pinchLocal_E2_positive (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ α₀ ξ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D)
    (F : Set Ω)
    (hF : MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] F)
    (hFpos : 0 < P F) (hFE1 : ∀ᵐ ω ∂P, ω ∈ F → pinchFirstEventLocal (D ω) W T Q' Q δ)
    (M : ℝ) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ F ∧ 0 < P A ∧
      ∀ ω ∈ A, pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hδ : 0 < δ := hG.delta_pos
  have hδ1 : δ < 1 / 1000 := hG.delta_lt
  -- the outside sigma-algebra and its open domains
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := fun z hz hzW => by
    have h1 := BundleParts.closure_W_norm_gt_one hG hzW
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  have hBE : ball (0 : ℂ) (3 * δ) ⊆ (closure W)ᶜ := fun z hz hzW => by
    have h1 := BundleParts.closure_W_norm_gt_one hG hzW
    rw [mem_ball_zero_iff] at hz
    linarith
  -- item I (Euclidean length metric) and item II (locality) of the metric axioms
  obtain ⟨𝔇, h𝔇, hDae⟩ := id hDm
  obtain ⟨hI, hII, -, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [hI, hDae] with ω h1 h2
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h3 := ENNReal.toReal_ofReal (h2 u v).1
      rw [(h2 u v).2] at h3
      exact h3.symm
    rw [hDeq]
    exact h1.2
  have hloc : ∀ V' : Set ℂ, IsOpen V' → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V'] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V', ∀ w ∈ V', internalMetric (D ω) V' z w = G ω z w := by
    intro V' hV'
    obtain ⟨G, hGm, hGa⟩ := hII V' hV'
    refine ⟨G, hGm, ?_⟩
    filter_upwards [hGa, hmetric, hDae] with ω h1 h2 h3
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h4 := ENNReal.toReal_ofReal (h3 u v).1
      rw [(h3 u v).2] at h4
      exact h4.symm
    rw [hDeq]
    exact h1
  -- the exterior version of the crossing distance `a₁ = D(∂B_δ, ∂B_{2δ})`
  obtain ⟨a1, ha1m, ha1⟩ := ExteriorDistances.exists_exterior_setDist_spheres hGFF α₀ hE hsph hmetric
    (fun V' hV' _ => hloc V' hV') hδ hBE
  -- the exterior version of the annular Green potential (N2)
  obtain ⟨G, hGm, hGa, hGfin⟩ := hS U V W T Q' Q δ hG γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ
  -- `a₁ > 0` and `M S < ∞` almost surely
  have hpos1 : ∀ᵐ ω ∂P, 0 < a1 ω := by
    filter_upwards [ha1, hmetric] with ω h1 h2
    rw [h1]
    exact IsEuclideanLengthMetric.setDist_spheres_pos h2 0 hδ (by linarith)
  -- the exhaustion sets `E n = {1/(n+1) ≤ a₁, M S ≤ n+1}`, outside-measurable
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set Ω, ∀ n : ℕ, E n =
      {ω | 1 / ((n : ℝ) + 1) ≤ a1 ω ∧ ENNReal.ofReal M * G ω ≤ ENNReal.ofReal ((n : ℝ) + 1)} :=
    ⟨fun n => {ω | 1 / ((n : ℝ) + 1) ≤ a1 ω ∧ ENNReal.ofReal M * G ω ≤ ENNReal.ofReal ((n : ℝ) + 1)},
      fun n => rfl⟩
  have hEm : ∀ n : ℕ, MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ)
      inferInstance] (E n) := by
    intro n
    rw [hEdef n]
    exact (measurableSet_le measurable_const ha1m).inter
      (measurableSet_le (hGm.const_mul _) measurable_const)
  -- every point of `F` almost surely lies in some `E n`
  have hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ n : ℕ, ω ∈ E n := by
    filter_upwards [hpos1, hGfin] with ω hω1 hωfin hωF
    have hfin : ENNReal.ofReal M * G ω ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin
    obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt hω1
    obtain ⟨n1, hn1⟩ := ENNReal.exists_nat_gt hfin
    refine ⟨n0 + n1, ?_⟩
    rw [hEdef, mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · have hn1pos : (0 : ℝ) ≤ n1 := Nat.cast_nonneg n1
      have hn0pos : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
      have hle1 : (1 : ℝ) / (((n0 + n1 : ℕ) : ℝ) + 1) ≤ 1 / ((n0 : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      exact hle1.trans hn0.le
    · have h1 : ((n1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (n1 : ℝ) := (ENNReal.ofReal_natCast n1).symm
      have h2 : ENNReal.ofReal (n1 : ℝ) ≤ ENNReal.ofReal (((n0 + n1 : ℕ) : ℝ) + 1) :=
        ENNReal.ofReal_le_ofReal (by push_cast; linarith [(Nat.cast_nonneg n0 : (0 : ℝ) ≤ n0)])
      exact hn1.le.trans (h1 ▸ h2)
  -- some `E n` has positive probability when intersected with `F`
  have hex : ∃ n : ℕ, 0 < P (F ∩ E n) := by
    by_contra hcon
    have hcon' : ∀ n : ℕ, P (F ∩ E n) ≤ 0 := fun n => not_lt.1 fun h => hcon ⟨n, h⟩
    have hU : P (⋃ n : ℕ, F ∩ E n) = 0 :=
      measure_iUnion_null_iff.2 fun n => le_antisymm (hcon' n) zero_le
    have hFsub : F ≤ᵐ[P] ⋃ n : ℕ, F ∩ E n := by
      filter_upwards [hcover] with ω hω
      intro hωF
      obtain ⟨n, hn⟩ := hω hωF
      exact mem_iUnion.2 ⟨n, hωF, hn⟩
    have h2 := measure_mono_ae hFsub
    rw [hU] at h2
    exact hFpos.ne' (le_antisymm h2 zero_le)
  obtain ⟨n, hnpos⟩ := hex
  have hc1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hc2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the conditional mass-diameter set `H` for the thresholds `c₁ = 1/(n+1)`, `c₂ = n+1`
  obtain ⟨H, hHm, hHsub, hcond⟩ := pinchSecondConditionalMass_of_frozen hD hM hDiam hMk U V W T Q' Q δ hG
    γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hDm (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) hc1 hc2
  have hle := localModConstPairings_comap_le (α₀ := α₀) (hC := hC) hGFF (closure W)ᶜ
  have hpos : 0 < P ((F ∩ E n) ∩ H) :=
    measure_inter_pos_of_condExp_indicator_pos P hle (hF.inter (hEm n)) hHm hnpos hcond
  -- the exceptional set on which the almost sure identities used below may fail
  have hall : ∀ᵐ ω ∂P, (ω ∈ F → pinchFirstEventLocal (D ω) W T Q' Q δ) ∧
      a1 ω = setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
      G ω = annulusGreenPotentialSup (μ ω) 0 3 6 := by
    filter_upwards [hFE1, ha1, hGa] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  refine ⟨((F ∩ E n) ∩ H) \ N, ?_, ?_, ?_, ?_⟩
  · exact (((hle _ (hF.inter (hEm n))).inter hHm)).diff hNm
  · intro ω hω
    exact hω.1.1.1
  · rw [measure_sdiff_null hN0]
    exact hpos
  · intro ω hω
    obtain ⟨⟨⟨hωF, hωE⟩, hωH⟩, hωN⟩ := hω
    have hωp : (ω ∈ F → pinchFirstEventLocal (D ω) W T Q' Q δ) ∧
        a1 ω = setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
        G ω = annulusGreenPotentialSup (μ ω) 0 3 6 := by
      by_contra h
      exact hωN (hNsub h)
    obtain ⟨hE1ω, hA1ω, hGω⟩ := hωp
    refine ⟨hE1ω hωF, ?_⟩
    simp only [hEdef, mem_ofPred_eq] at hωE
    obtain ⟨hA, hB⟩ := hωE
    obtain ⟨hmass, hdiam⟩ := hHsub hωH
    rw [hA1ω] at hA
    unfold pinchSecondEventLocal
    rw [← hGω]
    constructor
    · refine lt_of_lt_of_le hdiam (ENNReal.ofReal_le_ofReal ?_)
      linarith
    · calc ENNReal.ofReal M * G ω ≤ ENNReal.ofReal ((n : ℝ) + 1) := hB
        _ < ENNReal.ofReal (2 * ((n : ℝ) + 1)) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
        _ < μ ω U := hmass

end S11y

end HarmonicBalls
