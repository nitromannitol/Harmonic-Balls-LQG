import HarmonicBalls.FirstPass.S11d.ShiftAssembly
import HarmonicBalls.FirstPass.S11d.CMTransfer
import HarmonicBalls.FirstPass.S11d.Core
import HarmonicBalls.FirstPass.S11d.ShiftSets
import HarmonicBalls.FirstPass.Frozen.S11d

/-!
# Proposition 11.9 (`prop:mass-diam-gen`)

`firstPass_11_9` proves `SmallMetricDiameterLargeMassStmt` (Draft/Section11.lean) from:
* the 11.10 input `SmallMetricDiameterLargeMassSquareStmt`;
* FROZEN inputs: `LQGMetricContinuousShiftFactI`, `WeylScalingCompositionFrozen`,
  `CameronMartinGFFMutualAbsCont`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`,
  `LQGInternalMetricWeylAeMeasurableFrozen`, `LQGMassFunctionalMeasurableFrozen`;
* the Proposed input `LQGMetricFieldAxioms` (pending operator source-check), taken as a hypothesis.

Proof. `shifted_event_exists` gives the shifted event for
`h̃ = h^ℂ + g - α₀ log|·|`. The Cameron-Martin transfer `cm_transfer_pos` moves it to `h^ℂ` along a set `B` of fields.
`B` is defined with a countable dense `Q ⊆ V` (the sup over `V` is reduced to `Q` by `internalMetric_le_on_closure`),
so that `B` is measurable. The mass `μ(S₁)` enters through the frozen field-level mass functional `F`.
-/

universe u

namespace HarmonicBalls
open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- Measurability of the whole-plane field as a map into the distribution σ-algebra (pairings are measurable). -/
theorem measurable_field_distribution {Ω : Type u} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ}
    (hpair : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  exact iSup₂_le fun φ hφ => (hpair φ hφ).comap_le

/-- Proposition 11.9 (`prop:mass-diam-gen`): the Draft statement `SmallMetricDiameterLargeMassStmt`. -/
theorem firstPass_11_9
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD U V W hUo hUc hUb hVo hVc hVb hWo hWc hWb hUV hVW hcl hWs
    C ε hε hεC
  have hPprob : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨𝔇, h𝔇, hDeq, g, hgc, hgs, hg0, S₁, hS₁c, hg0S₁, hS₁U, A, hA, hAp, hAprop⟩ :=
    shifted_event_exists hγ0 hγ2 hα hGFF hμ hD (hAx γ ξ α₀ Ω P hC hcirc) hShift hFD h1110
      hUo hUc hVo hVc hVb hWo hWb hUV hVW hcl hWs hε hεC
  have hgcont : Continuous g := hgc.continuous
  -- Fact 2.2 I for the zero shift: the metric of `h` is an Euclidean length metric, almost surely.
  have hlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) := by
    filter_upwards [hShift γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 (fun _ => 0) continuous_const] with ω hω
    simpa [zero_sub, neg_mul] using hω.2
  -- the mass functional, and its value on `h^ℂ` (zero shift; `g = 0` on `S₁`)
  obtain ⟨F, hF, hFid⟩ := hMass γ α₀ Ω P hC hcirc μ hGFF hγ0 hγ2 hα hμ S₁ hS₁c
  have hFid0 : ∀ᵐ ω ∂P, F (hC ω) = μ ω S₁ := by
    filter_upwards [hFid (fun _ => 0) continuous_const (fun _ _ => rfl)] with ω hω
    have hadd : addFunPairing (hC ω) (fun _ => 0) = hC ω := by
      funext φ
      simp [addFunPairing]
    rwa [hadd] at hω
  -- countable dense subset of `V` (the sup over `V` is reduced to it)
  obtain ⟨Q, hQc, hQV, hVQ⟩ := TopologicalSpace.exists_countable_dense_subset V
  -- the field-level measurable versions `Φ q q'` of the internal metric on `W` (frozen), for the pairs in `Q`
  have hMetΦ := hMet γ ξ α₀ Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hα h𝔇 W hWo
  choose Φ hΦm hΦa using hMetΦ
  -- the set of fields `T` with the metric bound on `Q` and the mass bound
  set B : Set ((ℂ → ℝ) → ℝ) :=
    (⋂ q ∈ Q, ⋂ q' ∈ Q, {T | Φ q q' T ≤ ENNReal.ofReal ε}) ∩ {T | ENNReal.ofReal C ≤ F T} with hBdef
  have hBmem : ∀ T, T ∈ B ↔ (∀ q ∈ Q, ∀ q' ∈ Q, Φ q q' T ≤ ENNReal.ofReal ε) ∧
      ENNReal.ofReal C ≤ F T := by
    intro T
    simp [hBdef, Set.mem_iInter]
  have hBm : MeasurableSet[distributionMeasurableSpace] B := by
    refine MeasurableSet.inter ?_ ?_
    · refine MeasurableSet.biInter hQc fun q _ => MeasurableSet.biInter hQc fun q' _ => ?_
      exact measurableSet_le (hΦm q q') measurable_const
    · exact measurableSet_le measurable_const hF
  have hCmeas : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC :=
    measurable_field_distribution hGFF.measurable_pairing
  -- the shifted event lies in the preimage of `B` under the shift, with positive probability
  have hWSCg := hWSC γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 g hgcont
  have hMg : ∀ᵐ ω ∂P, F (addFunPairing (hC ω) g) = μ ω S₁ :=
    hFid g hgcont (fun x hx => hg0S₁ x hx)
  have hΦg : ∀ᵐ ω ∂P, ∀ q ∈ Q, ∀ q' ∈ Q, Φ q q' (addFunPairing (hC ω) g) = internalMetric
      (fun u v => (weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) W q q' :=
    (ae_ball_iff hQc).2 fun q _ => (ae_ball_iff hQc).2 fun q' _ => hΦa q q' g hgcont
  have hsub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ (fun ω => addFunPairing (hC ω) g) ⁻¹' B := by
    filter_upwards [hWSCg, hMg, hΦg] with ω h1 h2 h3 hωA
    obtain ⟨hmet, hmass⟩ := hAprop ω hωA
    rw [Set.mem_preimage, hBmem]
    refine ⟨fun q hq q' hq' => ?_, by rw [h2]; exact hmass⟩
    have hfun : (fun u v => (weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ
        (fun z => -α₀ * Real.log ‖z‖) u v).toReal)
        = (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => g z - α₀ * Real.log ‖z‖) x y).toReal) := by
      funext x y
      rw [h1 x y]
    rw [h3 q hq q' hq', hfun]
    exact hmet q (hQV hq) q' (hQV hq')
  have hpos : 0 < P ((fun ω => addFunPairing (hC ω) g) ⁻¹' B) :=
    lt_of_lt_of_le hAp (measure_mono_ae hsub)
  have hT : 0 < P ((fun ω => hC ω) ⁻¹' B) :=
    cm_transfer_pos hCM hGFF hgc hgs hg0 hBm hpos
  -- the positive-probability event for `h^ℂ`, inside the full-measure set of pointwise identities
  have hBmeas : MeasurableSet ((fun ω => hC ω) ⁻¹' B) := hCmeas hBm
  have hadd : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := fun T => by
    funext φ
    simp [addFunPairing]
  have hΦ0 : ∀ᵐ ω ∂P, ∀ q ∈ Q, ∀ q' ∈ Q, Φ q q' (hC ω) = internalMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) W q q' := by
    filter_upwards [(ae_ball_iff hQc).2 fun q _ => (ae_ball_iff hQc).2 fun q' _ =>
      hΦa q q' (fun _ => 0) continuous_const] with ω h
    simpa only [hadd] using h
  obtain ⟨A', hA'm, hA'sub, hA'good, hA'P⟩ := exists_measurable_subset_of_ae hBmeas
    (fun ω => F (hC ω) = μ ω S₁ ∧
      IsEuclideanLengthMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ∧
      D ω = (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ∧
      ∀ q ∈ Q, ∀ q' ∈ Q, Φ q q' (hC ω) = internalMetric
        (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) W q q')
    (by filter_upwards [hFid0, hlen, hDeq, hΦ0] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩)
  refine ⟨A', fun ω hω => ?_, hA'm, by rw [hA'P]; exact hT⟩
  obtain ⟨h1, h2, h3, h4⟩ := hA'good ω hω
  have hωB : hC ω ∈ B := hA'sub hω
  obtain ⟨hmetB, hmassB⟩ := (hBmem (hC ω)).1 hωB
  have hcl' : closure Q ⊆ W := (closure_mono hQV).trans hcl
  show (∀ u ∈ V, ∀ v ∈ V, internalMetric (D ω) W u v ≤ ENNReal.ofReal ε) ∧ ENNReal.ofReal C ≤ μ ω U
  refine ⟨fun u hu v hv => ?_, ?_⟩
  · rw [h3]
    have hcl_bound := internalMetric_le_on_closure h2 (fun x y => ENNReal.toReal_nonneg) hWo hcl'
      (c := ENNReal.ofReal ε) (fun q hq q' hq' => by
        rw [← h4 q hq q' hq']
        exact hmetB q hq q' hq')
    exact hcl_bound u (hVQ hu) v (hVQ hv)
  · rw [h1] at hmassB
    exact hmassB.trans (measure_mono hS₁U)

end HarmonicBalls
