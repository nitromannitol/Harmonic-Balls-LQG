import HarmonicBalls.FirstPass.S11r.UnrootedFixed

/-!
# The unrooted identity (18) with an explicit constant (step 1 of the local-agreement route for `hN2`)

For a fixed LQG metric `𝔇` and a disk `D = ball c r` with `0 ∉ closedBall c r`, let `(ρ, M)` be a bump and a decoder
as in `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (that is, `M (obs_D h^ℂ) = e^{-ξ ⟨h^ℂ,ρ⟩} D_{h^ℂ}(·,·;D)`
almost surely on `D × D` for every whole-plane GFF). Then for every `α < Q_γ`, almost surely
`M (obs_D h^α) = exp(-ξ ⟨h^α, ρ⟩) · D_{h^α}(·,·;D)` on `D × D`, where `⟨h^α, ρ⟩ = fieldPairing α (hC ω) ρ` and
`D_{h^α}` is the internal metric of the Weyl scaling of `𝔇 (h^ℂ)` by `-α log|·|`.

This is `unrooted_identity_fixedMetric` with the constant `b` of its conclusion made explicit and the decoder data
`(ρ, M)` taken as parameters instead of existentially quantified: the proof is that of `unrooted_identity_fixedMetric`,
with the identification `⟨h^ℂ + f, ρ⟩ = ⟨h^α, ρ⟩` at the end (`f = -α log|·|` on `D ⊇ tsupport ρ`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **(18) with the explicit constant `exp(-ξ ⟨h^α, ρ⟩)`.** -/
theorem unrooted_identity_fixedMetric_explicit
    {γ ξ : ℝ}
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {ρ : ℂ → ℝ}
    {M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ}
    (hρT : IsTestFunction (ball c r) ρ) (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
          ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
              internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2) :
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P,
          ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
            ENNReal.ofReal (M (localMeanZeroObs α (ball c r) (hC ω)) p) =
              ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) ρ)) * internalMetric
                (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal)
                (ball c r) p.1.1 p.1.2 := by
  intro α hα Ω _ P _ hC hcirc hGFF
  have hQ0 : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨f, hfsm, hfcomp, hfcirc, hfloc⟩ := exists_negLog_cutoff α hr h0
  have hfc : Continuous f := hfsm.continuous
  have hBopen : IsOpen (ball c r) := isOpen_ball
  -- countable dense set of endpoints in `D × D`
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ))
  have : Countable ↥Q := hQc.to_subtype
  -- measurable versions of the internal metric (frozen input, `α₀ = 0`)
  have hΦ : ∀ q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞,
      Measurable[distributionMeasurableSpace] Φ ∧ ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P,
        Φ (addFunPairing (hC ω) g) = internalMetric
          (fun x y => (weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -(0 : ℝ) * Real.log ‖z‖) x y).toReal)
          (ball c r) q.1.1 q.1.2 := fun q =>
    hPhi γ ξ 0 Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hQ0 h𝔇 (ball c r) hBopen q.1.1 q.1.2
  choose Φ hΦm hΦid using hΦ
  -- the value of `Φ_q` on a shifted field is the internal metric of that field
  have hPhiVal : ∀ (q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ))) (g : ℂ → ℝ), Continuous g → ∀ᵐ ω ∂P,
      Φ q (addFunPairing (hC ω) g) = internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) q.1.1 q.1.2 := by
    intro q g hg
    filter_upwards [hΦid q g hg, FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF g hg] with ω h1 h2
    rw [h1]
    have hfun : (fun x y => (weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ
        (fun z => -(0 : ℝ) * Real.log ‖z‖) x y).toReal) = 𝔇 (addFunPairing (hC ω) g) := by
      funext x y
      have hz : (fun z : ℂ => -(0 : ℝ) * Real.log ‖z‖) = 0 := by
        funext z
        simp
      rw [hz, h2.weylScaling_zero ξ x y, ENNReal.toReal_ofReal (euclidLength_nonneg h2 x y)]
    rw [hfun]
  -- the Borel set of fields satisfying the identity on `Q`
  let S : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) → Set ((ℂ → ℝ) → ℝ) := fun q =>
    {T | ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) T) q) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 T ρ)) * Φ q T}
  let B : Set ((ℂ → ℝ) → ℝ) := ⋂ q ∈ Q, S q
  have hSm : ∀ q, MeasurableSet[distributionMeasurableSpace] (S q) := by
    intro q
    have hobs : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
        localMeanZeroObs 0 (ball c r) T := measurable_localMeanZeroObs_zero (ball c r)
    have hρm : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
        ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 T ρ)) := by
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
      exact (measurable_fieldPairing_zero ⟨hρT.1, hρT.2.1, subset_univ _⟩).const_mul _
    have hLHS : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
        ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) T) q) :=
      ENNReal.measurable_ofReal.comp (((ContinuousMap.measurable_eval q).comp hMm).comp hobs)
    exact measurableSet_eq_fun hLHS (hρm.mul (hΦm q))
  have hBm : MeasurableSet[distributionMeasurableSpace] B :=
    MeasurableSet.biInter hQc fun q _ => hSm q
  -- a.s. `h^ℂ ∈ B`: the corrected identity at `h^ℂ` and the Φ-values at `h^ℂ`
  have hmem : ∀ᵐ ω ∂P, hC ω ∈ B := by
    have hval : ∀ᵐ ω ∂P, ∀ q ∈ Q, Φ q (hC ω) = internalMetric (𝔇 (hC ω)) (ball c r) q.1.1 q.1.2 :=
      (ae_ball_iff hQc).2 fun q _ => by
        simpa [addFunPairing_zero_fun] using hPhiVal q 0 continuous_const
    filter_upwards [hid Ω P hC hcirc hGFF, hval] with ω hω hvω
    show hC ω ∈ ⋂ q ∈ Q, S q
    refine Set.mem_iInter₂.2 fun q hq => ?_
    change ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) q) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) * Φ q (hC ω)
    rw [hω q, hvω q hq]
  -- Cameron-Martin: `h^ℂ + f ∈ B` almost surely
  have hadd := ae_mem_addFunPairing_of_ae_mem hCM P hC hcirc f hGFF hfsm hfcomp hfcirc B hBm hmem
  have hqΦ : ∀ᵐ ω ∂P, ∀ q ∈ Q, Φ q (addFunPairing (hC ω) f) =
      internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) q.1.1 q.1.2 :=
    (ae_ball_iff hQc).2 fun q _ => hPhiVal q f hfc
  have hEI := FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF f hfc
  have hE0 := FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF (0 : ℂ → ℝ) continuous_zero
  have hIII := FirstPassS11aa.ae_weylScaling_universe h𝔇 hGFF
  have hFI := ((hFA α hα Ω P hC hcirc) hGFF hγ0 hγ2 hα 𝔇 h𝔇).1
  filter_upwards [hadd, hqΦ, hEI, hE0, hIII, hFI] with ω hωB hωq hωE hωE0 hωIII hωF
  rw [addFunPairing_zero_fun] at hωE0
  have hD0 : IsEuclideanLengthMetric (𝔇 (hC ω)) := hωE0
  have hFl : IsEuclideanLengthMetric
      (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal) := hωF.2
  have hFfin : ∀ x y, ENNReal.ofReal ((weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y :=
    fun x y => ENNReal.ofReal_toReal (hωF.1 x y).ne
  -- locality: the internal metric of `𝔇 (h^ℂ + f)` on `D` is that of the Weyl scaling by `-α log|·|`
  have hloc : ∀ x y, internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) x y =
      internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal)
        (ball c r) x y :=
    fun x y => hD0.internalMetric_weylScaling_eq_of_eqOn hωE hFl ξ f (fun z => -α * Real.log ‖z‖)
      (fun x y => hωIII f hfc x y) hFfin isOpen_ball hfloc x y
  -- the identity on `Q` extends to `D × D` by continuity of both sides
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) p.1 p.2)
      (ball c r ×ˢ ball c r) :=
    hωE.continuousOn_internalMetric_pair (fun x y => euclidLength_nonneg hωE x y) isOpen_ball
  have hcR : Continuous (fun p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) p.1.1 p.1.2) :=
    hcont.comp_continuous continuous_subtype_val (fun p => p.2)
  have hcL : Continuous (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) f)) q)) :=
    ENNReal.continuous_ofReal.comp (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) f))).continuous
  have hcR' : Continuous (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) f) ρ)) *
        internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) q.1.1 q.1.2) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hcR
  have hext : (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) f)) q)) =
      (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) f) ρ)) *
        internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c r) q.1.1 q.1.2) := by
    refine Continuous.ext_on hQd hcL hcR' fun q hq => ?_
    have h := Set.mem_iInter₂.1 hωB q hq
    change ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) f)) q) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) f) ρ)) *
        Φ q (addFunPairing (hC ω) f) at h
    rw [hωq q hq] at h
    exact h
  have hobs : localMeanZeroObs α (ball c r) (hC ω) = localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) f) :=
    funext fun φ => localMeanZeroObs_eq_addFunPairing α hfloc (hC ω) φ
  have hconst : fieldPairing 0 (addFunPairing (hC ω) f) ρ = fieldPairing α (hC ω) ρ := by
    have hpt : ∀ x, f x * ρ x = -α * (ρ x * Real.log ‖x‖) := by
      intro x
      by_cases hx : x ∈ ball c r
      · rw [hfloc x hx]; ring
      · have hρ0 : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hρT.2.2 h))
        simp [hρ0]
    have hint : ∫ x, f x * ρ x = -α * ∫ x, ρ x * Real.log ‖x‖ := by
      rw [← integral_const_mul]
      congr 1
      funext x
      exact hpt x
    unfold fieldPairing addFunPairing
    rw [hint]
    ring
  intro p
  rw [hobs]
  have hp := congrFun hext p
  rw [hp, hloc p.1.1 p.1.2, hconst]

end HarmonicBalls
