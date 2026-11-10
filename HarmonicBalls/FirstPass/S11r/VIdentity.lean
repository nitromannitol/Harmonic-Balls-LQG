import HarmonicBalls.FirstPass.S11r.UnrootedFixed
import HarmonicBalls.FirstPass.S11r.LogSingularCutoff
import HarmonicBalls.FirstPass.S11r.RootedObsShift

/-!
# The disk identity for a continuous shift (fp-S11r part (b), step (d); owner n2)

Step (d) of the rooted identity (20) (CHATGPT-n3-B1-B2.md section 4.1-4.2, identities (22) and (26)). For a disk
`V = ball c r` with `0 ∉ closedBall c r`, let `M` and `ρ` be the decoder and bump of the corrected frozen input
`LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` for `V` and the fixed metric `𝔇`. The proof of
`unrooted_identity_fixedMetric` (UnrootedFixed.lean:75) uses the α-cutoff only through the Cameron-Martin shift and
the locality of the internal metric. Here the shift is an arbitrary smooth, compactly supported `g` with zero circle
average at `0` on the unit circle; the conclusion is the identity for the shifted field `h^ℂ + g` with the internal
metric of `𝔇 (h^ℂ + g)` itself, so no Weyl-scaling length property is needed. The rooted case applies it to the
cutoff `g_z = -α log|·| - γ log|·-z|` on `V` (z outside the closure of `V`), see `campbellReferenceObs_eq_addFunPairing`.

Inputs (named hypotheses): the α = 0 identity of the decoder (`hid`, the α = 0 case of `hB1`), the Cameron-Martin
transfer `CameronMartinGFFMutualAbsCont`, and the measurable internal metric `LQGInternalMetricWeylAeMeasurableFrozen`
(Mb; already a hypothesis of `unrooted_identity_fixedMetric`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **(d) for a continuous shift.** For a fixed metric `𝔇`, a disk `V = ball c r` and its decoder `(ρ, M)` with the
α = 0 identity `hid`, and a smooth compactly supported `g` with zero circle average, almost surely the decoder of the
mean-zero observation of `h^ℂ + g` equals `e^{-ξ ⟨h^ℂ + g, ρ⟩}` times the internal metric of `𝔇 (h^ℂ + g)` on `V`,
at every pair of endpoints in `V × V`. -/
theorem vIdentity_of_shift {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c : ℂ} {r : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (ρ : ℂ → ℝ) (hρT : IsTestFunction (ball c r) ρ)
    (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ)
    (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
        ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
          ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
            internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (g : ℂ → ℝ) (hgsm : ContDiff ℝ (⊤ : ℕ∞) g) (hgcomp : HasCompactSupport g)
    (hgcirc : Real.circleAverage g 0 1 = 0) :
    ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g)) p) =
        ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) g) ρ)) *
          internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) p.1.1 p.1.2 := by
  have hQ0 : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hBopen : IsOpen (ball c r) := isOpen_ball
  -- countable dense set of endpoints in `V × V`
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ))
  -- measurable versions of the internal metric (frozen input, `α₀ = 0`)
  have hΦ : ∀ q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞,
      Measurable[distributionMeasurableSpace] Φ ∧ ∀ k : ℂ → ℝ, Continuous k → ∀ᵐ ω ∂P,
        Φ (addFunPairing (hC ω) k) = internalMetric
          (fun x y => (weylScaling (𝔇 (addFunPairing (hC ω) k)) ξ (fun z => -(0 : ℝ) * Real.log ‖z‖) x y).toReal)
          (ball c r) q.1.1 q.1.2 := fun q =>
    hPhi γ ξ 0 Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hQ0 h𝔇 (ball c r) hBopen q.1.1 q.1.2
  choose Φ hΦm hΦid using hΦ
  -- the value of `Φ_q` on a shifted field is the internal metric of that field
  have hPhiVal : ∀ (q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ))) (k : ℂ → ℝ), Continuous k → ∀ᵐ ω ∂P,
      Φ q (addFunPairing (hC ω) k) = internalMetric (𝔇 (addFunPairing (hC ω) k)) (ball c r) q.1.1 q.1.2 := by
    intro q k hk
    filter_upwards [hΦid q k hk, FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF k hk] with ω h1 h2
    rw [h1]
    have hfun : (fun x y => (weylScaling (𝔇 (addFunPairing (hC ω) k)) ξ
        (fun z => -(0 : ℝ) * Real.log ‖z‖) x y).toReal) = 𝔇 (addFunPairing (hC ω) k) := by
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
  -- a.s. `h^ℂ ∈ B`: the α = 0 identity at `h^ℂ` and the Φ-values at `h^ℂ`
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
  -- Cameron-Martin: `h^ℂ + g ∈ B` almost surely
  have hadd := ae_mem_addFunPairing_of_ae_mem hCM P hC hcirc g hGFF hgsm hgcomp hgcirc B hBm hmem
  have hqΦ : ∀ᵐ ω ∂P, ∀ q ∈ Q, Φ q (addFunPairing (hC ω) g) =
      internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) q.1.1 q.1.2 :=
    (ae_ball_iff hQc).2 fun q _ => hPhiVal q g hgsm.continuous
  have hEI := FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF g hgsm.continuous
  filter_upwards [hadd, hqΦ, hEI] with ω hωB hωq hωE
  -- the identity on `Q` extends to `V × V` by continuity of both sides
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) p.1 p.2)
      (ball c r ×ˢ ball c r) :=
    hωE.continuousOn_internalMetric_pair (fun x y => euclidLength_nonneg hωE x y) isOpen_ball
  have hcR : Continuous (fun p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) p.1.1 p.1.2) :=
    hcont.comp_continuous continuous_subtype_val (fun p => p.2)
  have hcL : Continuous (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g)) q)) :=
    ENNReal.continuous_ofReal.comp (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g))).continuous
  have hcR' : Continuous (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) g) ρ)) *
        internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) q.1.1 q.1.2) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hcR
  have hext : (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g)) q)) =
      (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) g) ρ)) *
        internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) q.1.1 q.1.2) := by
    refine Continuous.ext_on hQd hcL hcR' fun q hq => ?_
    have h := Set.mem_iInter₂.1 hωB q hq
    change ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g)) q) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) g) ρ)) *
        Φ q (addFunPairing (hC ω) g) at h
    rw [hωq q hq] at h
    exact h
  intro p
  exact congrFun hext p

/-- **Rooted cutoff.** For a disk `V = ball c r` with `0 ∉ closedBall c r` and a root `z` with `closedBall c R ⊆ ball 0 1`,
`r < R < dist z c`, there is a smooth compactly supported `g` with zero circle average at `0` on the unit circle that equals
`-α log|·| - γ log|·-z|` on `V`: the sum of the α-cutoff `exists_negLog_cutoff` and the log-singular cutoff
`exists_log_sing_cutoff` with `β = γ`, `p = z`. -/
theorem exists_rooted_cutoff (α γ : ℝ) {c z : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hpR : R < dist z c)
    (hU : closedBall c R ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∃ g : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ Real.circleAverage g 0 1 = 0 ∧
      ∀ x ∈ ball c r, g x = -α * Real.log ‖x‖ - γ * Real.log ‖x - z‖ := by
  obtain ⟨f1, hf1s, hf1c, hf1a, hf1v⟩ := exists_negLog_cutoff α hr h0
  obtain ⟨f2, hf2s, hf2c, hf2a, -, hf2v⟩ := exists_log_sing_cutoff γ hr hrR hpR hU
  refine ⟨fun x => f1 x + f2 x, hf1s.add hf2s, hf1c.add hf2c, ?_, fun x hx => ?_⟩
  · rw [Real.circleAverage_fun_add (ContinuousOn.circleIntegrable zero_le_one hf1s.continuous.continuousOn)
      (ContinuousOn.circleIntegrable zero_le_one hf2s.continuous.continuousOn), hf1a, hf2a, add_zero]
  · simp only
    rw [hf1v x hx, hf2v x hx]
    ring

/-- **(d) for the rooted field.** Let `V = ball c r`, `0 ∉ closedBall c r`, and let `g` be a smooth compactly supported
function with zero circle average which equals `-α log|·| - γ log|·-z|` on `V` (`exists_rooted_cutoff`), with `z ∉ V`
and `V ⊆ ball 0 1`. Then almost surely the decoder `M` of `V`, applied to the rooted Campbell observation
`campbellReferenceObs γ α V (h^ℂ) z` of the field rooted at `z`, equals `e^{-ξ ⟨h^ℂ + g, ρ⟩}` times the internal metric of
`𝔇 (h^ℂ + g)` on `V`, at every pair of endpoints in `V × V`. The metric side is the internal metric of the shifted field;
its identification with the Weyl-scaled metric of the rooted field is a separate step (locality needs the length property of
that metric, which is not part of the frozen inputs). -/
theorem vIdentity_rooted {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c z : ℂ} {r : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (ρ : ℂ → ℝ) (hρT : IsTestFunction (ball c r) ρ)
    (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ)
    (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
        ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
          ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
            internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2)
    {R : ℝ} (hrR : r < R) (hpR : R < dist z c)
    (hU : closedBall c R ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    (g : ℂ → ℝ) (hgsm : ContDiff ℝ (⊤ : ℕ∞) g) (hgcomp : HasCompactSupport g)
    (hgcirc : Real.circleAverage g 0 1 = 0)
    (hgz : ∀ x ∈ ball c r, g x = -α * Real.log ‖x‖ - γ * Real.log ‖x - z‖)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (campbellReferenceObs γ α (ball c r) (hC ω) z).2 p) =
        ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) g) ρ)) *
          internalMetric (𝔇 (addFunPairing (hC ω) g)) (ball c r) p.1.1 p.1.2 := by
  have hV1 : ∀ x ∈ ball c r, ‖x‖ < 1 := fun x hx => by
    have hxR : x ∈ closedBall c R := by
      rw [mem_ball] at hx
      rw [mem_closedBall]
      linarith [dist_comm x c]
    have := hU hxR
    rwa [mem_ball_zero_iff] at this
  have hV0 : (0 : ℂ) ∉ ball c r := fun h => h0 (ball_subset_closedBall h)
  have hzV : z ∉ ball c r := fun hz => by
    rw [mem_ball] at hz
    linarith [dist_comm z c]
  have hobs : ∀ (T : (ℂ → ℝ) → ℝ) (φ : {φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0}),
      (campbellReferenceObs γ α (ball c r) T z).2 φ = localMeanZeroObs 0 (ball c r) (addFunPairing T g) φ := by
    intro T φ
    exact campbellReferenceObs_eq_addFunPairing T hV1 hV0 hzV hgz φ
  have key := vIdentity_of_shift hγ0 hγ2 h𝔇 hPhi hCM ρ hρT M hMm hid Ω P hC hcirc hGFF g hgsm hgcomp hgcirc
  filter_upwards [key] with ω hω
  have hm : (campbellReferenceObs γ α (ball c r) (hC ω) z).2 =
      localMeanZeroObs 0 (ball c r) (addFunPairing (hC ω) g) :=
    funext fun φ => hobs (hC ω) φ
  intro p
  rw [hm]
  exact hω p

end HarmonicBalls

#print axioms HarmonicBalls.vIdentity_rooted
#print axioms HarmonicBalls.vIdentity_of_shift
