import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11r.FrozenMetricReplacement
import HarmonicBalls.FirstPass.S11r.CMShift
import HarmonicBalls.FirstPass.S11r.Consistency
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11j.CertificateTransfer
import HarmonicBalls.Steps.Sec11.WeylLocality
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11aa

/-!
# The unrooted identity (18) for a fixed metric assignment (fp-S11r part (b) P3, owner n2)

For a fixed LQG metric `𝔇` (`IsLQGMetric γ ξ 𝔇`), a disk `D = ball c r` with `0 ∉ closedBall c r`, and the
decoder `M` and bump `ρ` of the corrected frozen input `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen`, the
identity (18) of CHATGPT-n3-B1-B2.md section 4.1 holds for every `α < Q_γ`: almost surely there is a positive constant
`b` with `M (obs_D h^α) = b · D_{h^α}(·,·;D)` on `D × D`, where `D_{h^α}` is the internal metric of the Weyl scaling
`weylScaling (𝔇 (h^ℂ)) ξ (-α log|·|)`.

Proof (Cameron-Martin, the paper's sentence "a smooth compactly supported function can equal `-α log|·|` near `D̄`"):
1. `f = χ · (-α log|·|)` (`exists_negLog_cutoff`) is smooth with compact support and equals `-α log|·|` on `D`.
2. The B-set `B = {g | ∀ q ∈ Q, M(obs_D g) q = e^{-ξ⟨g,ρ⟩} Φ_q(g)}` over a countable dense `Q ⊆ D × D`, with
   measurable `Φ_q` (`LQGInternalMetricWeylAeMeasurableFrozen` with `α₀ = 0`); almost surely `h^ℂ ∈ B` by the
   corrected B1 identity; Cameron-Martin (`ae_mem_addFunPairing_of_ae_mem`) gives `h^ℂ + f ∈ B` almost surely.
3. Continuity of both sides in the endpoint (`continuousOn_internalMetric_pair`) extends the identity from `Q` to `D × D`.
4. The observation of `h^α` is that of `h^ℂ + f` (`localMeanZeroObs_eq_addFunPairing`), and the internal metric of
   `𝔇 (h^ℂ + f)` on `D` is that of the Weyl scaling by `-α log|·|` on `D` (`internalMetric_weylScaling_eq_of_eqOn`).

Axioms I and III at universe `u` are `FirstPassS11aa.ae_isEuclideanLengthMetric_universe` and `FirstPassS11aa.ae_weylScaling_universe` (task fp-S11aa, commit b44b873). The length
property of `h^α` is item I of the Proposed `LQGMetricFieldAxioms` (Proposed/LQG.lean, pending source-check).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- A Euclidean length metric is nonnegative (symmetry, triangle inequality and `D x x = 0`). -/
theorem euclidLength_nonneg {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (x y : ℂ) : 0 ≤ E x y := by
  have h0 := hE.self_eq_zero x
  have h1 := hE.triangle x y x
  rw [hE.symm y x] at h1
  linarith

theorem addFunPairing_zero_fun (T : (ℂ → ℝ) → ℝ) : addFunPairing T (0 : ℂ → ℝ) = T := by
  funext φ
  simp [addFunPairing]

/-- Evaluation at a test function is measurable for the distribution σ-algebra. -/
theorem measurable_distribution_eval {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => T φ := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  exact le_iSup₂_of_le (f := fun (φ : ℂ → ℝ) (_ : IsTestFunction univ φ) =>
    MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ) inferInstance) φ hφ le_rfl

theorem measurable_fieldPairing_zero {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => fieldPairing 0 T φ := by
  unfold fieldPairing
  exact (measurable_distribution_eval hφ).sub_const _

/-- The mean-zero observation of a distribution on `D` is measurable for the distribution σ-algebra (`α₀ = 0`). -/
theorem measurable_localMeanZeroObs_zero (D : Set ℂ) :
    Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => localMeanZeroObs 0 D T := by
  let _inst : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
  refine measurable_pi_iff.2 fun φ => ?_
  exact measurable_fieldPairing_zero ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩

/-- **(18) for a fixed metric.** Given the corrected frozen decoder `hB1` for `𝔇`, the Cameron-Martin and measurability
inputs, and the named universe-`u` shift axioms, the decoder `M` of `𝔇` satisfies (18) for every `α < Q_γ`. -/
theorem unrooted_identity_fixedMetric
    {γ ξ : ℝ} (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ,
      Measurable M ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
          ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
            ENNReal.ofReal (M (localMeanZeroObs α (ball c r) (hC ω)) p) =
              ENNReal.ofReal b * internalMetric
                (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal)
                (ball c r) p.1.1 p.1.2 := by
  obtain ⟨ρ, M, hρT, -, hMm, hid⟩ := hB1 γ ξ c r hγ0 hγ2 hr h0 𝔇 h𝔇
  refine ⟨M, hMm, fun α hα Ω _ P _ hC hcirc hGFF => ?_⟩
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
  -- a.s. `h^ℂ ∈ B`: the corrected B1 identity at `h^ℂ` and the Φ-values at `h^ℂ`
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
  refine ⟨Real.exp (-ξ * fieldPairing 0 (addFunPairing (hC ω) f) ρ), Real.exp_pos _, fun p => ?_⟩
  rw [hobs]
  have hp := congrFun hext p
  rw [hp, hloc p.1.1 p.1.2]

end HarmonicBalls
