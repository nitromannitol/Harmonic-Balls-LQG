import HarmonicBalls.FirstPass.S11m.Corrected11_12
import HarmonicBalls.FirstPass.S11m.DecodedLocal
import HarmonicBalls.FirstPass.S11m.DecodedMass
import HarmonicBalls.FirstPass.S11m.DenseInf
import HarmonicBalls.FirstPass.S11m.MeasureDecoderBall
import HarmonicBalls.FirstPass.S11m.LocalInclusion
import HarmonicBalls.FirstPass.S11m.LocalRule
import HarmonicBalls.FirstPass.S11ah.LengthScale
import HarmonicBalls.FirstPass.S11am
import HarmonicBalls.FirstPass.S11ax
import HarmonicBalls.FirstPass.S11an
import HarmonicBalls.FirstPass.S11ay
import HarmonicBalls.FirstPass.S11ak.Seven
import HarmonicBalls.FirstPass.S11ak.BaseComparison

/-!
# Assembly of the local certificate `PinchLocalCertificateStmt` (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-lh-R4-R5.md` §R5b.3 (order of choices) and `CHATGPT-z4-11-12-local-certificate.md`
(decoded rule, eq. (17)). For fixed geometry, `γ`, `ξ`, `M`:

* if some `IsLQGMetric γ ξ 𝔇₀` exists, fix one, take the punctured-ball metric decoder `Ψ` of it
  (`S11ak.metricDecoder_punctured_ball_seven`), the measure decoder `Φμ` of `B₇`
  (`measureDecoder_ball_zero`), countable dense point sets `I`, and
  `E := decodedPinchRuleBall I (decodedFamily Ψ) (decGreen Φμ) (decMassU Φμ U) M`;
* otherwise `E := ∅`, and every model is excluded by its own `IsLQGMetricOfField`.

For a model, the base comparison `LQGMetricBaseComparisonStmt` gives `𝔇 = b₁ 𝔇₀` a.s., hence the target metric is
`b₁` times the reference Weyl metric; the decoded family is `b₀` times the reference internal metric; so the decoded
values are a.s. `(b₀/b₁)` times the internal metric of `D ω`. The masses are a.s. `c` times the masses of `μ ω`.
`decodedPinchRule_iff_ball` then identifies membership with the local rule (plus finiteness, which holds a.s.).
Positivity is the positive probability of the local events (`S11an.pinchLocal_events_pos_discharged`), which lie
a.s. in `E`; the a.s. implication `E ⊆ rule ⊆ auxiliary events` uses the local-to-auxiliary inclusions.

Named inputs (all frozen Props or Proposed/External statements, none about this paper's clusters): see the
hypotheses of `pinchLocalCertificate_of_inputs`.
-/

namespace HarmonicBalls.S11m.CertificateAssembly

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

open HarmonicBalls.S11ax HarmonicBalls.S11ay

/-! ### Elementary geometry of the bounded domains -/

lemma caAnnulusSubBall {r₁ r₂ R : ℝ} (h : r₂ ≤ R) : annulus (0 : ℂ) r₁ r₂ ⊆ ball (0 : ℂ) R := by
  intro z hz
  unfold annulus at hz
  exact ball_subset_ball h hz.1

lemma caZeroNotMemAnnulus {r₁ r₂ : ℝ} (hr : 0 ≤ r₁) : (0 : ℂ) ∉ annulus (0 : ℂ) r₁ r₂ := by
  intro hz
  unfold annulus at hz
  exact hz.2 (mem_closedBall_self hr)

lemma caZeroNotMemOf {O : Set ℂ} {r : ℝ} (h : O ⊆ annulus (0 : ℂ) 1 r) : (0 : ℂ) ∉ O :=
  fun h0 => caZeroNotMemAnnulus (r₁ := 1) zero_le_one (h h0)

lemma caSphereSubBall {r R : ℝ} (h : r < R) : sphere (0 : ℂ) r ⊆ ball (0 : ℂ) R := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  rw [mem_ball_zero_iff, hz]
  exact h

lemma caIsOpenPunct : IsOpen (ball (0 : ℂ) 7 \ {0}) :=
  isOpen_ball.sdiff isClosed_singleton

lemma caIsConnectedPunct : IsConnected (ball (0 : ℂ) 7 \ {0}) :=
  ⟨⟨1, by simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_singleton_iff, norm_one]; norm_num⟩,
    HarmonicBalls.S11m.MeasureDecoderBall.isPreconnected_ball_diff_zero 7⟩

lemma caIsConnBall {r : ℝ} (hr : 0 < r) : IsConnected (ball (0 : ℂ) r) :=
  (convex_ball (0 : ℂ) r).isConnected ⟨0, mem_ball_self hr⟩

lemma caPinchOmegaSubBall {W Q : Set ℂ} {δ : ℝ} : pinchOmegaGeom W Q δ ⊆ ball (0 : ℂ) 7 := by
  unfold pinchOmegaGeom
  intro z hz
  exact (connectedComponentIn_subset _ _ hz).1

lemma caIsOpenPinchOmega {W Q : Set ℂ} {δ : ℝ} : IsOpen (pinchOmegaGeom W Q δ) := by
  unfold pinchOmegaGeom
  exact (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)).connectedComponentIn

lemma caConnPinchOmega {W Q : Set ℂ} {δ : ℝ} (h0 : (0 : ℂ) ∈ pinchOmegaGeom W Q δ) :
    IsConnected (pinchOmegaGeom W Q δ) := by
  unfold pinchOmegaGeom at h0 ⊢
  exact isConnected_connectedComponentIn_iff.mpr (connectedComponentIn_nonempty_iff.mp ⟨0, h0⟩)

/-- The thickened `T`-domain of the local events lies in the annulus `1 < |z| < 6` (buffer clause `buffer_T`). -/
lemma caThickTSub {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    thickening δ (closure (T \ thickening (3 * δ) W)) ⊆ annulus (0 : ℂ) 1 6 := by
  have hδ := hgeo.delta_pos
  exact ((thickening_subset_of_subset δ (closure_mono sdiff_subset)).trans
    (thickening_mono (show δ ≤ 10 * δ by linarith) _)).trans (subset_closure.trans hgeo.buffer_T)

/-- The thickened `V`-domain lies in `W ⊆ annulus 0 1 2` (buffer clause `buffer_V`). -/
lemma caThickVSub {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    thickening δ (closure V) ⊆ annulus (0 : ℂ) 1 2 := by
  have hδ := hgeo.delta_pos
  exact ((thickening_mono (show δ ≤ 10 * δ by linarith) _).trans
    (subset_closure.trans hgeo.buffer_V)).trans hgeo.W_subset

/-- The thickened difference `B_{3δ}W \ V` lies in `T ∩ annulus 0 1 2` (buffer clause `buffer_W`). -/
lemma caThickCTSub {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    thickening δ (closure (thickening (3 * δ) W \ V)) ⊆ annulus (0 : ℂ) 1 2 := by
  have hδ := hgeo.delta_pos
  have h1 : thickening δ (closure (thickening (3 * δ) W \ V)) ⊆ thickening (10 * δ) W := by
    refine (thickening_subset_of_subset δ (closure_mono sdiff_subset)).trans ?_
    rw [thickening_closure]
    refine (thickening_thickening_subset δ (3 * δ) W).trans ?_
    exact thickening_mono (show δ + 3 * δ ≤ 10 * δ by linarith) W
  exact (h1.trans ((thickening_subset_of_subset (10 * δ) subset_closure).trans
    (subset_closure.trans hgeo.buffer_W))).trans inter_subset_right

/-- The set `U` of the geometry is bounded. -/
lemma caBoundedU {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    Bornology.IsBounded U :=
  (isBounded_ball (x := (0 : ℂ)) (r := 2)).subset (hgeo.U_subset.trans (caAnnulusSubBall le_rfl))

/-- Countable dense pinch point sets (`PinchCountSets`), from separability of subsets of `ℂ`. -/
lemma caExistsPinchCountSets (V W T Q' Q : Set ℂ) (δ : ℝ) :
    Nonempty (HarmonicBalls.S11am.PinchCountSets V W T Q' Q δ) := by
  have h : ∀ A : Set ℂ, ∃ S : Set ℂ, HarmonicBalls.S11am.IsCountDenseIn S A := fun A => by
    obtain ⟨C, hCA, hCc, hAC⟩ := exists_countable_dense_subset_of_secondCountable A
    exact ⟨C, hCA, hAC, hCc⟩
  obtain ⟨sp, hsp⟩ := h (sphere (0 : ℂ) 5)
  obtain ⟨qp, hqp⟩ := h (closure Q')
  obtain ⟨fp, hfp⟩ := h (frontier Q)
  obtain ⟨cp, hcp⟩ := h (closure (T \ thickening (3 * δ) W))
  obtain ⟨ep, hep⟩ := h (sphere (0 : ℂ) δ)
  obtain ⟨s2, hs2⟩ := h (sphere (0 : ℂ) δ)
  obtain ⟨s3, hs3⟩ := h (sphere (0 : ℂ) (2 * δ))
  obtain ⟨cv, hcv⟩ := h (closure V)
  obtain ⟨t2, ht2⟩ := h (sphere (0 : ℂ) (2 * δ))
  obtain ⟨t3, ht3⟩ := h (sphere (0 : ℂ) (3 * δ))
  obtain ⟨ct, hct⟩ := h (closure (thickening (3 * δ) W \ V))
  exact ⟨⟨sp, hsp, qp, hqp, fp, hfp, cp, hcp, ep, hep, s2, hs2, s3, hs3, cv, hcv, t2, ht2, t3, ht3, ct, hct⟩⟩

/-! ### The decoded family and its identification -/

/-- The decoded internal distance on the domain `O`: the decoder `Ψ ℓ` on the punctured ball `B₇ \ {0}`
(`S11m.decInt` with the radius `localEps`). -/
noncomputable def decodedFamily {X : Type*} (Ψ : X → ℂ → ℂ → ℝ) (O : Set ℂ) (x y : ℂ) (ℓ : X) : ℝ≥0∞ :=
  HarmonicBalls.S11m.decInt (ball (0 : ℂ) 7 \ {0}) (fun v w => (ENNReal.ofReal (Ψ ℓ v w)).toReal)
    HarmonicBalls.S11m.localEps O x y

lemma measurable_decodedFamily {X : Type*} [MeasurableSpace X] (Ψ : X → ℂ → ℂ → ℝ)
    (hΨ : ∀ a b : ℂ, Measurable fun ℓ => Ψ ℓ a b) (O : Set ℂ) (x y : ℂ) :
    Measurable fun ℓ => decodedFamily Ψ O x y ℓ :=
  HarmonicBalls.S11m.measurable_decodedVal (ball (0 : ℂ) 7 \ {0}) hΨ O x y

/-- **Decoded values on the countable sets.** If on every admissible open domain `O ⊆ B₇` the decoded family is
`b₀` times the internal metric of `Dw`, and `D = b₁ Dw`, then the decoded values are `b₀ / b₁` times the internal
metric of `D` on the domains of `DecodesOnSetsBall`. -/
lemma caDecodesOfFamily {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hOmega : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (I : HarmonicBalls.S11am.PinchCountSets V W T Q' Q δ) {X : Type*} (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X)
    {Dw D : ℂ → ℂ → ℝ} {b₀ b₁ : ℝ} (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hD : ∀ x y, D x y = b₁ * Dw x y)
    (hfam : ∀ O : Set ℂ, IsOpen O → O \ {0} ⊆ ball (0 : ℂ) 7 \ {0} → ((0 : ℂ) ∈ O → IsConnected O) →
      ∀ x ∈ O, ∀ y ∈ O, Φ O x y ℓ = ENNReal.ofReal b₀ * internalMetric Dw O x y) :
    HarmonicBalls.S11ax.DecodesOnSetsBall I Φ D (b₀ / b₁) ℓ := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hδ7 : 4 * δ ≤ 7 := by linarith [hgeo.delta_lt]
  have hδ4 : ball (0 : ℂ) (4 * δ) ⊆ ball (0 : ℂ) 7 := ball_subset_ball hδ7
  have hDfun : D = fun x y => b₁ * Dw x y := funext fun x => funext fun y => hD x y
  have hint : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal (b₀ / b₁) * internalMetric D O x y =
      ENNReal.ofReal b₀ * internalMetric Dw O x y := by
    intro O x y
    rw [hDfun, FirstPassS11ah.internalMetric_const_mul hb₁ Dw O x y, ← mul_assoc,
      ← ENNReal.ofReal_mul (div_pos hb₀ hb₁).le, div_mul_cancel₀ b₀ hb₁.ne']
  have key : ∀ O : Set ℂ, IsOpen O → O ⊆ ball (0 : ℂ) 7 → ((0 : ℂ) ∈ O → IsConnected O) →
      ∀ x ∈ O, ∀ y ∈ O, Φ O x y ℓ = ENNReal.ofReal (b₀ / b₁) * internalMetric D O x y := by
    intro O hO hsub hc x hx y hy
    rw [hint]
    exact hfam O hO (sdiff_subset_sdiff_left hsub) hc x hx y hy
  have hO6 : ball (0 : ℂ) 6 ⊆ ball (0 : ℂ) 7 := ball_subset_ball (by norm_num)
  have hQc : closure Q' ⊆ annulus (0 : ℂ) 4 5 :=
    (hgeo.closure_Q'_subset_Q.trans (subset_closure.trans hgeo.closure_Q_subset)).trans sdiff_subset
  have hQf : frontier Q ⊆ annulus (0 : ℂ) 4 5 :=
    frontier_subset_closure.trans (hgeo.closure_Q_subset.trans sdiff_subset)
  have h0Om : (0 : ℂ) ∈ pinchOmegaGeom W Q δ := hOmega (mem_insert _ _)
  refine ⟨fun y hy => ?_, fun p hp q hq => ?_, fun x hx y hy => ?_, fun p hp => ?_,
    fun x hx y hy => ?_, fun p hp q hq => ?_, fun x hx y hy => ?_, fun p hp q hq => ?_⟩
  · have hyO : y ∈ pinchOmegaGeom W Q δ := hOmega (subset_insert _ _ (I.sp_dense.1 hy))
    exact key _ caIsOpenPinchOmega caPinchOmegaSubBall (fun _ => caConnPinchOmega h0Om) 0 h0Om y hyO
  · exact key (ball (0 : ℂ) 6) isOpen_ball hO6 (fun _ => caIsConnBall (by norm_num)) p
      (caAnnulusSubBall (R := 6) (by norm_num) (hQc (I.qp_dense.1 hp))) q
      (caAnnulusSubBall (R := 6) (by norm_num) (hQf (I.fp_dense.1 hq)))
  · exact key (thickening δ (closure (T \ thickening (3 * δ) W))) isOpen_thickening
      ((caThickTSub hgeo).trans (caAnnulusSubBall (R := 7) (by norm_num)))
      (fun h0 => absurd h0 (caZeroNotMemOf (caThickTSub hgeo))) x
      (self_subset_thickening hδ _ (I.cp_dense.1 hx)) y (self_subset_thickening hδ _ (I.cp_dense.1 hy))
  · exact key (ball (0 : ℂ) (4 * δ)) isOpen_ball hδ4 (fun _ => caIsConnBall (by linarith)) 0
      (mem_ball_self (by linarith)) p (caSphereSubBall (by linarith) (I.ep_dense.1 hp))
  · exact key (thickening δ (closure V)) isOpen_thickening
      ((caThickVSub hgeo).trans (caAnnulusSubBall (R := 7) (by norm_num)))
      (fun h0 => absurd h0 (caZeroNotMemOf (caThickVSub hgeo))) x
      (self_subset_thickening hδ _ (I.cv_dense.1 hx)) y (self_subset_thickening hδ _ (I.cv_dense.1 hy))
  · exact key (ball (0 : ℂ) (4 * δ)) isOpen_ball hδ4 (fun _ => caIsConnBall (by linarith)) p
      (caSphereSubBall (by linarith) (I.s2_dense.1 hp)) q (caSphereSubBall (by linarith) (I.s3_dense.1 hq))
  · exact key (thickening δ (closure (thickening (3 * δ) W \ V))) isOpen_thickening
      ((caThickCTSub hgeo).trans (caAnnulusSubBall (R := 7) (by norm_num)))
      (fun h0 => absurd h0 (caZeroNotMemOf (caThickCTSub hgeo))) x
      (self_subset_thickening hδ _ (I.ct_dense.1 hx)) y (self_subset_thickening hδ _ (I.ct_dense.1 hy))
  · exact key (ball (0 : ℂ) (4 * δ)) isOpen_ball hδ4 (fun _ => caIsConnBall (by linarith)) p
      (caSphereSubBall (by linarith) (I.t2_dense.1 hp)) q (caSphereSubBall (by linarith) (I.t3_dense.1 hq))

/-- Weyl scaling of a constant multiple: if `Mt = b M₀` and `D` has `ofReal (D x y) = weylScaling Mt ξ f x y`, then
`D x y = b · (weylScaling M₀ ξ f x y).toReal` (`IsEuclideanLengthMetric.weylScaling_const_mul`). -/
lemma caWeylRel {M₀ Mt D : ℂ → ℂ → ℝ} (hM₀ : IsEuclideanLengthMetric M₀) {b : ℝ} (hb : 0 < b)
    (hMt : ∀ x y, Mt x y = b * M₀ x y) {ξ : ℝ} {f : ℂ → ℝ}
    (hD : ∀ x y, 0 ≤ D x y ∧ ENNReal.ofReal (D x y) = weylScaling Mt ξ f x y) :
    ∀ x y, D x y = b * (weylScaling M₀ ξ f x y).toReal := by
  intro x y
  have hfun : Mt = fun x y => b * M₀ x y := funext fun x => funext fun y => hMt x y
  have h1 : weylScaling Mt ξ f x y = ENNReal.ofReal b * weylScaling M₀ ξ f x y := by
    rw [hfun]
    exact IsEuclideanLengthMetric.weylScaling_const_mul hM₀ hb ξ f x y
  have h2 := congrArg ENNReal.toReal ((hD x y).2.trans h1)
  rw [ENNReal.toReal_ofReal (hD x y).1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le] at h2
  exact h2

/-- **Local certificate `PinchLocalCertificateStmt` from named inputs.** The decoders, the base comparison, the
positivity and the finiteness enter only as the hypotheses below (frozen Props or Proposed/External statements):
* `hAx`, `hLen`, `hN2`, `hBase`, `hμW`: the metric field axioms, the length property of the base metric, the
  local metric replacement (n2), the base comparison (z6, `S11ak.LQGMetricBaseComparisonStmt`), and the Weyl scaling of
  the measure (Proposed, Fact 2.1 III);
* `hLoc`, `hNonat`, `hFull`: the measure decoder inputs of `measureDecoder_ball_zero`;
* `hgrowth`: the volume growth input of the finiteness of `annulusGreenPotentialSup`;
* `hfr`, ..., `hS`: the inputs of the positivity `S11an.pinchLocal_events_pos_discharged` (z3). -/
theorem pinchLocalCertificate_of_inputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hBase : HarmonicBalls.S11ak.LQGMetricBaseComparisonStmt.{u})
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hFull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u}) :
    PinchLocalCertificateStmt.{u} := by
  intro U V W T Q' Q δ hgeo hOmega γ ξ hγ hγ2 hξ M hM
  have hΩS : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ := by
    rw [← Set.insert_eq]
    exact hOmega
  have hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := (subset_insert _ _).trans hOmega
  by_cases hex : ∃ 𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, HarmonicBalls.IsLQGMetric γ ξ 𝔇₀
  · obtain ⟨𝔇₀, h𝔇₀⟩ := hex
    obtain ⟨Ψ, hΨm, hΨ⟩ := HarmonicBalls.S11ak.metricDecoder_punctured_ball_seven hAx γ ξ hγ hγ2 hξ
      (hN2 γ ξ hγ hγ2 hξ) 𝔇₀ h𝔇₀
    obtain ⟨Ψc, hΨc⟩ : ∃ Ψc : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ → ℂ → ℝ,
        ∀ ℓ v w, Ψc ℓ v w = Ψ ℓ (v, w) := ⟨fun ℓ v w => Ψ ℓ (v, w), fun _ _ _ => rfl⟩
    have hΨcm : ∀ a b : ℂ, Measurable fun ℓ => Ψc ℓ a b := fun a b => by
      simp only [hΨc]
      exact hΨm (a, b)
    obtain ⟨Φμ, hΦμm, hΦμ⟩ := HarmonicBalls.S11m.MeasureDecoderBall.measureDecoder_ball_zero hLoc hNonat hFull
      7 (by norm_num) γ hγ hγ2
    obtain ⟨I⟩ := caExistsPinchCountSets V W T Q' Q δ
    refine ⟨decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M, ?_, ?_⟩
    · exact measurableSet_decodedPinchRuleBall I (Φ := decodedFamily Ψc)
        (fun O _ x y => measurable_decodedFamily Ψc hΨcm O x y)
        (measurable_decGreen hΦμm) (measurable_decMassU hΦμm hgeo.isOpen_U.measurableSet) M
    intro α hα Ω _ P hC hcirc μ D hgff hμ hD
    have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
    have hDm := hD
    obtain ⟨𝔇, h𝔇, hDω⟩ := hD
    have hbase := hBase γ ξ hγ hγ2 𝔇₀ 𝔇 h𝔇₀ h𝔇 Ω P hC hcirc hgff
    have hLen₀ := hLen γ ξ 𝔇₀ hγ hγ2 h𝔇₀ Ω P hC hcirc hgff
    have hAx₀ := ((hAx Ω P γ ξ α hC hcirc) hgff hγ hγ2 hα 𝔇₀ h𝔇₀).1
    have hΨω := hΨ α hα Ω P hC hcirc hgff
    have hΦμω := hΦμ α hα Ω P hC hcirc μ hgff hμ
    have hSG := ae_annulusGreenPotentialSup_ne_top_alpha hgff hγ hγ2 hα hμ hgrowth
    have hMU := ae_measure_ne_top_of_isBounded hμ U (caBoundedU hgeo)
    have hU7 : U ⊆ ball (0 : ℂ) 7 := hgeo.U_subset.trans (caAnnulusSubBall (R := 7) (by norm_num))
    have hA7 : annulus (0 : ℂ) 3 6 ⊆ ball (0 : ℂ) 7 := caAnnulusSubBall (R := 7) (by norm_num)
    have hdm := decodedMasses_ae Φμ (fun ω => localModConstField α hC (ball (0 : ℂ) 7) ω) μ
      isOpen_ball.measurableSet hU7 hA7 hΦμω
    have hgoodDw : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
        (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) ∧
        ∀ x y, 0 ≤ (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y := by
      filter_upwards [hAx₀] with ω hω
      exact ⟨hω.2, fun x y => ENNReal.toReal_nonneg⟩
    have hΨ' : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ v ∈ ball (0 : ℂ) 7 \ {0}, ∀ w ∈ ball (0 : ℂ) 7 \ {0},
        ENNReal.ofReal (Ψc (localModConstField α hC (ball (0 : ℂ) 7) ω) v w) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
            (ball (0 : ℂ) 7 \ {0}) v w := by
      filter_upwards [hΨω] with ω hω
      obtain ⟨b, hb, h⟩ := hω
      exact ⟨b, hb, fun v hv w hw => by
        rw [hΨc]
        exact h (v, w) ⟨hv, hw⟩⟩
    have hfamω := decodedVal_ae_family Ψc (fun ω => localModConstField α hC (ball (0 : ℂ) 7) ω)
      (fun ω u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
      caIsOpenPunct caIsConnectedPunct hgoodDw hΨ'
    have hall : ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈
        decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M ↔
        HarmonicBalls.S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
      filter_upwards [hbase, hLen₀, hgoodDw, hfamω, hDω, hdm, hSG, hMU] with
        ω hbω hLenω hgoodω hfω hDωω hdmω hSGω hMUω
      obtain ⟨b₁, hb₁, hb₁e⟩ := hbω
      obtain ⟨b₀, hb₀, hfamω'⟩ := hfω
      obtain ⟨c, hc0, hctop, hmUω, hmSω⟩ := hdmω
      have hD₁ : ∀ x y, D ω x y = b₁ *
          (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y :=
        caWeylRel hLenω hb₁ hb₁e (fun x y => ⟨(hDωω x y).1, (hDωω x y).2⟩)
      have hDlen : IsEuclideanLengthMetric (D ω) := by
        have hfun : D ω = fun x y => b₁ *
            (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y :=
          funext fun x => funext fun y => hD₁ x y
        rw [hfun]
        exact IsEuclideanLengthMetric.const_mul hgoodω.1 hb₁
      have hΦ := caDecodesOfFamily hgeo hOmega I (decodedFamily Ψc)
        (localModConstField α hC (ball (0 : ℂ) 7) ω) (Dw := fun u v =>
          (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) (D := D ω)
        hb₀ hb₁ hD₁ hfamω'
      have hmS : decGreen Φμ (localModConstField α hC (ball (0 : ℂ) 7) ω) =
          ENNReal.ofReal c.toReal * annulusGreenPotentialSup (μ ω) 0 3 6 := by
        have h' : decGreen Φμ (localModConstField α hC (ball (0 : ℂ) 7) ω) =
            c * annulusGreenPotentialSup (μ ω) 0 3 6 := hmSω
        rw [h', ENNReal.ofReal_toReal hctop.ne]
      have hmU : decMassU Φμ U (localModConstField α hC (ball (0 : ℂ) 7) ω) =
          ENNReal.ofReal c.toReal * μ ω U := by
        have h' : decMassU Φμ U (localModConstField α hC (ball (0 : ℂ) 7) ω) = c * μ ω U := hmUω
        rw [h', ENNReal.ofReal_toReal hctop.ne]
      have hpos' : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hctop.ne
      have hiff := HarmonicBalls.S11ax.decodedPinchRule_iff_ball hDlen (fun x y => (hDωω x y).1)
        (div_pos hb₀ hb₁) hpos' hgeo hΩ I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) (μ ω) M
        (localModConstField α hC (ball (0 : ℂ) 7) ω) hΦ hmS hmU
      constructor
      · intro hmem
        exact (hiff.mp hmem).1
      · intro hr
        exact hiff.mpr ⟨hr, hSGω, hMUω⟩
    have hsub : ∀ᵐ ω ∂P, (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ) →
        localModConstField α hC (ball (0 : ℂ) 7) ω ∈
          decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M := by
      filter_upwards [hall] with ω hω hev
      exact hω.mpr hev
    have hpos := HarmonicBalls.S11an.pinchLocal_events_pos_discharged hfr hmass hAx hCMAbs hCMRew hComp hDsm
      hMf hDiam hMk hS U V W T Q' Q δ hgeo hΩS γ α ξ hγ hγ2 hξ hα Ω P hC hcirc μ D hgff hμ hDm
      (hμW Ω P γ α hC hcirc) M hM
    refine ⟨lt_of_lt_of_le hpos (measure_mono_ae hsub), ?_⟩
    filter_upwards [hall, hDω] with ω hω hDωω hmem
    have hr := hω.mp hmem
    exact ⟨pinchFirstEventLocal_subset (D ω) (fun x y => (hDωω x y).1) W T Q' Q δ hr.1,
      pinchSecondEventLocal_subset (μ ω) (D ω) U V δ M hr.2.1,
      pinchThirdEventLocal_subset (D ω) V W δ hr.2.2⟩
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    intro α _ Ω _ P hC hcirc μ D _ _ hD
    obtain ⟨𝔇, h𝔇, -⟩ := hD
    exact (hex ⟨𝔇, h𝔇⟩).elim

/-- **Lemma 11.12 (corrected), `CorrectedLemma11_12Stmt`, from external inputs only.** The local certificate is
`pinchLocalCertificate_of_inputs`; the length axioms and the exponent positivity `LQGMetricExponentPositive` (n4,
truth check TRUE) enter as in `firstPass_11_12_corrected` (`S11m/Corrected11_12.lean`). The hypotheses are exactly the
named inputs of `pinchLocalCertificate_of_inputs` together with `hXi`; there is no other hypothesis. -/
theorem firstPass_11_12_corrected_of_inputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hXi : LQGMetricExponentPositive)
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hBase : HarmonicBalls.S11ak.LQGMetricBaseComparisonStmt.{u})
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hFull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u}) :
    CorrectedLemma11_12Stmt.{u} :=
  firstPass_11_12_corrected (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    (pinchLocalCertificate_of_inputs hAx hLen hN2 hBase hμW hLoc hNonat hFull hgrowth hfr hmass hCMAbs hCMRew
      hComp hDsm hMf hDiam hMk hS) hXi

end HarmonicBalls.S11m.CertificateAssembly
