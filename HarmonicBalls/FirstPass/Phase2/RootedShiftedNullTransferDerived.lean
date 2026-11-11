import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferSteps
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance
import HarmonicBalls.Proofs.Sec2.AffineField
import HarmonicBalls.Proofs.Sec2.LQGLimitLocality
import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferEvent
import HarmonicBalls.FirstPass.Phase2.GFFJointLaw
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferLaw

/-! # Shifted-root null transfer: the local identification

Local identification for the corrected `RootedShiftedDecoderNullTransfer`.
On the ball `B_{5r/4}` around the root, the profile decoder applied to the DMS-shifted α₀-profile, recentred at `z`,
equals `exp(γ h(1,z))` times the γ-decoded profile of the affine-plus-test-function field (Duplantier-Sheffield, LQG
measure of a field with an insertion; Armitage-Gardiner, circle averages). The identity is local: it is obtained by
`IsLQGLimit.restrict_eq` from the translated α₀-limit and the `add_const` limit of the γ-field, which agree on the
dyadic scales below `r/4`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The circle average of the DMS shift is jointly continuous in `(radius, centre)` on positive radii
(Armitage-Gardiner; Jensen's formula `circleAverage_rootShift`). -/
theorem continuousOn_circleAverage_dmsShift (γ : ℝ) (z : ℂ) :
    ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (dmsShift γ z) p.2 p.1) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hds : dmsShift γ z = LocalDecoderCommon.rootShift γ z := by
    funext w
    simp only [dmsShift, LocalDecoderCommon.rootShift]
    rw [max_comm]
  have hfun : ∀ p : ℝ × ℂ, 0 < p.1 → Real.circleAverage (dmsShift γ z) p.2 p.1 =
      -γ * Real.log (max p.1 ‖p.2 - z‖) +
        γ * Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1 := by
    intro p hp
    rw [hds]
    exact LocalDecoderCommon.circleAverage_rootShift γ hp z p.2
  have hm : ContinuousOn (fun p : ℝ × ℂ => max p.1 ‖p.2 - z‖) (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuous_fst.max (continuous_snd.sub continuous_const).norm).continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℂ => Real.log (max p.1 ‖p.2 - z‖)) (Set.Ioi 0 ×ˢ Set.univ) :=
    hm.log fun p hp => (lt_max_of_lt_left (Set.mem_Ioi.mp hp.1)).ne'
  have h2 : Continuous (fun p : ℝ × ℂ => Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1) :=
    Section6.continuous_circleAverage_radius_center LocalDecoderCommon.continuous_log_max_one
  have hcont : ContinuousOn (fun p : ℝ × ℂ => -γ * Real.log (max p.1 ‖p.2 - z‖) +
      γ * Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1) (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuousOn_const.mul h1).add (continuousOn_const.mul h2.continuousOn)
  exact hcont.congr fun p hp => hfun p (Set.mem_Ioi.mp hp.1)

/-- **L4a, local profile identity.** For `0 < ε < r/4` and `|y| < 5r/4`, the α₀-field of the profile `G1`
(the DMS-shifted field `hc + Av dmsShift`) at the point `y + z` equals the γ-field of the profile `G2`
(the affine profile `hc(·, · + z) - hc(1, z)` plus the smooth shift `Av gt`) at `y`, plus the constant `hc(1,z)`.
Uses `fieldCircleAverage_dmsShift_add` and `circleAverage_testShift_eq`. -/
theorem fieldCircleAverage_local_identity {a0 γ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ} {G1 G2 : ℝ → ℂ → ℝ}
    {gt : ℂ → ℝ} (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r)
    (hEq : Set.EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hG1 : ∀ s x, 0 < s → G1 s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hG2 : ∀ s x, 0 < s → G2 s x = hc s (x + z) - hc 1 z + Real.circleAverage gt x s)
    {ε : ℝ} {y : ℂ} (hε : 0 < ε) (hεr : ε < r / 4) (hy : ‖y‖ < 5 * r / 4) :
    fieldCircleAverage a0 G1 ε (y + z) = fieldCircleAverage γ G2 ε y + hc 1 z := by
  have hn1 : ‖y + z‖ + ε ≤ 1 := by
    have := norm_add_le y z
    linarith
  have hn2 : ε ≤ ‖y + z‖ := by
    have h3 : ‖(y + z) - y‖ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
    have h4 : (y + z) - y = z := by ring
    rw [h4] at h3
    linarith
  have hA := fieldCircleAverage_dmsShift_add (α₀ := a0) (γ := γ) (z := z) (c := y + z) hc hε hn2 hn1
  have hB := circleAverage_testShift_eq hz hEq hy hε hεr
  have hC : Real.circleAverage (fun x : ℂ => Real.log ‖x‖) y ε = Real.log (max ε ‖y‖) := by
    have := circleAverage_log_norm_sub_eq y 0 hε
    simpa [sub_zero] using this
  have hG1' : fieldCircleAverage a0 G1 ε (y + z) =
      fieldCircleAverage a0 (fun s x => hc s x + Real.circleAverage (dmsShift γ z) x s) ε (y + z) := by
    simp only [fieldCircleAverage, hG1 ε (y + z) hε]
  have hG2' : fieldCircleAverage γ G2 ε y =
      hc ε (y + z) - hc 1 z + Real.circleAverage gt y ε - γ * Real.log (max ε ‖y‖) := by
    simp only [fieldCircleAverage, hG2 ε y hε, hC]
  rw [hG1', hA, hG2', hB, add_sub_cancel_right]
  ring

/-- **Local identification of the decoded shifted measure.** If the α₀-profile `F1` of the DMS-shifted field and
the γ-profile `F2` of the affine-plus-test field lie in the convergence locus of the test family `T`, then the
decoded α₀-measure of `F1`, recentred at `z`, agrees on `B_{5r/4}` with `exp(γ h(1,z))` times the decoded γ-measure of
`F2`. Proof: `IsLQGLimit.restrict_eq` for the translated α₀-limit and the `add_const` γ-limit. -/
theorem decoder_shifted_local_eq {a0 γ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ}
    (T : ProfileDecoderDerived.TestFamily) (F1 F2 : C(CircleParameter, ℝ)) {gt : ℂ → ℝ}
    (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r) (hr : 0 < r)
    (hEq : Set.EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hF1 : ∀ s x, 0 < s → circleProfile F1 s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hF2 : ∀ s x, 0 < s → circleProfile F2 s x = hc s (x + z) - hc 1 z + Real.circleAverage gt x s)
    (h1 : F1 ∈ ProfileDecoderDerived.convSet T γ a0) (h2 : F2 ∈ ProfileDecoderDerived.convSet T γ γ) :
    ((ProfileDecoderDerived.decoder T γ a0 F1).map (fun w => w - z)).restrict (ball (0 : ℂ) (5 * r / 4)) =
      (ENNReal.ofReal (Real.exp (γ * hc 1 z)) • ProfileDecoderDerived.decoder T γ γ F2).restrict
        (ball (0 : ℂ) (5 * r / 4)) := by
  have hpos : ∀ n : ℕ, 0 < dyadicScale n := fun n => by unfold dyadicScale; positivity
  have hA := ProfileDecoderDerived.isLQGLimit_decoder T γ a0 h1
  have hB := ProfileDecoderDerived.isLQGLimit_decoder T γ γ h2
  have hT := Section6.isLQGLimit_translate hA (fun n => ProfileDecoderDerived.continuous_fca a0 F1 (hpos n)) z
  have hAdd := hB.add_const (hc 1 z)
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < r / 4 := by
    unfold dyadicScale
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds (by linarith))
  refine hT.restrict_eq hAdd isOpen_ball ?_
  intro K _ hK
  filter_upwards [hev] with k hk
  intro y hy
  have hyU : ‖y‖ < 5 * r / 4 := mem_ball_zero_iff.mp (hK hy)
  exact fieldCircleAverage_local_identity (G1 := circleProfile F1) (G2 := circleProfile F2) hz hzu hEq
    (fun s x hs => hF1 s x hs) (fun s x hs => hF2 s x hs) (hpos k) hk hyU

universe u

open GFFJointLaw

/-! ## Selector recovery and the per-sample step -/

/-- The zero extension of a profile on the positive-radius subtype of the joint sample (`jointSample`):
`extSub F r z = F (r, z)` for `r > 0` and `0` otherwise. -/
noncomputable def extSub (F : {p : ℝ × ℂ // 0 < p.1} → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then F ⟨(r, z), h⟩ else 0

lemma extSub_restrict (c : ℝ → ℂ → ℝ) : extSub (fun p => c p.1.1 p.1.2) = posPart c := by
  funext r z
  by_cases h : 0 < r <;> simp [extSub, posPart, h]

lemma measurable_extSub : Measurable extSub := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun z => ?_
  by_cases h : 0 < r
  · simpa [extSub, h] using measurable_pi_apply (⟨(r, z), h⟩ : {p : ℝ × ℂ // 0 < p.1})
  · simp [extSub, h, measurable_const]

/-- **Recovery of a continuous profile.** If `Sel` recovers every profile from its zero extension (the recovery form
of `CanonicalProfileSelectorStmt`, `B2ShiftedProfileDecoder.lean:59`), and `G` is continuous on the positive radii, then
`Sel (posPart G)` is the profile `y` of `G`: `posPart G = posExtend y`, and `circleProfile y` reads `G` at every positive
radius (Armitage-Gardiner, circle averages; Duplantier-Sheffield, circle-average profile). -/
theorem sel_posPart_of_continuousOn {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)}
    (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y) {G : ℝ → ℂ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    ∃ y : C(CircleParameter, ℝ), posPart G = posExtend ⇑y ∧ Sel (posPart G) = y ∧
      ∀ s x, 0 < s → circleProfile y s x = G s x := by
  have hc : Continuous fun p : CircleParameter => G p.1.1 p.2 :=
    hG.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun p => Set.mk_mem_prod p.1.2 (Set.mem_univ _)
  let y : C(CircleParameter, ℝ) := ⟨fun p => G p.1.1 p.2, hc⟩
  have hpp : posPart G = posExtend ⇑y := by
    funext r z
    by_cases h : 0 < r <;> simp [posPart, posExtend, y, h]
  exact ⟨y, hpp, by rw [hpp]; exact hRec y, fun s x hs => by simp [circleProfile, y, hs]⟩

/-- **One sample.** For a fixed sample: the α₀-decoder of the selected DMS-shifted profile, recentred
at `z`, equals `exp(γ h(1,z))` times the γ-decoder of the selected affine-plus-test profile, on `B_{5r/4}`. The
hypotheses `hA` (the α₀ membership) and `hB` (the γ membership) are almost-sure facts. -/
theorem decoder_shifted_of_selector {a0 γ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ} {gt : ℂ → ℝ}
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (T : ProfileDecoderDerived.TestFamily)
    (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r) (hr : 0 < r)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hL1 : ∀ s x, dmsShiftedCircle γ z hc s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hgt : Continuous gt) (hEq : EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hA : ∀ y : C(CircleParameter, ℝ), posPart (dmsShiftedCircle γ z hc) = posExtend ⇑y →
      y ∈ ProfileDecoderDerived.convSet T γ a0)
    (hB : Sel (posPart (fun s x => hc s (x + z) - hc 1 z + Real.circleAverage gt x s)) ∈
      ProfileDecoderDerived.convSet T γ γ) :
    ((ProfileDecoderDerived.decoder T γ a0 (Sel (posPart (dmsShiftedCircle γ z hc)))).map
        (fun w => w - z)).restrict (ball (0 : ℂ) (5 * r / 4)) =
      (ENNReal.ofReal (Real.exp (γ * hc 1 z)) •
        ProfileDecoderDerived.decoder T γ γ
          (Sel (posPart (fun s x => hc s (x + z) - hc 1 z + Real.circleAverage gt x s)))).restrict
        (ball (0 : ℂ) (5 * r / 4)) := by
  have hcontDms : ContinuousOn (fun p : ℝ × ℂ => dmsShiftedCircle γ z hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) :=
    (hcont.add (continuousOn_circleAverage_dmsShift γ z)).add continuousOn_const
  have hcontG : ContinuousOn (fun p : ℝ × ℂ => hc p.1 (p.2 + z) - hc 1 z + Real.circleAverage gt p.2 p.1)
      (Set.Ioi 0 ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℝ × ℂ => hc p.1 (p.2 + z)) (Set.Ioi 0 ×ˢ Set.univ) :=
      hcont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn
        fun p hp => Set.mk_mem_prod hp.1 (Set.mem_univ _)
    exact (h1.sub continuousOn_const).add (Section6.continuous_circleAverage_radius_center hgt).continuousOn
  obtain ⟨y1, hpp1, hsel1, hprof1⟩ :=
    sel_posPart_of_continuousOn (G := dmsShiftedCircle γ z hc) hRec hcontDms
  obtain ⟨y2, -, hsel2, hprof2⟩ :=
    sel_posPart_of_continuousOn (G := fun s x => hc s (x + z) - hc 1 z + Real.circleAverage gt x s) hRec hcontG
  refine decoder_shifted_local_eq T _ _ hz hzu hr hEq ?_ ?_ ?_ hB
  · intro s x hs
    rw [hsel1, hprof1 s x hs, hL1 s x]
  · intro s x hs
    rw [hsel2, hprof2 s x hs]
  · rw [hsel1]
    exact hA y1 hpp1

/-- **Almost-sure selected membership.** For an LQG measure `μ` of the field at parameter `α`, the selected profile of the
unshifted field lies in `convSet T γ α` almost surely (the `hmem` step of `lqgMeasureOfProfileMeasurable_derived`). -/
theorem ae_sel_mem_convSet {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    (T : ProfileDecoderDerived.TestFamily) (γ α : ℝ) (μ : Ω → Measure ℂ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, Sel (posPart (hcirc ω)) ∈ ProfileDecoderDerived.convSet T γ α := by
  have hagree : ∀ᵐ ω ∂P, ∀ p : CircleParameter, Sel (posPart (hcirc ω)) p = hcirc ω p.1 p.2 := by
    filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
    obtain ⟨y, -, hsel, hprof⟩ := sel_posPart_of_continuousOn hRec hω
    intro p
    rw [hsel]
    have hp : (0 : ℝ) < p.1.1 := p.1.2
    have h := hprof p.1.1 p.2 hp
    simpa [circleProfile, hp] using h
  have h2 := (isLQGMeasureOfField_circleProfile_iff (F := fun ω => Sel (posPart (hcirc ω))) hagree γ α μ).1 hμ
  filter_upwards [h2] with ω hω
  intro m
  exact ⟨_, hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport⟩

/-- Measurability of the joint sample of a whole-plane GFF. -/
theorem measurable_jointSample_of {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsWholePlaneGFF P hC hcirc) :
    Measurable (jointSample hC hcirc) := by
  rw [jointSample_eq_pairOfFamily]
  exact measurable_pairOfFamily.comp (measurable_obsFamily_map hP)

/-- Transfer of an almost-sure membership along an equality of laws, with `P ≪ P'`. -/
theorem ae_mem_of_map_eq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P P' : Measure Ω}
    {X X' : Ω → β} {A : Set β} (hA : MeasurableSet A) (hX : Measurable X) (hX' : Measurable X')
    (hac : P ≪ P') (hmap : P'.map X' = P.map X) (h : ∀ᵐ ω ∂P, X ω ∈ A) :
    ∀ᵐ ω ∂P, X' ω ∈ A := by
  have h1 : P (X ⁻¹' Aᶜ) = 0 := ae_iff.mp h
  have h2 : P' (X' ⁻¹' Aᶜ) = 0 := by
    rw [← Measure.map_apply hX' hA.compl, hmap, Measure.map_apply hX hA.compl]
    exact h1
  exact ae_iff.mpr (hac h2)

/-- **The γ-profile of the shifted field.** Let `gt` be a smooth compactly supported test function with mean zero on
the unit circle. Under the Cameron-Martin reweighting `P'` of the affine pullback `h' = (affinePairing hC hcirc 1 z,
affineCircle hcirc 1 z)` by `gt` (`cameronMartinGFFReweighting_derived`), the selected profile of `h' + Av gt` lies in
`convSet T γ γ` almost surely, whenever the selected profile of `hcirc` does. -/
theorem ae_sel_affine_shift_mem_convSet {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (hSelM : Measurable Sel)
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ) (z : ℂ) {gt : ℂ → ℝ}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) gt) (hcs : HasCompactSupport gt) (hgt0 : Real.circleAverage gt 0 1 = 0)
    (hmem : ∀ᵐ ω ∂P, Sel (posPart (hcirc ω)) ∈ ProfileDecoderDerived.convSet T γ γ) :
    ∀ᵐ ω ∂P, Sel (posPart (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s)) ∈
      ProfileDecoderDerived.convSet T γ γ := by
  have hAff : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) :=
    wholePlaneGFFAffineInvariance_derived P hC hcirc hGFF 1 one_ne_zero z
  obtain ⟨P', hP'1, hP'2, hGFF'⟩ :=
    S11aj.cameronMartinGFFReweighting_derived Ω P _ _ hAff gt hsm hcs hgt0
  have : IsProbabilityMeasure P' := hGFF'.isGaussianProcess.isProbabilityMeasure
  have hjl := (isWholePlaneGFF_jointLaw_map_eq P' P _ _ _ _ hGFF' hAff).trans
    (isWholePlaneGFF_jointLaw_map_eq P P _ _ hC hcirc hAff hGFF)
  have hJm := measurable_jointSample_of hGFF
  have hJ'm := measurable_jointSample_of hGFF'
  have hQm : Measurable fun J : ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) ×
      ({p : ℝ × ℂ // 0 < p.1} → ℝ) => Sel (extSub J.2) :=
    hSelM.comp (measurable_extSub.comp measurable_snd)
  have hmap := congrArg (Measure.map fun J : ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) ×
      ({p : ℝ × ℂ // 0 < p.1} → ℝ) => Sel (extSub J.2)) hjl
  rw [Measure.map_map hQm hJ'm, Measure.map_map hQm hJm] at hmap
  have hmem' : ∀ᵐ ω ∂P, Sel (extSub (jointSample hC hcirc ω).2) ∈ ProfileDecoderDerived.convSet T γ γ :=
    hmem.mono fun ω hω => by
      show Sel (extSub (fun p => hcirc ω p.1.1 p.1.2)) ∈ _
      rw [extSub_restrict]
      exact hω
  have key := ae_mem_of_map_eq (ProfileDecoderDerived.measurableSet_convSet T γ γ)
    (hQm.comp hJm) (hQm.comp hJ'm) hP'2 hmap hmem'
  filter_upwards [key] with ω hω
  have hω' : Sel (extSub (fun p : {p : ℝ × ℂ // 0 < p.1} =>
      affineCircle hcirc 1 z ω p.1.1 p.1.2 + Real.circleAverage gt p.1.2 p.1.1)) ∈
      ProfileDecoderDerived.convSet T γ γ := hω
  rwa [extSub_restrict (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s)] at hω'

/-! ## Canonical data and the corrected statement -/

/-- Selection of a continuous profile: a point of `convSet` for the selected profile. -/
theorem sel_mem_of_ext {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)}
    (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y) {G : ℝ → ℂ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {A : Set C(CircleParameter, ℝ)} (hA : ∀ y : C(CircleParameter, ℝ), posPart G = posExtend ⇑y → y ∈ A) :
    Sel (posPart G) ∈ A := by
  obtain ⟨y, hpp, hsel, -⟩ := sel_posPart_of_continuousOn hRec hG
  rw [hsel]
  exact hA y hpp

/-- **Measure algebra of the shifted root.** If the recentred measure of `μ` agrees on `B_R(0)` with `c • η`
(`c ≠ 0, ⊤`, `r ≤ R`), then the recentred output at radius `r` is `(z, N_r(η|B_r(0)))`. -/
theorem recentredOutput_of_restrict_eq {μ η : Measure ℂ} [IsLocallyFiniteMeasure μ] {z : ℂ} {r R : ℝ}
    (hrR : r ≤ R) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : (μ.map (fun w => w - z)).restrict (ball (0 : ℂ) R) = (c • η).restrict (ball (0 : ℂ) R)) :
    recentredOutput r (μ, z) = (z, massNormalize r (η.restrict (ball (0 : ℂ) r))) := by
  have hpre : (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r = ball z r := by
    ext w
    simp [dist_eq_norm]
  have hrec : recenteredRestriction μ r z = (μ.map (fun w => w - z)).restrict (ball (0 : ℂ) r) := by
    unfold recenteredRestriction
    rw [Measure.restrict_map (measurable_sub_const z) measurableSet_ball, hpre]
  have hsub : (μ.map (fun w => w - z)).restrict (ball (0 : ℂ) r) =
      ((μ.map (fun w => w - z)).restrict (ball (0 : ℂ) R)).restrict (ball (0 : ℂ) r) := by
    rw [Measure.restrict_restrict measurableSet_ball, Set.inter_eq_left.2 (Metric.ball_subset_ball hrR)]
  rw [recentredOutput, finitePart_eq_of_locallyFinite, hrec, hsub, h,
    Measure.restrict_restrict measurableSet_ball, Set.inter_eq_left.2 (Metric.ball_subset_ball hrR),
    Measure.restrict_smul, massNormalize_smul_const _ hc0 hct]

/-- **One sample, after mass normalisation.** The recentred α₀-output of the selected DMS-shifted profile equals the shifted-root output
`(z, N_r(Dg(Sel(posPart G2))|B_r(0)))`. -/
theorem recentredOutput_decoder_shift {γ α₀ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ} {gt : ℂ → ℝ}
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (T : ProfileDecoderDerived.TestFamily)
    (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r) (hr : 0 < r)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hL1 : ∀ s x, dmsShiftedCircle γ z hc s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hgt : Continuous gt) (hEq : EqOn gt (fun y => -α₀ * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hA : ∀ y : C(CircleParameter, ℝ), posPart (dmsShiftedCircle γ z hc) = posExtend ⇑y →
      y ∈ ProfileDecoderDerived.convSet T γ α₀)
    (hB : Sel (posPart (fun s x => hc s (x + z) - hc 1 z + Real.circleAverage gt x s)) ∈
      ProfileDecoderDerived.convSet T γ γ) :
    recentredOutput r (ProfileDecoderDerived.decoder T γ α₀ (Sel (posPart (dmsShiftedCircle γ z hc))), z) =
      (z, massNormalize r ((ProfileDecoderDerived.decoder T γ γ
        (Sel (posPart (fun s x => hc s (x + z) - hc 1 z + Real.circleAverage gt x s)))).restrict
        (ball (0 : ℂ) r))) := by
  have hcontDms : ContinuousOn (fun p : ℝ × ℂ => dmsShiftedCircle γ z hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) :=
    (hcont.add (continuousOn_circleAverage_dmsShift γ z)).add continuousOn_const
  have hF1 : Sel (posPart (dmsShiftedCircle γ z hc)) ∈ ProfileDecoderDerived.convSet T γ α₀ :=
    sel_mem_of_ext hRec hcontDms hA
  have : IsLocallyFiniteMeasure
      (ProfileDecoderDerived.decoder T γ α₀ (Sel (posPart (dmsShiftedCircle γ z hc)))) :=
    (ProfileDecoderDerived.isLQGLimit_decoder T γ α₀ hF1).isLocallyFiniteMeasure
  have key := decoder_shifted_of_selector (a0 := α₀) (gt := gt) T hRec hz hzu hr hcont hL1 hgt hEq hA hB
  refine recentredOutput_of_restrict_eq (by linarith) ?_ ?_ key
  · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  · exact ENNReal.ofReal_ne_top

/-- The canonical test family of the decoder: `Classical.choice` of `exists_testFamily`. -/
noncomputable def canonicalTest : ProfileDecoderDerived.TestFamily :=
  Classical.choice ProfileDecoderDerived.exists_testFamily

/-- The canonical profile selector: the selector of `canonicalProfileSelector`
(`B2ShiftedProfileDecoder.lean:74`). -/
noncomputable def canonicalSel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ) :=
  Classical.choose canonicalProfileSelector

theorem canonicalSel_measurable : Measurable canonicalSel :=
  (Classical.choose_spec canonicalProfileSelector).1

theorem canonicalSel_posExtend (y : C(CircleParameter, ℝ)) : canonicalSel (posExtend ⇑y) = y :=
  (Classical.choose_spec canonicalProfileSelector).2 y

/-- **Corrected `RootedShiftedDecoderNullTransfer`.** The decoder is the canonical
`decoder canonicalTest γ α₀` applied to the canonical selector, and the root quantifier is almost everywhere for the
Lebesgue measure restricted to the local domain `D_j` (Duplantier-Miller-Sheffield, Lemma A.10, a.e.-root form). The
original `RootedShiftedDecoderNullTransfer` (`RootedDominationJoint.lean:126`) is left unchanged. -/
def RootedShiftedDecoderNullTransferCanonical {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) (j : ℕ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (localDomain j)), ∀ S : Set (ℂ × Measure ℂ), MeasurableSet S →
    P {ω | localReferenceObservation ν j (z, ω) ∈ S} = 0 →
      P {ω | recentredOutput (localRadius j)
        (ProfileDecoderDerived.decoder canonicalTest γ α₀
          (canonicalSel (posPart (dmsShiftedCircle γ z (hcirc ω)))), z) ∈ S} = 0

/-- Canonical form of `ShiftedDecoderNullTransferStmt` (`RootedDominationJoint.lean:138`): the α₀-measure `μ` is the
canonical decoded measure of the field, and the conclusion is `RootedShiftedDecoderNullTransferCanonical`. The three
existence and a.e.-root inputs of `ae_rootedShiftedNullEvent` are named hypotheses (Proposed, pending source-check). -/
def ShiftedDecoderNullTransferCanonicalStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMeasureOfField P γ γ hcirc ν →
    LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureExistence P γ α₀ hC hcirc →
    (∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ') →
    (∀ᵐ ω ∂P, μ ω = ProfileDecoderDerived.decoder canonicalTest γ α₀
      (canonicalSel (posPart (hcirc ω)))) →
    ∀ j : ℕ, RootedShiftedDecoderNullTransferCanonical P γ α₀ hcirc ν j

/-! ## Assembly -/

/-- The shifted-root output `W`, with the affine circle profile written through `hcirc`. -/
theorem rootShiftOutput_eq_hc {Ω : Type*} (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) (hcirc : Ω → ℝ → ℂ → ℝ) (gt : ℂ → ℝ)
    (ω : Ω) :
    RootedShiftedNullTransferLaw.rootShiftOutput T γ Sel r z hcirc gt ω =
      (z, massNormalize r ((ProfileDecoderDerived.decoder T γ γ
        (Sel (posPart (fun s x => hcirc ω s (x + z) - hcirc ω 1 z + Real.circleAverage gt x s)))).restrict
        (ball (0 : ℂ) r))) := by
  unfold RootedShiftedNullTransferLaw.rootShiftOutput RootedShiftedNullTransferLaw.rootOutputOfProfile
  simp [affineCircle]

theorem localRadius_zero_ball_empty (z : ℂ) : Metric.ball z (localRadius 0) = ∅ :=
  Metric.ball_eq_empty.2 (by simp [localRadius])

/-- At the zero radius the recentred output is the constant `(z, 0)`. -/
theorem recentredOutput_localRadius_zero (μ : Measure ℂ) (z : ℂ) :
    recentredOutput (localRadius 0) (μ, z) = (z, 0) := by
  simp [recentredOutput, recenteredRestriction, massNormalize, localRadius_zero_ball_empty]

/-- At the zero radius the reference observation is the constant `(z, 0)`. -/
theorem localReferenceObservation_localRadius_zero {Ω : Type*} (ν : Ω → Measure ℂ) (z : ℂ) (ω : Ω) :
    localReferenceObservation ν 0 (z, ω) = (z, 0) := by
  simp [localReferenceObservation, massNormalize, localRadius_zero_ball_empty]

/-- **Corrected null transfer, for every root class `j`.** The canonical shifted-root output is absolutely
continuous with respect to the reference observation for almost every root, so a null reference event is a
null canonical shifted event. The named inputs are the Proposed existence and Lemma A.10 hypotheses of
`ae_rootedShiftedNullEvent`. -/
theorem rootedShiftedNullTransferCanonical {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ α₀ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (ν : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hSub : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) (j : ℕ) :
    RootedShiftedDecoderNullTransferCanonical P γ α₀ hcirc ν j := by
  unfold RootedShiftedDecoderNullTransferCanonical
  have hmem := ae_sel_mem_convSet hGFF canonicalSel_posExtend canonicalTest γ γ ν hν
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ae_of_all _ fun z S _ h => ?_
    simpa only [recentredOutput_localRadius_zero, localReferenceObservation_localRadius_zero] using h
  · have hr : 0 < localRadius j := by unfold localRadius; positivity
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hr16 : 2 * localRadius j ≤ 1 := by
      unfold localRadius
      rw [show 2 * (1 / (16 * (j : ℝ))) = 1 / (8 * j) by ring, div_le_one (by positivity)]
      linarith
    have hE := ae_rootedShiftedNullEvent P canonicalTest γ α₀ hγ0 hγ2 hα hC hcirc hGFF hExist0 hExistα hSub j
    filter_upwards [hE, ae_restrict_mem (measurableSet_localDomain j)] with z hz hzD
    obtain ⟨hz1, hz2⟩ := hzD
    obtain ⟨gt, hgt, hEq⟩ := exists_testFunction_logShift (a0 := α₀) hr hz1
    have hgtc : Continuous gt := hgt.1.continuous
    have hgt0 : Real.circleAverage gt 0 1 = 0 := circleAverage_testShift_unit hgt hr16
    have hd := ae_sel_affine_shift_mem_convSet hGFF canonicalSel_measurable canonicalTest γ z hgt.1 hgt.2.1
      hgt0 hmem
    have hL1 := ae_dmsShiftedCircle_eq_field hGFF γ (show ‖z‖ ≤ 1 by linarith)
    have hL6 := RootedShiftedNullTransferLaw.rootShiftOutput_map_absolutelyContinuous_referenceObservation P
      canonicalTest γ canonicalSel canonicalSel_measurable canonicalSel_posExtend hGFF ν hν j hj z gt hgt
    have hW := RootedShiftedNullTransferLaw.measurable_rootShiftOutput canonicalTest γ canonicalSel_measurable
      hGFF (localRadius j) z gt
    have hXW : ∀ᵐ ω ∂P, recentredOutput (localRadius j) (ProfileDecoderDerived.decoder canonicalTest γ α₀
        (canonicalSel (posPart (dmsShiftedCircle γ z (hcirc ω)))), z) =
        RootedShiftedNullTransferLaw.rootShiftOutput canonicalTest γ canonicalSel (localRadius j) z hcirc gt ω := by
      filter_upwards [hz, hd, hL1] with ω hω hdω hL1ω
      obtain ⟨-, hcb, hcc⟩ := hω
      have e : (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s) =
          (fun s x => hcirc ω s (x + z) - hcirc ω 1 z + Real.circleAverage gt x s) := by
        funext s x
        simp [affineCircle]
      rw [e] at hdω
      rw [rootShiftOutput_eq_hc]
      exact recentredOutput_decoder_shift canonicalTest canonicalSel_posExtend hz1 hz2 hr hcb
        (fun s x => congrFun (congrFun hL1ω s) x) hgtc hEq hcc hdω
    intro S hS h0
    have hYm : AEMeasurable (fun ω => localReferenceObservation ν j (z, ω)) P := by
      obtain ⟨ν', hν'M, hν'ae⟩ := hGFF.aemeasurable_lqgMeasure hν
      have hm : Measurable fun ω => (z, massNormalize (localRadius j)
          ((ν' ω).restrict (ball (0 : ℂ) (localRadius j)))) :=
        measurable_const.prodMk ((measurable_massNormalize _).comp
          ((RootedShiftedNullTransferLaw.measurable_restrict_ball (localRadius j)).comp hν'M))
      refine AEMeasurable.congr hm.aemeasurable ?_
      filter_upwards [hν'ae] with ω hω
      simp only [localReferenceObservation, hω]
    have hYS : (P.map (fun ω => localReferenceObservation ν j (z, ω))) S = 0 := by
      rw [Measure.map_apply_of_aemeasurable hYm hS]
      exact h0
    have hWS := hL6 hYS
    rw [Measure.map_apply_of_aemeasurable hW.aemeasurable hS] at hWS
    refine (measure_congr (Filter.eventuallyEqSet_iff.2 (hXW.mono fun ω hω => ?_))).trans hWS
    simp [hω]

/-- **The canonical shifted decoder null transfer** (`ShiftedDecoderNullTransferCanonicalStmt`). -/
theorem shiftedDecoderNullTransferCanonicalStmt_derived : ShiftedDecoderNullTransferCanonicalStmt.{u} := by
  intro Ω _ P _ γ α₀ hC hcirc μ ν hGFF hγ0 hγ2 hα _ hν hE0 hEα hA _ j
  exact rootedShiftedNullTransferCanonical P γ α₀ ν hGFF hγ0 hγ2 hα hν hE0 hEα hA j

end HarmonicBalls
