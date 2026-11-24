import HarmonicBalls.Proofs.Sec11.MassDiamPositive
import HarmonicBalls.Proofs.Sec11.RadialCirclePairingApproximation
import HarmonicBalls.Proofs.Sec8.PuncturedFieldGeneration
import HarmonicBalls.Proofs.Sec1.Locality

/-!
# Lemma 11.18 with the conditioning on the field outside `W₀`

`MassDiamModConstStmt` (`MassDiamPositive.lean`) conditions on the field outside `W̄₀` modulo
additive constants. Lemma 11.18 (corrected paper lines 3583-3595) conditions on the field outside
`W₀`, with its constant. Since `W₀` avoids the normalization circle `∂B₁(0)`, the two conditionings
give the same conditional probabilities:

* Pairings with tests outside a closed set `F` disjoint from `∂B₁(0)` are almost surely functions
  of the zero-mean pairings outside `F` (`exists_outside_pairing_of_disjoint_sphere`): for a test
  `ψ` outside `F`, `(h, ψ) = (h, ψ - c b_n) + c (h, b_n)` with `c = ∫ ψ` and narrow radial tests `b_n`
  of mass one around `∂B₁(0)` (supported outside `F`), and `(h, b_n) → h₁(0) = 0` in probability.
  This is the argument of `IsCorrectedPinchConfiguration.exists_outside_absolute_pairing` for a
  general `F`.
* Hence every event of the field outside `F` agrees almost surely with an event of the field
  outside `F` modulo constants, and the two conditional expectations agree almost surely
  (`condExp_ae_eq_of_le_of_ae_representative`).
* `W₀` is shrunk to a concentric disk `W₁` with `Ō ⊆ W₁` and `W̄₁ ⊆ W₀`, so that `W̄₁` avoids
  `∂B₁(0)`. Conditioning on the field outside `W₁` is finer than on the field outside `W₀`, and almost
  sure positivity passes to the coarser conditioning (`ae_condExp_pos_of_le`).

`massDiamPositive_holds` is Lemma 11.18 as printed, for every geometry of concentric disks.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Narrow radial tests of mass one around `∂B₁(0)` are eventually supported outside every compact
set disjoint from `∂B₁(0)`. -/
theorem eventually_radialAnnularTest_one_outside {F : Set ℂ} (hF : IsCompact F)
    (hdisj : Disjoint F (sphere (0 : ℂ) 1)) :
    ∀ᶠ n : ℕ in atTop, IsTestFunction Fᶜ (radialAnnularTest 1 one_pos n) := by
  obtain ⟨η, hη, hgap⟩ : ∃ η : ℝ, 0 < η ∧ ∀ x ∈ F, η ≤ |‖x‖ - 1| := by
    rcases F.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨a, ha, hmin⟩ := hF.exists_isMinOn hne
        ((continuous_norm.sub continuous_const).abs.continuousOn)
      refine ⟨|‖a‖ - 1|, abs_pos.2 (sub_ne_zero.2 fun h => ?_), fun x hx => hmin hx⟩
      exact Set.disjoint_left.1 hdisj ha (mem_sphere_zero_iff_norm.2 h)
  have hsmall := (circleDensityWidth_tendsto_zero 1 1).eventually
    (Iio_mem_nhds (show (0 : ℝ) < min η 1 from lt_min hη one_pos))
  filter_upwards [hsmall] with n hn
  let w := circleDensityWidth 1 1 n
  have hw : 0 < w := circleDensityWidth_pos one_pos one_pos n
  have hclosed : IsClosed {x : ℂ | |‖x‖ ^ 2 - 1 ^ 2| ≤ w} :=
    isClosed_le (((continuous_norm.pow 2).sub continuous_const).abs) continuous_const
  have hts : tsupport (circleDensity 1 w hw 0) ⊆ {x : ℂ | |‖x‖ ^ 2 - 1 ^ 2| ≤ w} := by
    apply closure_minimal _ hclosed
    intro x hx
    have hx' := circleDensity_support 1 w hw 0 x hx
    change |‖x‖ ^ 2 - 1 ^ 2| ≤ w
    simpa only [sub_zero] using hx'.le
  have hout : {x : ℂ | |‖x‖ ^ 2 - 1 ^ 2| ≤ w} ⊆ Fᶜ := by
    intro x hx hxF
    have hg := hgap x hxF
    have hwη : w < η := lt_of_lt_of_le hn (min_le_left _ _)
    have h1 : |‖x‖ - 1| ≤ |‖x‖ ^ 2 - 1 ^ 2| := by
      rw [show ‖x‖ ^ 2 - 1 ^ 2 = (‖x‖ - 1) * (‖x‖ + 1) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ + 1)]
      nlinarith [abs_nonneg (‖x‖ - 1), norm_nonneg x]
    change |‖x‖ ^ 2 - 1 ^ 2| ≤ w at hx
    linarith
  have htest := radialAnnularTest_isTestFunction one_pos n
  exact ⟨htest.1, htest.2.1, (tsupport_mul_subset_right.trans hts).trans hout⟩

/-- **Pairings outside a compact set avoiding the normalization circle are functions of the
zero-mean pairings there.** -/
theorem exists_outside_pairing_of_disjoint_sphere {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {F : Set ℂ} (hF : IsCompact F) (hdisj : Disjoint F (sphere (0 : ℂ) 1)) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction Fᶜ ψ) :
    ∃ X : Ω → ℝ, @Measurable Ω ℝ
      (MeasurableSpace.comap (localModConstPairings 0 hC Fᶜ) inferInstance) _ X ∧
      X =ᵐ[P] fun ω => hC ω ψ := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_radialAnnularTest_one_outside hF hdisj)
  set c : ℝ := ∫ x, ψ x with hc
  let b (n : ℕ) := radialAnnularTest 1 one_pos (n + N)
  have hb (n : ℕ) : IsTestFunction Fᶜ (b n) := hN (n + N) (by omega)
  let φ (n : ℕ) : ℂ → ℝ := fun x => 1 * ψ x + (-c) * b n x
  have hφ (n : ℕ) : IsTestFunction Fᶜ (φ n) ∧ ∫ x, φ n x = 0 := by
    have hi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
    have hj : Integrable (b n) := (hb n).1.continuous.integrable_of_hasCompactSupport (hb n).2.1
    refine ⟨⟨(contDiff_const.mul hψ.1).add (contDiff_const.mul (hb n).1),
      (hψ.2.1.mul_left).add (hb n).2.1.mul_left, ?_⟩, ?_⟩
    · refine (tsupport_add _ _).trans (union_subset ?_ ?_)
      · exact (tsupport_mul_subset_right).trans hψ.2.2
      · exact (tsupport_mul_subset_right).trans (hb n).2.2
    · change ∫ x, (1 * ψ x + (-c) * b n x) = 0
      rw [integral_add (hi.const_mul 1) ((hj).const_mul (-c)), integral_const_mul,
        integral_const_mul, ← hc, radialAnnularTest_integral]
      ring
  have hp := (hgff.tendstoInMeasure_circleDensity_pairing one_pos one_pos 0).comp
    (tendsto_add_atTop_nat N)
  change TendstoInMeasure P (fun n ω => hC ω (b n)) atTop (fun ω => hcirc ω 1 0) at hp
  obtain ⟨s, hs, hsae⟩ := hp.exists_seq_tendsto_ae
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (φ n) = 1 * hC ω ψ + (-c) * hC ω (b n) := by
    apply ae_all_iff.mpr
    intro n
    exact hgff.ae_pairing_linear_combination (hψ.mono_set (subset_univ _))
      ((hb n).mono_set (subset_univ _)) 1 (-c)
  let X : Ω → ℝ := fun ω => liminf (fun n => hC ω (φ (s n))) atTop
  refine ⟨X, ?_, ?_⟩
  · rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    apply Measurable.liminf
    intro n
    simpa only [fieldPairing, zero_mul, sub_zero] using
      (measurable_fieldPairing_modConst 0 hC Fᶜ (φ (s n)) (hφ (s n)))
  · filter_upwards [hsae, hlin, hgff.ae_circleAverage_one_zero] with ω hω hl hpin
    have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 * hC ω ψ) atTop
      (𝓝 (1 * hC ω ψ))).add (hω.const_mul (-c)))
    have ht' : Tendsto (fun n => hC ω (φ (s n))) atTop (𝓝 (hC ω ψ)) := by
      simpa [hl, hpin] using ht
    exact ht'.liminf_eq

/-- Conditional expectations with respect to a σ-algebra all of whose events agree almost surely
with events of a smaller σ-algebra agree almost surely with the conditional expectations with
respect to the smaller one. -/
theorem condExp_ae_eq_of_le_of_ae_representative {Ω : Type*} {m₀ m₁ m₂ : MeasurableSpace Ω}
    {P : @Measure Ω m₀} [IsFiniteMeasure P] (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ m₀)
    (hrep : ∀ s, MeasurableSet[m₂] s → ∃ t, MeasurableSet[m₁] t ∧ s =ᵐ[P] t)
    {f : Ω → ℝ} (hf : Integrable f P) : P[f | m₂] =ᵐ[P] P[f | m₁] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq h2 hf
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_)
    ((stronglyMeasurable_condExp.mono h12).aestronglyMeasurable)).symm
  obtain ⟨t, ht, hst⟩ := hrep s hs
  rw [setIntegral_congr_set hst, setIntegral_condExp (h12.trans h2) hf ht,
    setIntegral_congr_set hst.symm]

/-- Almost sure positivity of a conditional expectation passes to a smaller σ-algebra. -/
theorem ae_condExp_pos_of_le {Ω : Type*} {m₀ m₁ m₂ : MeasurableSpace Ω}
    {P : @Measure Ω m₀} [IsFiniteMeasure P] (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ m₀) {f : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂P, 0 < P[f | m₂] ω) : ∀ᵐ ω ∂P, 0 < P[f | m₁] ω := by
  set g := P[f | m₂] with hg
  set Y := P[g | m₁] with hY
  have hYm : StronglyMeasurable[m₁] Y := stronglyMeasurable_condExp
  have hA : MeasurableSet[m₁] {ω | Y ω ≤ 0} := measurableSet_le hYm.measurable measurable_const
  have hint : ∫ ω in {ω | Y ω ≤ 0}, g ω ∂P = ∫ ω in {ω | Y ω ≤ 0}, Y ω ∂P :=
    (setIntegral_condExp (h12.trans h2) integrable_condExp hA).symm
  have hle : ∫ ω in {ω | Y ω ≤ 0}, Y ω ∂P ≤ 0 :=
    setIntegral_nonpos (h12.trans h2 _ hA) fun ω hω => hω
  have hnull : P {ω | Y ω ≤ 0} = 0 := by
    by_contra hne
    have hsupp : 0 < ∫ ω in {ω | Y ω ≤ 0}, g ω ∂P := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        ((ae_restrict_of_ae hpos).mono fun ω h => h.le) integrable_condExp.integrableOn]
      have heq : Function.support g ∩ {ω | Y ω ≤ 0} =ᵐ[P] {ω | Y ω ≤ 0} := by
        filter_upwards [hpos] with ω hω
        simp [Function.mem_support, hω.ne']
      rw [measure_congr heq]
      exact pos_iff_ne_zero.2 hne
    linarith
  have hYpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    rw [ae_iff]
    simpa only [not_lt] using hnull
  filter_upwards [hYpos, condExp_condExp_of_le h12 h2 (f := f) (μ := P)] with ω h1 h2'
  rw [← h2']
  exact h1

/-- **Every event of the field outside a compact set avoiding the normalization circle agrees almost
surely with an event of the field there modulo additive constants.** -/
theorem fieldSigmaAlgebra_outside_le_aeRepresentative {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {F : Set ℂ} (hF : IsCompact F)
    (hdisj : Disjoint F (sphere (0 : ℂ) 1)) (α₀ : ℝ) :
    fieldSigmaAlgebra α₀ hC Fᶜ ≤
      aeRepresentativeSigma P (MeasurableSpace.comap (localModConstPairings α₀ hC Fᶜ) inferInstance) := by
  unfold fieldSigmaAlgebra
  refine iSup_le fun ψ => iSup_le fun hψ => ?_
  obtain ⟨X, hXm, hXae⟩ := exists_outside_pairing_of_disjoint_sphere hgff hF hdisj ψ hψ
  have hXm' : @Measurable Ω ℝ (MeasurableSpace.comap (localModConstPairings α₀ hC Fᶜ) inferInstance)
      _ X := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings,
      Section6.fieldSigmaAlgebraModConst_eq α₀ hC _,
      fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact hXm
  rintro s ⟨B, hB, rfl⟩
  have hfae : (fun ω => fieldPairing α₀ (hC ω) ψ) =ᵐ[P]
      fun ω => X ω - α₀ * ∫ x, ψ x * Real.log ‖x‖ := by
    filter_upwards [hXae] with ω hω
    simp only [fieldPairing, hω]
  exact ⟨(fun ω => X ω - α₀ * ∫ x, ψ x * Real.log ‖x‖) ⁻¹' B, (hXm'.sub_const _) hB,
    hfae.preimage B⟩

/-- Lemma 11.18 (`s11-pinch:lem:massdiam`, corrected paper lines 3583-3595). The disks are
`U₀ = B_{ρ_U}(c₀)`, `V₀ = B_{ρ_V}(c₀)`, `O = B_{ρ_O}(c₀)` with `0 < ρ_U < ρ_V < ρ_O`, and
`W₀ = B_r(w)` with `Ō ⊆ W₀`, `0 ∉ W₀` and `W₀ ∩ ∂B₁(0) = ∅`. For all `c, ε > 0` there is a measurable
event `H` inside `{μ_h(U₀) > c, diam_h(V̄₀; O) < ε}` of positive probability whose conditional
probability given the field outside `W₀` (the pairings with tests supported outside `W̄₀`) is almost
surely positive. -/
def MassDiamPositiveStmt : Prop :=
  ∀ (c₀ : ℂ) (ρU ρV ρO : ℝ), 0 < ρU → ρU < ρV → ρV < ρO →
  ∀ (w : ℂ) (r : ℝ), closure (ball c₀ ρO) ⊆ ball w r → (0 : ℂ) ∉ ball w r →
    Disjoint (ball w r) (sphere (0 : ℂ) 1) →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ H : Set Ω, MeasurableSet H ∧
      H ⊆ {ω | ENNReal.ofReal c < μ ω (ball c₀ ρU) ∧
        (⨆ x ∈ closure (ball c₀ ρV), ⨆ y ∈ closure (ball c₀ ρV),
          internalMetric (D ω) (ball c₀ ρO) x y) < ENNReal.ofReal ε} ∧
      0 < P H ∧
      ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) | fieldSigmaAlgebra α₀ hC (closure (ball w r))ᶜ]) ω

/-- **Lemma 11.18 for every geometry of concentric disks**, with no hypothesis. -/
theorem massDiamPositive_holds : MassDiamPositiveStmt.{u} := by
  intro c₀ ρU ρV ρO hρU hUV hVO w r hOW h0W hW1 γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hDm
    c ε hc hε
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨r', hr'r, hOr'⟩ := exists_lt_subset_ball isClosed_closure hOW
  have h0 : (0 : ℂ) ∉ ball w r' := fun h => h0W (ball_subset_ball hr'r.le h)
  have hdisj1 : Disjoint (ball w r') (sphere (0 : ℂ) 1) := hW1.mono_left (ball_subset_ball hr'r.le)
  obtain ⟨H, hHm, hHsub, hHpos, hcond⟩ := massDiamModConst_holds c₀ ρU ρV ρO hρU hUV hVO w r' hOr'
    h0 hdisj1 γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hDm c ε hc hε
  refine ⟨H, hHm, hHsub, hHpos, ?_⟩
  have hcl1 : closure (ball w r') ⊆ ball w r :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball hr'r)
  have hdisjcl : Disjoint (closure (ball w r')) (sphere (0 : ℂ) 1) := hW1.mono_left hcl1
  have hcpt : IsCompact (closure (ball w r')) := isBounded_ball.isCompact_closure
  have hcG₁ : MeasurableSpace.comap (localModConstPairings α₀ hC (closure (ball w r'))ᶜ) inferInstance ≤
      fieldSigmaAlgebra α₀ hC (closure (ball w r'))ᶜ := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact Section6.fieldSigmaAlgebraModConst_le α₀ hC _
  have hG₁m : fieldSigmaAlgebra α₀ hC (closure (ball w r'))ᶜ ≤ ‹MeasurableSpace Ω› :=
    hGFF.fieldSigmaAlgebra_le α₀ _
  have hrep := fieldSigmaAlgebra_outside_le_aeRepresentative hGFF hcpt hdisjcl α₀
  have hint : Integrable (H.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hHm
  have hcondeq := condExp_ae_eq_of_le_of_ae_representative hcG₁ hG₁m (fun s hs => hrep s hs) hint
  have hpos₁ : ∀ᵐ ω ∂P,
      0 < P[H.indicator (1 : Ω → ℝ) | fieldSigmaAlgebra α₀ hC (closure (ball w r'))ᶜ] ω := by
    filter_upwards [hcondeq, hcond] with ω h1 h2
    rw [h1]
    exact h2
  have h01 : fieldSigmaAlgebra α₀ hC (closure (ball w r))ᶜ ≤
      fieldSigmaAlgebra α₀ hC (closure (ball w r'))ᶜ :=
    fieldSigmaAlgebra_mono α₀ hC (compl_subset_compl.2 (closure_mono (ball_subset_ball hr'r.le)))
  exact ae_condExp_pos_of_le h01 hG₁m hpos₁

end HarmonicBalls
