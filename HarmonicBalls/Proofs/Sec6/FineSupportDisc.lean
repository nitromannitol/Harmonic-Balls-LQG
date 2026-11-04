import HarmonicBalls.Proofs.Sec6.GeneralDomainStopped
import HarmonicBalls.Proofs.Sec6.MeasurePushforwardJoint
import HarmonicBalls.Proofs.Sec6.DiscGreenMass
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.LQGFineSupportReduction
import HarmonicBalls.Proofs.Sec6.BrownianGermBlocks

/-! # Fine-support estimates using discs

The disc Green kernel is symmetric. These geometric and affine-law results
prepare a fine-support argument that uses this symmetry directly.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter InnerProductSpace ProbabilityTheory MarkovProcess
open scoped ENNReal Topology NNReal

open scoped ContDiff in
/-- A disc with positive radius has a smooth nondegenerate defining function. -/
theorem isSmoothBoundedOpen_disc (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSmoothBoundedOpen (ball c r) := by
  let ρ : ℂ → ℝ := fun z => ‖z - c‖ ^ 2 - r ^ 2
  refine ⟨isBounded_ball, ρ, ?_, ?_, ?_⟩
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  · ext z
    simp only [mem_ball, dist_eq_norm, mem_ofPred_eq, ρ]
    have hn := norm_nonneg (z - c)
    constructor <;> intro h <;> nlinarith [sq_nonneg (‖z - c‖ - r)]
  · intro z hz hzero
    have hn : 0 < ‖z - c‖ ^ 2 := by dsimp [ρ] at hz; nlinarith [sq_pos_of_pos hr]
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L (z - c)) hzero
    have hf : HasFDerivAt ρ (2 • (innerSL ℝ (z - c)).comp
        (ContinuousLinearMap.id ℝ ℂ)) z := by
      exact (((hasFDerivAt_id z).sub_const c).norm_sq).sub_const _
    rw [hf.fderiv] at hd
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_self_eq_norm_sq_to_K,
      zero_apply, nsmul_eq_mul] at hd
    exact (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hn))) hd

/-- A quarter-radius circle is a nonempty compact subset of a disc. -/
theorem fineSupportDisc_geometry (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSmoothBoundedOpen (ball c r) ∧ IsCompact (sphere c (r / 4)) ∧
    (sphere c (r / 4)).Nonempty ∧ sphere c (r / 4) ⊆ ball c r ∧
    ∃ R : ℝ, 0 < R ∧ ball c r ⊆ ball 0 R := by
  obtain ⟨_, hk, hkne, hsub, R, hR, hRsub⟩ := fineSupportAnnulus_geometry c hr
  refine ⟨isSmoothBoundedOpen_disc c hr, hk, hkne, ?_, ‖c‖ + r + 1, by positivity, ?_⟩
  · intro z hz
    have hz' := hsub hz
    simpa only [mem_ball, dist_eq_norm] using hz'.2
  · intro z hz
    have hz' : ‖z - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
    have hnorm := norm_add_le (z - c) c
    simp only [sub_add_cancel] at hnorm
    simp only [mem_ball, dist_zero_right]
    linarith

/-- A positive affine map carries the unit disc to the corresponding disc. -/
theorem fineSupportDisc_affine (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => r • z + c) '' ball 0 1 = ball c r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr] at hw ⊢
    nlinarith
  · intro hz
    refine ⟨r⁻¹ • (z - c), ?_, ?_⟩
    · simp only [mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have hz' : ‖z - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
      rw [show r⁻¹ * ‖z - c‖ = ‖z - c‖ / r by rw [div_eq_mul_inv, mul_comm],
        div_lt_one hr]
      exact hz'
    · simp only [smul_inv_smul₀ hr.ne', sub_add_cancel]

universe u

/-- The disc potential ratio is positive simultaneously at all centres and scales. -/
theorem ae_fineSupportDisc_ratio_pos
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      0 < greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ sample) := by
  filter_upwards [ae_lqg_greenPotential_extrema_ratio_pos hholder hfull hgrowth
    hγ hγ2 hα hGFF hμ hnonatom] with sample hs
  intro c r hr
  obtain ⟨ho, hk, hkne, hko, R, hR, hOR⟩ := fineSupportDisc_geometry c hr
  exact hs _ ho R hR hOR _ hk hkne hko

/-- Disc potential ratios have the same law at all centres and positive scales. -/
theorem identDistrib_fineSupportDisc_ratio
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IdentDistrib (fun sample => greenPotentialExtremaRatio (ball 0 1) (sphere 0 (1 / 4)) (μ sample))
      (fun sample => greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ sample)) P P := by
  obtain ⟨ho, _, _, hko, _⟩ := fineSupportDisc_geometry 0 (by norm_num : (0 : ℝ) < 1)
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_positive_affine
    hholder hγ hγ2 h hμ hAff hCC hr c ho (hko.trans subset_closure)
  simpa only [fineSupportDisc_affine c hr, fineSupportSphere_affine c hr] using hd

/-- The disc potential ratio bounds the probability of hitting a full-mass
compact exhaustion before leaving the disc. -/
theorem fineSupportDisc_circle_hitting_union
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {c : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hrε : r ≤ ε) {K : ℕ → Set ℂ}
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (ball c ε \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure (ball c r))) →
      (∀ x ∈ closure (ball c r),
        IntegrableOn (fun y => greenFunction (ball c r) x y * f y) (ball c r) μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧ HolderOnWith C t
        (fun x => ∫ y in ball c r, greenFunction (ball c r) x y * f y ∂μ)
        (closure (ball c r)))
    (hpos : 0 < greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) μ) :
    ∀ x ∈ sphere c (r / 4),
      ENNReal.ofReal (greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) μ) ≤
      planarBrownianMotion x {path | ContinuousPath.exitTime (⋃ n, K n)ᶜ path ≤
        ContinuousPath.exitTime (ball c r) path} := by
  obtain ⟨_, hS, _, hSU, _⟩ := fineSupportDisc_geometry c hr
  apply greenPotentialExtremaRatio_hitting_union_of_stopped_representation_off_obstacle
    isOpen_ball isBounded_ball hS (hSU.trans subset_closure) hK hKmono
    (measure_mono_null (sdiff_subset_sdiff_left (ball_subset_ball hrε)) hfull) hholder hpos
  intro L hL hLU x hx hxL
  exact restricted_greenPotential_stopped_representation_of_symmetry
    isOpen_ball isBounded_ball hL hLU hholder (greenFunction_ball_center_comm c r)
    ⟨hSU hx, hxL⟩ exists_planarBrownian_generator_eq_zero_of_harmonic

/-- Disc potential ratios are jointly almost everywhere measurable in
field and centre at each positive scale. -/
theorem aemeasurable_fineSupportDisc_ratio_joint
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun p : Ω × ℂ =>
      greenPotentialExtremaRatio (ball p.2 r)
        (sphere p.2 (r / 4)) (μ p.1)) (P.prod volume) := by
  let O := ball (0 : ℂ) 1
  let K := sphere (0 : ℂ) (1 / 4)
  obtain ⟨hO, _, _, hKO, _⟩ := fineSupportDisc_geometry 0 (by norm_num : (0 : ℝ) < 1)
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, heq, _⟩ := hO
    change IsOpen (ball 0 1)
    rw [heq]
    exact isOpen_lt hρ.continuous continuous_const
  have hbounded : Bornology.IsBounded O := hO.1
  let m : Ω × ℂ → Measure ℂ := fun p => (μ p.1).map (fun z => r⁻¹ • (z - p.2))
  have hm : AEMeasurable m (P.prod volume) := by
    change AEMeasurable (fun p : Ω × ℂ => (μ p.1).map (fun z => r⁻¹ • (z - p.2))) _
    apply aemeasurable_map_prod_of_locallyFinite (f := fun q : (Ω × ℂ) × ℂ =>
      r⁻¹ • (q.2 - q.1.2)) (h.aemeasurable_lqgMeasure hμ)
    · filter_upwards [hμ] with ω hω
      exact hω.isLocallyFiniteMeasure
    · fun_prop
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hc : ∀ᵐ p ∂(P.prod volume),
      Continuous (fun z : K => greenPotential O (m p) z) ∧
      Continuous (fun z : O => greenPotential O (m p) z) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (hholder γ 0 hγ hγ2 hQ Ω P hC hcirc μ h hμ)] with p hhold
    obtain ⟨ho, _, _, _, _⟩ := fineSupportDisc_geometry p.2 hr
    obtain ⟨_, C, δ, hδ, hcont⟩ := hhold (ball p.2 r) ho
      (fun _ => 1) (memLp_top_const (1 : ℝ))
    have hcont' : ContinuousOn (greenPotential (ball p.2 r) (μ p.1))
        (closure (ball p.2 r)) := by
      apply greenPotential_continuousOn_of_holder (μ p.1)
      refine ⟨C, δ, hδ, ?_⟩
      simpa only [mul_one] using hcont
    have hcontinuous (S : Set ℂ) (hS : S ⊆ O) :
        Continuous (fun z : S => greenPotential O (m p) z) := by
      have heq : (fun z : S => greenPotential O (m p) z) =
          (fun z : S => greenPotential (ball p.2 r) (μ p.1)
            (r • (z : ℂ) + p.2)) := by
        funext z
        have hcov := greenPotential_affine hopen hbounded (μ p.1) hr p.2 (z : ℂ)
        rw [fineSupportDisc_affine p.2 hr] at hcov
        exact hcov.symm
      rw [heq]
      change Continuous (S.domRestrict (fun z : ℂ =>
        greenPotential (ball p.2 r) (μ p.1) (r • z + p.2)))
      apply ContinuousOn.domRestrict
      apply hcont'.comp (by fun_prop)
      intro z hz
      apply subset_closure
      rw [← fineSupportDisc_affine p.2 hr]
      exact ⟨z, hS hz, rfl⟩
    exact ⟨hcontinuous K hKO, hcontinuous O (Subset.rfl)⟩
  have hratio := aemeasurable_potential_extrema_ratio_of_sections (P.prod volume)
    (fun p (z : K) => greenPotential O (m p) z)
    (fun p (z : O) => greenPotential O (m p) z)
    (fun z => (measurable_greenPotential_measure hopen hbounded z).comp_aemeasurable hm)
    (fun z => (measurable_greenPotential_measure hopen hbounded z).comp_aemeasurable hm) hc
  apply hratio.congr
  filter_upwards [] with p
  have hcov := greenPotentialExtremaRatio_affine hopen hbounded K (μ p.1) hr p.2
  rw [fineSupportDisc_affine p.2 hr, fineSupportSphere_affine p.2 hr] at hcov
  exact hcov.symm


/-- Disc potential ratios recur above a positive threshold at almost every centre. -/
theorem ae_ae_fineSupportDisc_ratio_recurs_of_gff_joint
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (ball c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ ω) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply ae_ae_frequently_lqg_potential_ratio_of_equal_lower_tails
    hholder hfull hgrowth volume hγ hγ2 hQ h hμ hnonatom
    (fun n c => ball c (fineSupportScale n))
    (fun n c => sphere c (fineSupportScale n / 4))
  · intro c
    simpa only [fineSupportScale, pow_zero] using
      (fineSupportDisc_geometry c (by norm_num : (0 : ℝ) < 1))
  · intro n
    exact aemeasurable_fineSupportDisc_ratio_joint hholder hγ hγ2 h hμ
      (by unfold fineSupportScale; positivity)
  · filter_upwards [] with c n a
    have hn := identDistrib_fineSupportDisc_ratio hholder hγ hγ2 h hμ hAff hCC c
      (by unfold fineSupportScale; positivity : 0 < fineSupportScale n)
    have h0 := identDistrib_fineSupportDisc_ratio hholder hγ hγ2 h hμ hAff hCC c
      (by unfold fineSupportScale; positivity : 0 < fineSupportScale 0)
    exact (hn.symm.trans h0).measure_mem_eq measurableSet_Iio

/-- A disc ratio gives a hitting bound at its centre. -/
theorem fineSupportDisc_centre_hitting_union
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {c : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hrε : r ≤ ε) {K : ℕ → Set ℂ}
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (ball c ε \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure (ball c r))) →
      (∀ x ∈ closure (ball c r),
        IntegrableOn (fun y => greenFunction (ball c r) x y * f y) (ball c r) μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧ HolderOnWith C t
        (fun x => ∫ y in ball c r, greenFunction (ball c r) x y * f y ∂μ)
        (closure (ball c r)))
    (hpos : 0 < greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) μ) :
    ENNReal.ofReal (greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) μ) ≤
      planarBrownianMotion c {path | ContinuousPath.exitTime (⋃ n, K n)ᶜ path ≤
        ContinuousPath.exitTime (ball c r) path} := by
  apply planarBrownian_hitting_probability_ge_of_circle (by positivity : 0 < r / 4)
    (by linarith : r / 4 < r) K hK
  exact fineSupportDisc_circle_hitting_union hr hrε hK hKmono hfull hholder hpos

/-- The LQG measure has Brownian fine support at almost every centre. The
proof uses disc Green symmetry and the Brownian germ zero-one theorem. -/
theorem ae_ae_lqg_fine_support_of_disc
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ path ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ path = 0 := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_ae_fineSupportDisc_ratio_recurs_of_gff_joint
      hholder hfull hgrowth hγ hγ2 h hμ hnonatom hAff hCC,
    ae_fineSupportDisc_ratio_pos hholder hfull hgrowth hγ hγ2 hQ h hμ hnonatom,
    hholder γ 0 hγ hγ2 hQ Ω P hC hcirc μ h hμ, hμ] with ω hrec hpos hhold hμω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  filter_upwards [hrec] with x hrecx
  intro ε hε E hE hmass
  apply ae_instant_hit_of_recurrent_lower_bounds
    (measure_ball_ne_top (μ := μ ω) (x := x) (r := ε))
    tendsto_fineSupportScale_zero antitone_fineSupportScale hrecx ?_
    (planarBrownian_compact_union_zeroOne x) hE hmass
  intro K hK hmono hfullK
  filter_upwards [tendsto_fineSupportScale_zero.eventually (eventually_lt_nhds hε)] with n hn
  have hr : 0 < fineSupportScale n := by unfold fineSupportScale; positivity
  exact fineSupportDisc_centre_hitting_union hr hn.le hK hmono hfullK
    (hhold _ (isSmoothBoundedOpen_disc x hr)) (hpos x _ hr)

end HarmonicBalls.Section6
