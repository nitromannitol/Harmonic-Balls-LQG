import HarmonicBalls.Proofs.Sec6.DiscHittingVolumeGrowth

/-! # Fine support from disc volume growth -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter InnerProductSpace ProbabilityTheory MarkovProcess
open scoped ENNReal Topology NNReal

universe u

/-- The Green potential of an LQG measure is continuous on each disc and
its closure, on a common event supplied by volume growth. -/
theorem ae_continuous_lqg_discPotential_extrema_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) {K : Set ℂ} (hK : K ⊆ closure (ball c r)) :
    ∀ᵐ ω ∂P, Continuous (fun z : K => greenPotential (ball c r) (μ ω) z) ∧
      Continuous (fun z : ball c r => greenPotential (ball c r) (μ ω) z) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  obtain ⟨_, _, _, _, R, hR, hsub⟩ := fineSupportDisc_geometry c hr
  obtain ⟨hc, _⟩ := restricted_greenPotential_center_regular hV.1 hr
    (hV.2 R hR) hsub (Set.Subset.rfl : ball c r ⊆ ball c r)
  have heq : (fun x => ∫ y in ball c r, greenFunction (ball c r) x y ∂(μ ω)) =
      greenPotential (ball c r) (μ ω) := by
    funext x
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => greenFunction_of_notMem_right hy x)
  rw [heq] at hc
  have hc' : ContinuousOn (greenPotential (ball c r) (μ ω)) (closure (ball c r)) := by
    simpa only [closure_ball c hr.ne'] using hc
  exact ⟨(hc'.mono hK).domRestrict, (hc'.mono subset_closure).domRestrict⟩

/-- Disc potential ratios at different centres and scales have the same law
under volume growth and the affine and coordinate-change laws. -/
theorem identDistrib_fineSupportDisc_ratio_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio (ball 0 1) (sphere 0 (1 / 4)) (μ ω))
      (fun ω => greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ ω)) P P := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have ha : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs := hAff h (r : ℂ) ha c
  have hsμ := isLQGMeasureOfField_affine hCC h hγ hγ2 hμ ha c
  obtain ⟨_, _, _, hko, _⟩ := fineSupportDisc_geometry 0 (by norm_num : (0 : ℝ) < 1)
  have hd := identDistrib_greenPotentialExtremaRatio
    (identDistrib_affineMeasure h hμ hAff hCC hγ hγ2 ha c) isOpen_ball isBounded_ball
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ 0
      (by norm_num) (hko.trans subset_closure))
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ hs hsμ 0
      (by norm_num) (hko.trans subset_closure))
  have hp : IdentDistrib (fun ω => greenPotentialExtremaRatio (ball 0 1) (sphere 0 (1 / 4)) (μ ω))
      (fun ω => greenPotentialExtremaRatio (ball 0 1) (sphere 0 (1 / 4))
        ((μ ω).map (fun z => (z - c) / (r : ℂ)))) P P :=
    hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd (by
    filter_upwards [] with ω
    simp only [affineMeasure, greenPotentialExtremaRatio]
    apply greenPotential_extrema_ratio_smul_measure
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    · exact ENNReal.ofReal_ne_top))
  apply hp.trans
  apply IdentDistrib.of_ae_eq hp.aemeasurable_snd
  filter_upwards [] with ω
  have hc := greenPotentialExtremaRatio_affine (O := ball (0 : ℂ) 1) isOpen_ball isBounded_ball
    (sphere 0 (1 / 4)) (μ ω) hr c
  rw [fineSupportDisc_affine c hr, fineSupportSphere_affine c hr] at hc
  simpa only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.real_smul, mul_comm] using hc.symm

/-- Disc potential ratios are jointly almost everywhere measurable in
field and centre at each positive scale. -/
theorem aemeasurable_fineSupportDisc_ratio_joint_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
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
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ
  have hc : ∀ᵐ p ∂(P.prod volume),
      Continuous (fun z : K => greenPotential O (m p) z) ∧
      Continuous (fun z : O => greenPotential O (m p) z) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hV] with p hvol
    let : IsLocallyFiniteMeasure (μ p.1) := hvol.1
    obtain ⟨_, _, _, _, R, hR, hsub⟩ := fineSupportDisc_geometry p.2 hr
    obtain ⟨hc, _⟩ := restricted_greenPotential_center_regular hvol.1 hr
      (hvol.2 R hR) hsub (Set.Subset.rfl : ball p.2 r ⊆ ball p.2 r)
    have hcont' : ContinuousOn (greenPotential (ball p.2 r) (μ p.1))
        (closure (ball p.2 r)) := by
      have heq : (fun x => ∫ y in ball p.2 r, greenFunction (ball p.2 r) x y ∂(μ p.1)) =
          greenPotential (ball p.2 r) (μ p.1) := by
        funext x
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => greenFunction_of_notMem_right hy x)
      rw [heq] at hc
      simpa only [closure_ball p.2 hr.ne'] using hc
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


/-- Disc potential ratios recur above a positive threshold at almost every
centre, under volume growth and the affine laws. -/
theorem ae_ae_fineSupportDisc_ratio_recurs_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (ball c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ ω) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply ae_ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P volume
    (fun n p => greenPotentialExtremaRatio (ball p.2 (fineSupportScale n))
      (sphere p.2 (fineSupportScale n / 4)) (μ p.1))
  · intro n
    exact aemeasurable_fineSupportDisc_ratio_joint_of_volumeGrowth hgrowth hγ hγ2 h hμ
      (by unfold fineSupportScale; positivity)
  · filter_upwards [] with c
    filter_upwards [ae_fineSupportDisc_ratio_pos_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ] with ω hp
    exact hp c _ (by unfold fineSupportScale; positivity)
  · filter_upwards [] with c n a
    have hn := identDistrib_fineSupportDisc_ratio_of_volumeGrowth hgrowth hγ hγ2 h hμ hAff hCC c
      (by unfold fineSupportScale; positivity : 0 < fineSupportScale n)
    have h0 := identDistrib_fineSupportDisc_ratio_of_volumeGrowth hgrowth hγ hγ2 h hμ hAff hCC c
      (by unfold fineSupportScale; positivity : 0 < fineSupportScale 0)
    exact (hn.symm.trans h0).measure_mem_eq measurableSet_Iio

/-- LQG has Brownian fine support at almost every centre, assuming volume
growth and the affine and coordinate-change laws. -/
theorem ae_ae_lqg_fine_support_of_disc_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ path ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ path = 0 := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_ae_fineSupportDisc_ratio_recurs_of_volumeGrowth hgrowth hγ hγ2 h hμ hAff hCC,
    ae_fineSupportDisc_centre_hitting_union_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ, hμ] with ω hrec hhit hμω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  filter_upwards [hrec] with x hrecx
  intro ε hε E hE hmass
  apply ae_instant_hit_of_recurrent_lower_bounds
    (measure_ball_ne_top (μ := μ ω) (x := x) (r := ε))
    tendsto_fineSupportScale_zero antitone_fineSupportScale hrecx ?_
    (planarBrownian_compact_union_zeroOne x) hE hmass
  intro K hK hmono hfullK
  filter_upwards [tendsto_fineSupportScale_zero.eventually (eventually_lt_nhds hε)] with n hn
  exact hhit x _ ε (by unfold fineSupportScale; positivity) hn.le K hK hmono hfullK

end HarmonicBalls.Section6
