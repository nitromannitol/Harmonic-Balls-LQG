import HarmonicBalls.Proofs.Sec6.UniformGoodAnnulusFineSupport

/-! # Uniform good-annulus thresholds over nearby centres

The fine-support assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- Fine support and a common integrated avoidance estimate give a single
threshold for an arbitrary family of centres and radii. -/
theorem exists_uniform_goodAnnulus_threshold_family
    (μ ν : Measure ℂ) [IsFiniteMeasure ν] {A U : Set ℂ} (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) (hU : IsOpen U) (hx : ∀ᵐ x ∂ν, x ∈ U)
    (hfull : ∀ E : Set ℂ, MeasurableSet E → μ (A \ E) = 0 →
      ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {ι : Type*} (z : ι → ℂ) (r : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hcontain : ∀ i, annulus (z i) (3 * r i) (5 * r i) ⊆ A)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hmean : ∀ i, ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (z i) (4 * r i),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus (z i) (3 * r i) (5 * r i)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x, planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂ν) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, IsGoodAnnulus μ (r i) (z i) a b := by
  classical
  by_contra hnone
  have hex (n : ℕ) : ∃ i, ¬ IsGoodAnnulus μ (r i) (z i) ((1 / 2 : ℝ) ^ n) b := by
    by_contra hn
    push Not at hn
    exact hnone ⟨_, by positivity, hn⟩
  choose i hbad using hex
  have hw (n : ℕ) : ∃ Y : Set ℂ, MeasurableSet Y ∧
      Y ⊆ annulus (z (i n)) (3 * r (i n)) (5 * r (i n)) ∧
      μ Y ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) *
        μ (annulus (z (i n)) (3 * r (i n)) (5 * r (i n))) ∧
      ∃ u ∈ sphere (z (i n)) (4 * r (i n)), ENNReal.ofReal b < planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus (z (i n)) (3 * r (i n)) (5 * r (i n))) ω ≤
          ContinuousPath.exitTime Y ω} := by
    have h := hbad n
    simp only [IsGoodAnnulus] at h
    push Not at h
    exact h
  choose Y hY hYA hsmall u hu hprob using hw
  have hsmall' (n : ℕ) : μ (Y n) ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A := by
    have heq : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), one_div,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    calc
      μ (Y n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) *
          μ (annulus (z (i n)) (3 * r (i n)) (5 * r (i n))) := hsmall n
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A := by
        rw [heq]
        gcongr
        exact hcontain (i n)
  let d : ℝ≥0∞ := ENNReal.ofReal b / C
  have hd : 0 < d := ENNReal.div_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) hCt
  apply not_uniform_avoidance_of_dyadic_exceptions hU μ ν hA hAfin hx hfull Y hY hsmall' hd
  intro n K hK hKY
  have hbound : ENNReal.ofReal b ≤ C * ∫⁻ x, planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂ν := by
    calc
      ENNReal.ofReal b ≤ planarBrownianMotion (u n)
          {ω | ContinuousPath.exitTime (annulus (z (i n)) (3 * r (i n)) (5 * r (i n))) ω ≤
            ContinuousPath.exitTime (Y n) ω} := (hprob n).le
      _ ≤ planarBrownianMotion (u n)
          {ω | ContinuousPath.exitTime (annulus (z (i n)) (3 * r (i n)) (5 * r (i n))) ω ≤
            ContinuousPath.exitTime Kᶜ ω} := by
        exact measure_mono (stay_subset_avoid_before_exit _ (Y n) K
          (disjoint_left.mpr (fun x hxK hxY => (hKY hxK).2 hxY)))
      _ ≤ _ := hmean (i n) K hK (u n) (hu n)
  exact (ENNReal.div_le_iff_le_mul (Or.inl hC0) (Or.inl hCt)).2 (by
    simpa only [mul_comm] using hbound)

/-- A shared interior domain controls compact avoidance uniformly over an
indexed family of annuli and middle circles. -/
theorem uniform_goodAnnulus_family_avoidance_submean
    {ι : Type*} (z : ι → ℂ) (r : ι → ℝ) {U : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hinner : ∀ i, U ⊆ annulus (z i) (3 * r i) (5 * r i))
    (hball : ∀ i, ∀ u ∈ sphere (z i) (4 * r i), ball u ρ ⊆ U)
    (hball2 : ∀ i, ∀ u ∈ sphere (z i) (4 * r i), ball u (2 * ρ) ⊆
      annulus (z i) (3 * r i) (5 * r i)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ i, ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (z i) (4 * r i),
        planarBrownianMotion u
          {ω | ContinuousPath.exitTime (annulus (z i) (3 * r i) (5 * r i)) ω ≤
            ContinuousPath.exitTime Kᶜ ω} ≤
        C * ∫⁻ x in U, planarBrownianMotion x
          {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂volume := by
  let D : ℝ≥0∞ := ENNReal.ofReal (ρ / 2) * ENNReal.ofReal (2 * Real.pi) *
    ENNReal.ofReal (ρ / 2)
  have hD0 : D ≠ 0 := by dsimp only [D]; positivity
  have hDt : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  refine ⟨D⁻¹, ENNReal.inv_ne_zero.mpr hDt, ENNReal.inv_ne_top.mpr hD0, ?_⟩
  intro i K hK u hu
  let A := annulus (z i) (3 * r i) (5 * r i)
  let f : ℂ → ℝ≥0∞ := fun x => planarBrownianMotion x
    {path | ContinuousPath.exitTime A path ≤ ContinuousPath.exitTime Kᶜ path}
  have hf : Measurable f := measurable_avoidance_probability
    (isOpen_ball.sdiff isClosed_closedBall) hK
  have hcircle : ∀ s ∈ Ioo (ρ / 2) ρ,
      f u ≤ ∫⁻ x, f x ∂(normalizedCircleMeasure u s) := by
    intro s hs
    apply planarBrownian_avoidance_le_circle_mean (isOpen_ball.sdiff isClosed_closedBall) hK
      (by linarith [hs.1]) (show s < 2 * ρ by linarith [hs.2])
    exact hball2 i u hu
  have hsub := ball_submean_of_circle_submean_radius u hρ hf hcircle
  change D * f u ≤ ∫⁻ x in ball u ρ, f x at hsub
  have hmul : D⁻¹ * (D * f u) ≤ D⁻¹ * ∫⁻ x in ball u ρ, f x := by gcongr
  rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul] at hmul
  calc
    f u ≤ D⁻¹ * ∫⁻ x in ball u ρ, f x := hmul
    _ ≤ D⁻¹ * ∫⁻ x in U, f x := by
      gcongr
      exact hball i u hu
    _ ≤ D⁻¹ * ∫⁻ x in U, planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂volume := by
      gcongr with x
      apply measure_mono
      intro path hp
      exact (ContinuousPath.exitTime_mono (hinner i) path).trans hp

/-- For a locally finite measure with local fine support, one positive
threshold works at a fixed radius for all centres in a neighbourhood. -/
theorem uniform_goodAnnulus_threshold_near_center
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (z₀ : ℂ) {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ ball z₀ (r / 32), IsGoodAnnulus μ r z a b := by
  let U := annulus z₀ (3 * r + r / 16) (5 * r - r / 16)
  let A := ball z₀ (5 * r + r / 32 + 1)
  let ν : Measure ℂ := volume.restrict U
  let ι := {z : ℂ // z ∈ ball z₀ (r / 32)}
  let center : ι → ℂ := Subtype.val
  let radius : ι → ℝ := fun _ => r
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hνfin : volume U ≠ ∞ := ne_top_of_le_ne_top
    (measure_ball_lt_top (μ := volume)).ne (measure_mono sdiff_subset)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hνfin
  have hUsub : U ⊆ A := by
    intro x hx
    change dist x z₀ < 5 * r + r / 32 + 1
    have hx' : dist x z₀ < 5 * r - r / 16 := hx.1
    linarith
  have hinner : ∀ i, U ⊆ annulus (center i) (3 * radius i) (5 * radius i) := by
    intro i x hx
    have hi : dist (center i) z₀ < r / 32 := i.property
    have hx' : dist x z₀ < 5 * r - r / 16 ∧ 3 * r + r / 16 < dist x z₀ := by
      simpa only [U, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] using hx
    have ht1 := dist_triangle x z₀ (center i)
    have ht2 := dist_triangle x (center i) z₀
    have hs : dist z₀ (center i) = dist (center i) z₀ := dist_comm _ _
    change dist x (center i) < 5 * r ∧ ¬ dist x (center i) ≤ 3 * r
    constructor <;> linarith
  have hball : ∀ i, ∀ u ∈ sphere (center i) (4 * radius i), ball u (r / 8) ⊆ U := by
    intro i u hu x hx
    have hi : dist (center i) z₀ < r / 32 := i.property
    have hu' : dist u (center i) = 4 * r := hu
    have hx' : dist x u < r / 8 := hx
    have ht1 := dist_triangle x u (center i)
    have ht2 := dist_triangle u x z₀
    have ht3 := dist_triangle x (center i) z₀
    have ht4 := dist_triangle u (center i) z₀
    have ht5 := dist_triangle (center i) u x
    have ht6 := dist_triangle u z₀ (center i)
    have hsz : dist z₀ (center i) = dist (center i) z₀ := dist_comm _ _
    have hsu : dist u x = dist x u := dist_comm _ _
    have hsc : dist (center i) u = dist u (center i) := dist_comm _ _
    change dist x z₀ < 5 * r - r / 16 ∧ ¬ dist x z₀ ≤ 3 * r + r / 16
    constructor <;> linarith
  have hball2 : ∀ i, ∀ u ∈ sphere (center i) (4 * radius i),
      ball u (2 * (r / 8)) ⊆ annulus (center i) (3 * radius i) (5 * radius i) := by
    intro i u hu
    apply (ball_subset_ball (by linarith : 2 * (r / 8) ≤ r / 2)).trans
    exact middleCircle_half_disc_subset_annulus hr hu
  obtain ⟨C, hC0, hCt, hmean⟩ :=
    uniform_goodAnnulus_family_avoidance_submean center radius (by positivity) hinner hball hball2
  obtain ⟨a, ha, hgood⟩ := exists_uniform_goodAnnulus_threshold_family μ ν
    (A := A) (U := U) isOpen_ball.measurableSet (measure_ball_ne_top (μ := μ)) hU
    (ae_restrict_mem hU.measurableSet) (by
      intro E hE hmass
      exact ae_instant_hit_of_ae_local_fine_support μ isOpen_ball hU.measurableSet hUsub
        hloc hE hmass) center radius hb (by
      intro i x hx
      have hi : dist (center i) z₀ < r / 32 := i.property
      have hx' : dist x (center i) < 5 * r := hx.1
      have ht := dist_triangle x (center i) z₀
      change dist x z₀ < 5 * r + r / 32 + 1
      linarith) hC0 hCt hmean
  exact ⟨a, ha, fun z hz => hgood ⟨z, hz⟩⟩

/-- On any compact set of centres, local fine support gives a common positive
threshold at each prescribed radius. -/
theorem uniform_goodAnnulus_threshold_on_compact
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {K : Set ℂ} (hK : IsCompact K) {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, IsGoodAnnulus μ r z a b := by
  classical
  obtain ⟨T, _, hT, hcover⟩ := hK.finite_cover_balls (show 0 < r / 32 by positivity)
  have hex : ∀ z₀ : ℂ, ∃ a : ℝ, 0 < a ∧
      ∀ z ∈ ball z₀ (r / 32), IsGoodAnnulus μ r z a b :=
    fun z₀ => uniform_goodAnnulus_threshold_near_center μ hloc z₀ hr hb
  choose a ha hgood using hex
  let F : Finset ℂ := insert 0 hT.toFinset
  have hF : F.Nonempty := Finset.insert_nonempty _ _
  let d : ℝ := F.inf' hF a
  have hd : 0 < d := (Finset.lt_inf'_iff _).2 (fun z _ => ha z)
  refine ⟨d, hd, ?_⟩
  intro z hz
  have hz' := hcover hz
  simp only [mem_iUnion] at hz'
  obtain ⟨w, hw, hzw⟩ := hz'
  have hwF : w ∈ F := Finset.mem_insert_of_mem (hT.mem_toFinset.mpr hw)
  exact isGoodAnnulus_mono_mass (hgood w z hzw) (Finset.inf'_le a hwF)

universe u

/-- Almost surely, the whole-plane LQG measure has these compact-centre
thresholds simultaneously for every compact set, radius and positive `b`. -/
theorem ae_compact_center_goodAnnulus_thresholds_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (K : Set ℂ), IsCompact K → ∀ r b : ℝ, 0 < r → 0 < b →
      ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, IsGoodAnnulus (μ ω) r z a b := by
  let := h.isProbabilityMeasure
  have hloc := ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc)
  filter_upwards [hμ, hloc] with ω hμω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  intro K hK r b hr hb
  exact uniform_goodAnnulus_threshold_on_compact (μ ω) hlocω hK hr hb

end HarmonicBalls.Section6
