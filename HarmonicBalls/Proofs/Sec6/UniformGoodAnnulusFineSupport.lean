import HarmonicBalls.Proofs.Sec6.SimultaneousGoodAnnulusThreshold

/-! # Uniform good-annulus thresholds from fine support

The fine-support assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- A common integrated avoidance bound gives a good-annulus threshold
uniformly over a family of radii. The ambient set need only contain the
annuli, while the fixed domain controls the avoidance integrals. -/
theorem exists_uniform_goodAnnulus_threshold_of_fine_support
    (μ ν : Measure ℂ) [IsFiniteMeasure ν] {A U : Set ℂ} (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) (hU : IsOpen U) (hx : ∀ᵐ x ∂ν, x ∈ U)
    (hfull : ∀ E : Set ℂ, MeasurableSet E → μ (A \ E) = 0 →
      ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {z : ℂ} {S : Set ℝ} {b : ℝ} (hb : 0 < b)
    (hcontain : ∀ r ∈ S, annulus z (3 * r) (5 * r) ⊆ A)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hmean : ∀ r ∈ S, ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x, planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂ν) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S, IsGoodAnnulus μ r z a b := by
  classical
  by_contra hnone
  have hex (n : ℕ) : ∃ r ∈ S, ¬ IsGoodAnnulus μ r z ((1 / 2 : ℝ) ^ n) b := by
    by_contra hn
    push Not at hn
    exact hnone ⟨_, by positivity, hn⟩
  choose r hr hbad using hex
  have hw (n : ℕ) : ∃ Y : Set ℂ, MeasurableSet Y ∧
      Y ⊆ annulus z (3 * r n) (5 * r n) ∧
      μ Y ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μ (annulus z (3 * r n) (5 * r n)) ∧
      ∃ u ∈ sphere z (4 * r n), ENNReal.ofReal b < planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r n) (5 * r n)) ω ≤
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
          μ (annulus z (3 * r n) (5 * r n)) := hsmall n
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A := by
        rw [heq]
        gcongr
        exact hcontain (r n) (hr n)
  let d : ℝ≥0∞ := ENNReal.ofReal b / C
  have hd : 0 < d := ENNReal.div_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) hCt
  apply not_uniform_avoidance_of_dyadic_exceptions hU μ ν hA hAfin hx hfull Y hY hsmall' hd
  intro n K hK hKY
  have hbound : ENNReal.ofReal b ≤ C * ∫⁻ x, planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂ν := by
    calc
      ENNReal.ofReal b ≤ planarBrownianMotion (u n)
          {ω | ContinuousPath.exitTime (annulus z (3 * r n) (5 * r n)) ω ≤
            ContinuousPath.exitTime (Y n) ω} := (hprob n).le
      _ ≤ planarBrownianMotion (u n)
          {ω | ContinuousPath.exitTime (annulus z (3 * r n) (5 * r n)) ω ≤
            ContinuousPath.exitTime Kᶜ ω} := by
        exact measure_mono (stay_subset_avoid_before_exit _ (Y n) K
          (disjoint_left.mpr (fun x hxK hxY => (hKY hxK).2 hxY)))
      _ ≤ _ := hmean (r n) (hr n) K hK (u n) (hu n)
  exact (ENNReal.div_le_iff_le_mul (Or.inl hC0) (Or.inl hCt)).2 (by
    simpa only [mul_comm] using hbound)


/-- A fixed interior domain gives one submean constant for a family of
annuli when fixed-size balls around their middle circles lie inside it. -/
theorem uniform_goodAnnulus_avoidance_submean
    {z : ℂ} {S : Set ℝ} {U : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hinner : ∀ r ∈ S, U ⊆ annulus z (3 * r) (5 * r))
    (hball : ∀ r ∈ S, ∀ u ∈ sphere z (4 * r), ball u ρ ⊆ U)
    (hball2 : ∀ r ∈ S, ∀ u ∈ sphere z (4 * r), ball u (2 * ρ) ⊆
      annulus z (3 * r) (5 * r)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ r ∈ S, ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
        planarBrownianMotion u
          {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
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
  intro r hr K hK u hu
  let A := annulus z (3 * r) (5 * r)
  let f : ℂ → ℝ≥0∞ := fun x => planarBrownianMotion x
    {path | ContinuousPath.exitTime A path ≤ ContinuousPath.exitTime Kᶜ path}
  have hf : Measurable f := measurable_avoidance_probability
    (isOpen_ball.sdiff isClosed_closedBall) hK
  have hcircle : ∀ s ∈ Ioo (ρ / 2) ρ,
      f u ≤ ∫⁻ x, f x ∂(normalizedCircleMeasure u s) := by
    intro s hs
    apply planarBrownian_avoidance_le_circle_mean (isOpen_ball.sdiff isClosed_closedBall) hK
      (by linarith [hs.1]) (show s < 2 * ρ by linarith [hs.2])
    exact hball2 r hr u hu
  have hsub := ball_submean_of_circle_submean_radius u hρ hf hcircle
  change D * f u ≤ ∫⁻ x in ball u ρ, f x at hsub
  have hmul : D⁻¹ * (D * f u) ≤ D⁻¹ * ∫⁻ x in ball u ρ, f x := by gcongr
  rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul] at hmul
  calc
    f u ≤ D⁻¹ * ∫⁻ x in ball u ρ, f x := hmul
    _ ≤ D⁻¹ * ∫⁻ x in U, f x := by
      gcongr
      exact hball r hr u hu
    _ ≤ D⁻¹ * ∫⁻ x in U, planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂volume := by
      gcongr with x
      apply measure_mono
      intro path hp
      exact (ContinuousPath.exitTime_mono (hinner r hr) path).trans hp


/-- Fine support gives one positive threshold for all radii in a sufficiently
narrow compact interval. -/
theorem uniform_goodAnnulus_threshold_of_ae_local_fine_support
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (z : ℂ) {lo hi ρ b : ℝ} (hlohi : lo ≤ hi)
    (hρ : 0 < ρ) (hgap2 : 4 * hi + ρ < 5 * lo) (hsize : 2 * ρ ≤ lo / 2)
    (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ Icc lo hi, IsGoodAnnulus μ r z a b := by
  let U := annulus z (3 * hi) (5 * lo)
  let A := ball z (5 * hi + 1)
  let ν : Measure ℂ := volume.restrict U
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hνfin : volume U ≠ ∞ := ne_top_of_le_ne_top
    (measure_ball_lt_top (μ := volume)).ne (measure_mono sdiff_subset)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hνfin
  have hUsub : U ⊆ A := by
    intro x hx
    change dist x z < 5 * hi + 1
    have hx' : dist x z < 5 * lo := hx.1
    linarith
  have hinner : ∀ r ∈ Icc lo hi, U ⊆ annulus z (3 * r) (5 * r) := by
    intro r hr x hx
    change dist x z < 5 * lo ∧ ¬ dist x z ≤ 3 * hi at hx
    change dist x z < 5 * r ∧ ¬ dist x z ≤ 3 * r
    constructor <;> linarith [hr.1, hr.2, hx.1, not_le.mp hx.2]
  have hball : ∀ r ∈ Icc lo hi, ∀ u ∈ sphere z (4 * r), ball u ρ ⊆ U := by
    intro r hr u hu x hx
    have hu' : dist u z = 4 * r := hu
    have hx' : dist x u < ρ := hx
    have hupper := dist_triangle x u z
    have hlower := dist_triangle u x z
    have hsymm : dist u x = dist x u := dist_comm _ _
    change dist x z < 5 * lo ∧ ¬ dist x z ≤ 3 * hi
    constructor <;> linarith [hr.1, hr.2, hgap2]
  have hball2 : ∀ r ∈ Icc lo hi, ∀ u ∈ sphere z (4 * r),
      ball u (2 * ρ) ⊆ annulus z (3 * r) (5 * r) := by
    intro r hr u hu
    apply (ball_subset_ball (by linarith [hr.1] : 2 * ρ ≤ r / 2)).trans
    exact middleCircle_half_disc_subset_annulus (by linarith [hr.1, hρ, hsize]) hu
  obtain ⟨C, hC0, hCt, hmean⟩ :=
    uniform_goodAnnulus_avoidance_submean hρ hinner hball hball2
  refine exists_uniform_goodAnnulus_threshold_of_fine_support μ ν (A := A) (U := U)
    (z := z) (S := Icc lo hi) isOpen_ball.measurableSet
    (measure_ball_ne_top (μ := μ)) hU (ae_restrict_mem hU.measurableSet) ?_ hb ?_ hC0 hCt ?_
  · intro E hE hmass
    exact ae_instant_hit_of_ae_local_fine_support μ isOpen_ball hU.measurableSet hUsub
      hloc hE hmass
  · intro r hr x hx
    change dist x z < 5 * hi + 1
    have hx' : dist x z < 5 * r := hx.1
    linarith [hr.2]
  · intro r hr K hK u hu
    exact hmean r hr K hK u hu


/-- Fine support gives a single threshold for every radius in the compact
phase interval `[1/2,1]`. -/
theorem uniform_goodAnnulus_threshold_on_dyadic_phases
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (z : ℂ) {b : ℝ} (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, IsGoodAnnulus μ r z a b := by
  classical
  let lo : Fin 8 → ℝ := fun i => 1 / 2 + (i.val : ℝ) / 16
  have hex : ∀ i : Fin 8, ∃ a : ℝ, 0 < a ∧
      ∀ r ∈ Icc (lo i) (lo i + 1 / 16), IsGoodAnnulus μ r z a b := by
    intro i
    have hi : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
    have hnonneg : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    apply uniform_goodAnnulus_threshold_of_ae_local_fine_support μ hloc z
      (lo := lo i) (hi := lo i + 1 / 16) (ρ := 1 / 100)
    · linarith
    · norm_num
    · dsimp [lo]; linarith
    · dsimp [lo]; linarith
    · exact hb
  choose a ha hgood using hex
  let d : ℝ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin 8)).Nonempty) a
  have hd : 0 < d := (Finset.lt_inf'_iff _).2 (fun i _ => ha i)
  refine ⟨d, hd, ?_⟩
  intro r hr
  have hcover : ∃ i : Fin 8, r ∈ Icc (lo i) (lo i + 1 / 16) := by
    by_cases h0 : r ≤ 9 / 16
    · refine ⟨⟨0, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith [hr.1]
    by_cases h1 : r ≤ 10 / 16
    · refine ⟨⟨1, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    by_cases h2 : r ≤ 11 / 16
    · refine ⟨⟨2, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    by_cases h3 : r ≤ 12 / 16
    · refine ⟨⟨3, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    by_cases h4 : r ≤ 13 / 16
    · refine ⟨⟨4, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    by_cases h5 : r ≤ 14 / 16
    · refine ⟨⟨5, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    by_cases h6 : r ≤ 15 / 16
    · refine ⟨⟨6, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith
    · refine ⟨⟨7, by omega⟩, ?_⟩
      dsimp [lo]; constructor <;> linarith [hr.2]
  obtain ⟨i, hi⟩ := hcover
  exact isGoodAnnulus_mono_mass (hgood i r hi) (Finset.inf'_le a (Finset.mem_univ i))


universe u

/-- Almost surely, the whole-plane LQG measure has a single positive
threshold for all radii in the compact dyadic phase interval. -/
theorem ae_uniform_goodAnnulus_threshold_on_dyadic_phases
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (b : ℝ), 0 < b → ∃ a : ℝ, 0 < a ∧
      ∀ r ∈ Icc (1 / 2 : ℝ) 1, IsGoodAnnulus (μ ω) r z a b := by
  let := h.isProbabilityMeasure
  have hloc := ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc)
  filter_upwards [hμ, hloc] with ω hμω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  intro z b hb
  exact uniform_goodAnnulus_threshold_on_dyadic_phases (μ ω) hlocω z hb

/-- A null-measurable simultaneous good-annulus event turns an almost-sure
uniform threshold into a deterministic probability bound for every radius
in the family. -/
theorem exists_uniform_goodAnnulus_threshold_of_measurable_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} {S : Set ℝ} {b : ℝ} {z : ℂ}
    (hmeas : ∀ n : ℕ, NullMeasurableSet
      {ω | ∀ r ∈ S, IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b} P)
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S, IsGoodAnnulus (μ ω) r z a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r ∈ S,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let A : ℕ → Set Ω := fun n =>
    {ω | ¬ ∀ r ∈ S, IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b}
  have hA : ∀ n, NullMeasurableSet (A n) P := fun n => (hmeas n).compl
  have hanti : Antitone A := by
    intro m n hmn ω hbad hgood
    apply hbad
    intro r hr
    exact isGoodAnnulus_mono_mass (hgood r hr)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hmn 1))
  have hi : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hae)
    intro ω hω hex
    obtain ⟨a, ha, hgood⟩ := hex
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha))
    have hsmall : (1 / 2 : ℝ) ^ (n + 1) < a :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt (hn n le_rfl)
    have hbad := mem_iInter.1 hω n
    apply hbad
    intro r hr
    exact isGoodAnnulus_mono_mass (hgood r hr) hsmall.le
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => hA n) hanti ⟨0, measure_ne_top P _⟩
  rw [hi] at hlim
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (sub_pos.2 hp.2)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · intro r hr
    have hsub : {ω | ¬ IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b} ⊆ A n := by
      intro ω hbad hgood
      exact hbad (hgood r hr)
    exact (measure_mono hsub).trans (hn n le_rfl).le

/-- The LQG phase-uniform probability bound follows once the simultaneous
phase events are null measurable. -/
theorem uniform_goodAnnulus_probability_of_measurable_events
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b p : ℝ} (hb : 0 < b) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hmeas : ∀ n : ℕ, NullMeasurableSet {ω | ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      IsGoodAnnulus (μ ω) r 0 ((1 / 2 : ℝ) ^ (n + 1)) b} P) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} ≤ ENNReal.ofReal (1 - p) := by
  let := h.isProbabilityMeasure
  apply exists_uniform_goodAnnulus_threshold_of_measurable_events P hmeas ?_ hp
  filter_upwards [ae_uniform_goodAnnulus_threshold_on_dyadic_phases hgrowth hγ hγ2 h hμ] with ω hω
  exact hω 0 b hb

end HarmonicBalls.Section6
