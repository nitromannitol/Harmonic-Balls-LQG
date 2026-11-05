import HarmonicBalls.Proofs.Sec6.CircleCrossingStability
import HarmonicBalls.Proofs.Sec6.AvoidanceStoppingComparison

/-! # Quantitative events for Brownian circle crossings -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- A path visits both radial sides with a specified separation before exit. -/
def radialCrossingEvent (z : ℂ) (r d : ℝ) (V : Set ℂ) : Set (ContinuousPath ℂ) :=
  {ω | (∃ s : ℝ≥0, (s : ℝ≥0∞) < ContinuousPath.exitTime V ω ∧ dist (ω s) z ≤ r - d) ∧
       (∃ t : ℝ≥0, (t : ℝ≥0∞) < ContinuousPath.exitTime V ω ∧ r + d ≤ dist (ω t) z)}

/-- The separated two-sided crossing event is measurable. -/
theorem measurableSet_radialCrossingEvent (z : ℂ) (r d : ℝ) {V : Set ℂ}
    (hV : IsOpen V) : MeasurableSet (radialCrossingEvent z r d V) := by
  have hin : IsClosed {w : ℂ | dist w z ≤ r - d} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  have hout : IsClosed {w : ℂ | r + d ≤ dist w z} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact (measurableSet_hit_closed_before_exit hV hin).inter
    (measurableSet_hit_closed_before_exit hV hout)

/-- The probability of failing a separated crossing tends to zero as the
separation decreases to zero. -/
theorem tendsto_radialCrossingEvent_compl {z y : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : dist y z = r) {V : Set ℂ} (hV : IsOpen V) (hyV : y ∈ V)
    {d : ℕ → ℝ} (hdanti : Antitone d) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => planarBrownianMotion y (radialCrossingEvent z r (d n) V)ᶜ)
      atTop (𝓝 0) := by
  let A : ℕ → Set (ContinuousPath ℂ) := fun n => (radialCrossingEvent z r (d n) V)ᶜ
  have hmeas (n : ℕ) : MeasurableSet (A n) := (measurableSet_radialCrossingEvent z r (d n) hV).compl
  have hanti : Antitone A := by
    intro n m hnm ω hω hgood
    apply hω
    obtain ⟨⟨s, hsV, hs⟩, ⟨t, htV, ht⟩⟩ := hgood
    exact ⟨⟨s, hsV, by linarith [hdanti hnm]⟩, ⟨t, htV, by linarith [hdanti hnm]⟩⟩
  have hz : planarBrownianMotion y (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 (ae_planarBrownian_visits_both_sides_before_exit hr hy hV hyV))
    intro ω hω hgood
    obtain ⟨⟨s, hsV, hs⟩, ⟨t, htV, ht⟩⟩ := hgood
    have he : 0 < min (r - dist (ω s) z) (dist (ω t) z - r) := lt_min (by linarith) (by linarith)
    obtain ⟨n, hn⟩ := (hd.eventually_lt_const he).exists
    have hbad := mem_iInter.mp hω n
    apply hbad
    exact ⟨⟨s, hsV, by linarith [min_le_left (r - dist (ω s) z) (dist (ω t) z - r)]⟩,
      ⟨t, htV, by linarith [min_le_right (r - dist (ω s) z) (dist (ω t) z - r)]⟩⟩
  have hlim := tendsto_measure_iInter_atTop (μ := planarBrownianMotion y)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hz, A, Function.comp_def] using hlim

/-- At a circle point, separated crossings occur with arbitrarily high
probability for a deterministic positive separation. -/
theorem exists_radialCrossingEvent_compl_lt {z y : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : dist y z = r) {V : Set ℂ} (hV : IsOpen V) (hyV : y ∈ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ planarBrownianMotion y (radialCrossingEvent z r d V)ᶜ < ε := by
  have hlim := tendsto_radialCrossingEvent_compl hr hy hV hyV
    (d := fun n => 1 / (n + 1 : ℝ))
    (by
      intro n m hnm
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1)
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  exact ⟨1 / (n + 1 : ℝ), by positivity, hn⟩

/-- A separated crossing survives any smaller translation and remains before
exit from a domain containing the translated neighborhood. -/
theorem radialCrossingEvent_translated_hit {z v : ℂ} {r d : ℝ} {V U : Set ℂ}
    (hv : ‖v‖ < d) (hVU : (fun w : ℂ => w + v) '' V ⊆ U)
    {ω : ContinuousPath ℂ} (hω : ω ∈ radialCrossingEvent z r d V) :
    ∃ u : ℝ≥0, (u : ℝ≥0∞) < ContinuousPath.exitTime U
      ((⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ)).comp ω) ∧
      dist (ω u + v) z = r := by
  obtain ⟨⟨s, hsV, hs⟩, ⟨t, htV, ht⟩⟩ := hω
  have hvs : |dist (ω s + v) z - dist (ω s) z| ≤ ‖v‖ := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using abs_dist_sub_le (ω s + v) (ω s) z
  have hvt : |dist (ω t + v) z - dist (ω t) z| ≤ ‖v‖ := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using abs_dist_sub_le (ω t + v) (ω t) z
  have hs' : dist (ω s + v) z ≤ r := by have := (abs_le.mp hvs).2; linarith
  have ht' : r ≤ dist (ω t + v) z := by have := (abs_le.mp hvt).1; linarith
  have hc : Continuous (fun u : ℝ≥0 => dist (ω u + v) z) := by fun_prop
  have hr : r ∈ Set.uIcc (dist (ω s + v) z) (dist (ω t + v) z) := by
    rw [uIcc_of_le (hs'.trans ht')]
    exact ⟨hs', ht'⟩
  obtain ⟨u, hu, heq⟩ := intermediate_value_uIcc hc.continuousOn hr
  have humax : u ≤ max s t := by
    rcases mem_uIcc.mp hu with hu | hu
    · exact hu.2.trans (le_max_right _ _)
    · exact hu.2.trans (le_max_left _ _)
  refine ⟨u, ?_, heq⟩
  have hmax : ((max s t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime V ω := by
    rcases le_total s t with h | h
    · simpa only [max_eq_right h] using htV
    · simpa only [max_eq_left h] using hsV
  have htime : ContinuousPath.exitTime V ω = ContinuousPath.exitTime
      ((fun w : ℂ => w + v) '' V)
      ((⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ)).comp ω) := by
    symm
    exact exitTime_comp_injective (⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ))
      (fun _ _ h => add_right_cancel h) V ω
  rw [htime] at hmax
  exact (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr humax) hmax).trans_le
    (ContinuousPath.exitTime_mono hVU _)

/-- The probability of exiting a domain before hitting a circle from a
translated starting point is bounded by failure of a separated crossing. -/
theorem planarBrownian_exit_before_circle_le_crossing_compl
    {y z v : ℂ} {r d : ℝ} {V U : Set ℂ} (hU : IsOpen U)
    (hv : ‖v‖ < d) (hVU : (fun w : ℂ => w + v) '' V ⊆ U) :
    planarBrownianMotion (y + v) {ω | ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime (U \ sphere z r) ω} ≤
      planarBrownianMotion y (radialCrossingEvent z r d V)ᶜ := by
  let f := (Homeomorph.refl ℝ≥0).arrowCongr (Homeomorph.addRight v)
  let E : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime U ω ≤
    ContinuousPath.exitTime (U \ sphere z r) ω}
  have hE : MeasurableSet E := measurableSet_le (ContinuousPath.measurable_exitTime U hU)
    (ContinuousPath.measurable_exitTime _ (hU.sdiff isClosed_sphere))
  have hmap : (planarBrownianMotion y).map f = planarBrownianMotion (y + v) :=
    planarBrownianMotion_map_add_from y v
  rw [← hmap, Measure.map_apply f.measurable hE]
  apply measure_mono
  intro ω hω hgood
  obtain ⟨t, ht, hcircle⟩ := radialCrossingEvent_translated_hit hv hVU hgood
  have hnot : f ω t ∉ U \ sphere z r := by
    intro htmem
    apply htmem.2
    change dist (ω t + v) z = r at hcircle
    apply mem_sphere.mpr
    change dist (ω t + v) z = r
    exact hcircle
  have hle := ContinuousPath.exitTime_le_of_notMem (U \ sphere z r) (f ω) t hnot
  have ht' : (t : ℝ≥0∞) < ContinuousPath.exitTime U (f ω) := ht
  exact (not_lt_of_ge ((hω : ContinuousPath.exitTime U (f ω) ≤
    ContinuousPath.exitTime (U \ sphere z r) (f ω)).trans hle)) ht'

/-- The exit-before-circle probability is uniformly small for starting points
near a fixed point of the circle lying in an open domain. -/
theorem locally_uniform_planarBrownian_exit_before_circle
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    {U : Set ℂ} (hU : IsOpen U) (hyU : y ∈ U)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℂ, dist x y < δ →
      planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
        ContinuousPath.exitTime (U \ sphere z r) ω} < ε := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hyU)
  have hhalf : 0 < R / 2 := by linarith
  obtain ⟨d, hd, hdprob⟩ := exists_radialCrossingEvent_compl_lt hr hy
    isOpen_ball (mem_ball_self hhalf) hε
  refine ⟨min d (R / 2), lt_min hd hhalf, ?_⟩
  intro x hx
  have hvd : ‖x - y‖ < d := by
    have := lt_of_lt_of_le hx (min_le_left d (R / 2))
    simpa only [dist_eq_norm] using this
  have hvR : ‖x - y‖ < R / 2 := by
    have := lt_of_lt_of_le hx (min_le_right d (R / 2))
    simpa only [dist_eq_norm] using this
  have hVU : (fun w : ℂ => w + (x - y)) '' ball y (R / 2) ⊆ U := by
    rintro w ⟨a, ha, rfl⟩
    apply hRU
    apply mem_ball.mpr
    have htri := dist_triangle (a + (x - y)) a y
    have hstep : dist (a + (x - y)) a = ‖x - y‖ := by simp only [dist_eq_norm, add_sub_cancel_left]
    have ha' : dist a y < R / 2 := mem_ball.mp ha
    linarith
  have hb := planarBrownian_exit_before_circle_le_crossing_compl (y := y)
    (z := z) (r := r) hU hvd hVU
  rw [add_sub_cancel] at hb
  exact lt_of_le_of_lt hb hdprob

/-- The exit-before-circle estimate is uniform in a neighborhood of every
compact subset of the circle contained in the domain. -/
theorem uniform_planarBrownian_exit_before_circle_of_compact
    {z : ℂ} {r : ℝ} (hr : 0 < r) {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKsphere : K ⊆ sphere z r) (hKU : K ⊆ U)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℂ, y ∈ K → dist x y < δ →
      planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
        ContinuousPath.exitTime (U \ sphere z r) ω} < ε := by
  classical
  have hlocal (y : K) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℂ, dist x y.val < δ →
      planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
        ContinuousPath.exitTime (U \ sphere z r) ω} < ε := by
    apply locally_uniform_planarBrownian_exit_before_circle hr _ hU (hKU y.property) hε
    exact mem_sphere.mp (hKsphere y.property)
  choose δ hδ hbound using hlocal
  let c : K → Set ℂ := fun y => ball y.val (δ y)
  have hcover : K ⊆ ⋃ y, c y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hδ ⟨y, hy⟩)⟩
  obtain ⟨η, hη, hηcover⟩ := lebesgue_number_lemma_of_metric hK (fun y => isOpen_ball) hcover
  refine ⟨η, hη, ?_⟩
  intro x y hy hxy
  obtain ⟨w, hw⟩ := hηcover y hy
  exact hbound w x (by simpa only [c, mem_ball] using hw (mem_ball.mpr hxy))

/-- Near an interior circle, avoidance is controlled by the uniform bound
on that circle plus an arbitrarily small exit-before-hitting error. -/
theorem uniform_planarBrownian_avoidance_le_near_circle
    {z : ℂ} {r : ℝ} (hr : 0 < r) {U Y : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hsphere : sphere z r ⊆ U)
    (hE : MeasurableSet {ω : ContinuousPath ℂ |
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω})
    (c : ℝ≥0∞) (hbound : ∀ y ∈ sphere z r, planarBrownianMotion y
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω} ≤ c)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℂ, y ∈ sphere z r → dist x y < δ →
      x ∈ U \ sphere z r → planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω} ≤ c + 2 * ε := by
  obtain ⟨δ, hδ, hprob⟩ := uniform_planarBrownian_exit_before_circle_of_compact
    hr hU (isCompact_sphere z r) (subset_rfl) hsphere hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hy hxy hx
  have hcomp := planarBrownian_avoidance_le_of_circle_hitting hU hUb hE hx c hbound
  apply hcomp.trans
  gcongr
  exact (hprob x y hy hxy).le

end HarmonicBalls.Section6
