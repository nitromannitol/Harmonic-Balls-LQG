import HarmonicBalls.Proofs.Sec6.AnnulusMassContinuity

/-! # Annular mass envelopes for nearby centres

Concentric inner and outer annuli give measurable bounds on the mass of all
nearby annuli. Their masses converge when the limiting circles are null.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- Annulus mass converges under independent changes of centre and both
boundary radii when the limiting boundary circles are null. -/
theorem tendsto_annulus_mass_of_tendsto_boundaries
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {z : ℂ} {r R : ℝ} {zs : ι → ℂ} {rs Rs : ι → ℝ}
    (hz : Tendsto zs L (𝓝 z)) (hr : Tendsto rs L (𝓝 r))
    (hR : Tendsto Rs L (𝓝 R))
    (hinner : μ (sphere z (r)) = 0)
    (houter : μ (sphere z (R)) = 0) :
    Tendsto (fun n => μ (annulus (zs n) (rs n) (Rs n)))
      L (𝓝 (μ (annulus z (r) (R)))) := by
  classical
  apply tendsto_measure_of_ae_tendsto_indicator L
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    (fun _ => (isOpen_ball.sdiff isClosed_closedBall).measurableSet)
    (B := ball z (|R| + 2)) isOpen_ball.measurableSet
    (measure_ball_ne_top (μ := μ))
  · have hz' : ∀ᶠ n in L, dist (zs n) z < 1 :=
      hz.eventually (ball_mem_nhds z zero_lt_one)
    have hr' : ∀ᶠ n in L, Rs n < R + 1 :=
      hR.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hz', hr'] with n hnz hnr x hx
    have hx' : dist x (zs n) < Rs n := hx.1
    have ht := dist_triangle x (zs n) z
    have ha := le_abs_self R
    change dist x z < |R| + 2
    linarith
  · have hi : ∀ᵐ x ∂μ, x ∉ sphere z (r) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hinner
    have ho : ∀ᵐ x ∂μ, x ∉ sphere z (R) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using houter
    filter_upwards [hi, ho] with x hxi hxo
    have hdi : dist x z ≠ r := hxi
    have hdo : dist x z ≠ R := hxo
    have hd : Tendsto (fun n => dist x (zs n)) L (𝓝 (dist x z)) :=
      tendsto_const_nhds.dist hz
    have h3 : Tendsto (fun n => rs n) L (𝓝 r) := hr
    have h5 : Tendsto (fun n => Rs n) L (𝓝 R) := hR
    rcases lt_or_gt_of_ne hdi with hi | hi <;>
      rcases lt_or_gt_of_ne hdo with ho | ho
    · filter_upwards [hd.eventually_lt h3 hi, hd.eventually_lt h5 ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [hd.eventually_lt h3 hi, h5.eventually_lt hd ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [h3.eventually_lt hd hi, hd.eventually_lt h5 ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [h3.eventually_lt hd hi, h5.eventually_lt hd ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- All annuli with centres within `ε` of `z` lie between two concentric
annuli with boundary radii shifted by `ε`. -/
theorem annulus_nearby_center_sandwich {z w : ℂ} {r R ε : ℝ}
    (hzw : dist w z < ε) :
    annulus z (r + ε) (R - ε) ⊆ annulus w r R ∧
      annulus w r R ⊆ annulus z (r - ε) (R + ε) := by
  constructor
  · intro x hx
    have hx' : dist x z < R - ε ∧ r + ε < dist x z := by
      simpa only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] using hx
    have ht₁ := dist_triangle x z w
    have ht₂ := dist_triangle x w z
    have hs := dist_comm z w
    change dist x w < R ∧ ¬ dist x w ≤ r
    constructor <;> linarith
  · intro x hx
    have hx' : dist x w < R ∧ r < dist x w := by
      simpa only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] using hx
    have ht₁ := dist_triangle x z w
    have ht₂ := dist_triangle x w z
    have hs := dist_comm z w
    change dist x z < R + ε ∧ ¬ dist x z ≤ r - ε
    constructor <;> linarith

/-- For a measurable random locally finite measure whose reference annulus has
positive finite mass and null boundary circles, a deterministic displacement
radius controls all nearby annulus masses with arbitrarily high probability.
The exceptional event is bounded by a measurable concentric-annulus envelope. -/
theorem exists_nearby_annulus_mass_ratio_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (z : ℂ) (r R : ℝ)
    (hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      μ ω (sphere z r) = 0 ∧ μ ω (sphere z R) = 0 ∧
      0 < μ ω (annulus z r R) ∧ μ ω (annulus z r R) ≠ ∞)
    {l u : ℝ≥0∞} (hl : l < 1) (hu : 1 < u)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      P {ω | ∃ w : ℂ, dist w z < ε ∧
        ¬ (l * μ ω (annulus z r R) < μ ω (annulus w r R) ∧
           μ ω (annulus w r R) < u * μ ω (annulus z r R))} ≤ δ := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let A : Set ℂ := annulus z r R
  let B : ℕ → Set Ω := fun n => {ω |
    μ ω (annulus z (r + e n) (R - e n)) ≤ l * μ ω A ∨
      u * μ ω A ≤ μ ω (annulus z (r - e n) (R + e n))}
  have hB : ∀ n, MeasurableSet (B n) := by
    intro n
    dsimp only [B]
    apply MeasurableSet.union
    · exact measurableSet_le
        ((Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet).comp hμ)
        (measurable_const.mul ((Measure.measurable_coe
          (isOpen_ball.sdiff isClosed_closedBall).measurableSet).comp hμ))
    · exact measurableSet_le
        (measurable_const.mul ((Measure.measurable_coe
          (isOpen_ball.sdiff isClosed_closedBall).measurableSet).comp hμ))
        ((Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet).comp hμ)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => P (B n)) atTop (𝓝 0) := by
    have hconv := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := P) (As := B) (A := ∅) atTop MeasurableSet.empty hB
    have hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ B n ↔ ω ∈ (∅ : Set Ω) := by
      filter_upwards [hreg] with ω hω
      let : IsLocallyFiniteMeasure (μ ω) := hω.1
      have hpos := hω.2.2.2.1
      have hfin := hω.2.2.2.2
      have hlo : l * μ ω A < μ ω A := by
        simpa only [one_mul] using ENNReal.mul_lt_mul_left hpos.ne' hfin hl
      have hup : μ ω A < u * μ ω A := by
        simpa only [one_mul] using ENNReal.mul_lt_mul_left hpos.ne' hfin hu
      have hinner := tendsto_annulus_mass_of_tendsto_boundaries (μ ω)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
        (by simpa using tendsto_const_nhds.add he)
        (by simpa using tendsto_const_nhds.sub he) hω.2.1 hω.2.2.1
      have houter := tendsto_annulus_mass_of_tendsto_boundaries (μ ω)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
        (by simpa using tendsto_const_nhds.sub he)
        (by simpa using tendsto_const_nhds.add he) hω.2.1 hω.2.2.1
      filter_upwards [tendsto_const_nhds.eventually_lt hinner hlo,
        houter.eventually_lt tendsto_const_nhds hup] with n hn hm
      simp only [B, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or, not_le]
      exact ⟨hn, hm⟩
    simpa using hconv hae
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨e n, by dsimp [e]; positivity, ?_⟩
  calc
    _ ≤ P (B n) := by
      apply measure_mono
      rintro ω ⟨w, hw, hbad⟩
      have hs := annulus_nearby_center_sandwich (r := r) (R := R) hw
      have hlower := measure_mono (μ := μ ω) hs.1
      have hupper := measure_mono (μ := μ ω) hs.2
      change μ ω (annulus z (r + e n) (R - e n)) ≤ l * μ ω A ∨
        u * μ ω A ≤ μ ω (annulus z (r - e n) (R + e n))
      by_contra hnot
      push Not at hnot
      exact hbad ⟨hnot.1.trans_le hlower, hupper.trans_lt hnot.2⟩
    _ ≤ δ := (hn n le_rfl).le

end HarmonicBalls.Section6
